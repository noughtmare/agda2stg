module Main where

import Prelude hiding ( null , empty )

import Agda.Compiler.Backend
import Agda.Compiler.Common

import Agda.Main ( runAgda )

import Agda.Compiler.ToStg

import Agda.Interaction.Options ( OptDescr(..) , ArgDescr(..) )

import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Treeless ( EvaluationStrategy(..) )

import Agda.TypeChecking.Pretty

import Agda.Utils.Either
import Agda.Utils.Functor hiding ((<.>))
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty ( prettyShow )

import Control.DeepSeq ( NFData )

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Function
import qualified Data.List.NonEmpty as NE
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import qualified GHC.Data.Stream as Stream
import GHC.Generics ( Generic )
import GHC.Stg.Syntax (pprStgTopBinding, StgPprOpts (StgPprOpts))
import GHC.Driver.Ppr (showSDocUnsafe)
import GHC.Utils.Logger (initLogger, HasLogger (getLogger))
import GHC (mkModule, mkModuleName, runGhc, ModLocation (..), moduleNameSlashes, moduleName, setUnitDynFlags, getSessionDynFlags, setSessionDynFlags, GhcMonad (getSession), setTargets, DynFlags (homeUnitId_), setProgramDynFlags)
import GHC.Unit (mainUnit, GenericUnitInfo (unitId, unitIncludeDirs), lookupUnitId, rtsUnitId, mainUnitId, initUnits)
import GHC.Driver.DynFlags (defaultDynFlags, initDynFlags, targetProfile)
import qualified GHC.Driver.DynFlags as GHC
import qualified GHC.SysTools
import GHC.Driver.Main (initHscEnv, doCodeGen)
import GHC.Driver.Env (HscEnv(hsc_dflags, hsc_llvm_config, hsc_tmpfs, hsc_logger, hsc_unit_env), hsc_units)
import GHC.Stg.Pipeline (stg2stg)
import GHC.Driver.Config.Stg.Pipeline (initStgPipelineOpts)
import GHC.Types.IPE (emptyInfoTableProvMap)
import GHC.Cmm.Info (cmmToRawCmm)
import GHC.Platform.Profile (Profile(Profile))
import GHC.Driver.CodeOutput (codeOutput)
import GHC.Unit.Finder
import GHC.Driver.Config.Finder (initFinderOpts)

import System.OsPath
import Data.Time.Clock
import GHC.Types.ForeignStubs (ForeignStubs(NoStubs))
import Data.Unique (newUnique)
import GHC.Cmm.UniqueRenamer (initDUniqSupply, runUniqueDSM, runUDSMT)
import GHC.Driver.Session (updatePlatformConstants)
import GHC.Prelude (pprTrace, pprTraceM)
import GHC.Utils.Outputable (ppr)
import GHC.Driver.Pipeline (hscPostBackendPipeline, compileForeign)
import GHC.Driver.Pipeline.Execute (compileStub)
import GHC.SysTools (runAs)
import qualified GHC.Driver.Session as GHC
import GHC.Plugins (withAtomicRename)
import GHC.Linker.Static (linkBinary)

main :: IO ()
main = runAgda [backend]

backend :: Backend
backend = Backend backend'

backend' :: Backend' StgOptions StgOptions () () (IsMain, Definition)
backend' = Backend'
  { backendName           = "agda2stg"
  , options               = StgOptions EagerEvaluation
  , commandLineFlags      = stgFlags
  , isEnabled             = \ _ -> True
  , preCompile            = stgPreCompile
  , postCompile           = \ _ _ _ -> return ()
  , preModule             = \ _ _ _ _ -> return $ Recompile ()
  , compileDef            = \ _ _ isMain def -> return (isMain,def)
  , postModule            = stgPostModule
  , backendVersion        = Nothing
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  , backendInteractTop    = Nothing
  , backendInteractHole   = Nothing
  }

stgFlags :: [OptDescr (Flag StgOptions)]
stgFlags =
  [ Option [] ["lazy-evaluation"] (NoArg $ evaluationFlag LazyEvaluation)
              "Insert delay and force operations to enable lazy evaluation"
  , Option [] ["strict-evaluation"] (NoArg $ evaluationFlag EagerEvaluation)
              "Do not insert delay and force operations (default)"
  ]

stgPreCompile :: StgOptions -> TCM StgOptions
stgPreCompile opts = return opts

-- Run either 'clang' or 'gcc' phases
runGenericAsPhase :: [GHC.Option] -> Bool -> FilePath -> HscEnv -> Maybe ModLocation -> FilePath -> IO FilePath
runGenericAsPhase extra_opts with_cpp output_fn hsc_env location input_fn = do
        let dflags     = hsc_dflags   hsc_env
        let logger     = hsc_logger   hsc_env
        let unit_env   = hsc_unit_env hsc_env

        let cmdline_include_paths = GHC.includePaths dflags
        let pic_c_flags = GHC.picCCOpts dflags

        -- -- we create directories for the object file, because it
        -- -- might be a hierarchical module.
        -- createDirectoryIfMissing True (takeDirectory output_fn)

        -- add package include paths
        -- all_includes <- if not with_cpp
        --   then pure []
        --   else do
        --     pkg_include_dirs <- mayThrowUnitErr (collectIncludeDirs <$> preloadUnitsInfo unit_env)
        --     let global_includes = [ GHC.SysTools.Option ("-I" ++ p)
        --                           | p <- includePathsGlobal cmdline_include_paths ++ pkg_include_dirs]
        --     let local_includes = [ GHC.SysTools.Option ("-iquote" ++ p)
        --                          | p <- includePathsQuote cmdline_include_paths ++ includePathsQuoteImplicit cmdline_include_paths]
        --     pure (local_includes ++ global_includes)
        let all_includes = []
        let runAssembler inputFilename outputFilename
              = withAtomicRename outputFilename $ \temp_outputFilename ->
                    runAs
                       logger dflags
                       (all_includes
                       -- See Note [-fPIC for assembler]
                       ++ map GHC.SysTools.Option pic_c_flags
                       -- See Note [Produce big objects on Windows]
                       -- ++ [ GHC.SysTools.Option "-Wa,-mbig-obj"
                       --    | platformOS (targetPlatform dflags) == OSMinGW32
                       --    , not $ target32Bit (targetPlatform dflags)
                       --    ]

                       -- See Note [-Wa,--no-type-check on wasm32]
                       -- ++ [ GHC.SysTools.Option "-Wa,--no-type-check"
                       --    | platformArch (targetPlatform dflags) == ArchWasm32]

                       ++ [ GHC.SysTools.Option "-x"
                          , if with_cpp
                              then GHC.SysTools.Option "assembler-with-cpp"
                              else GHC.SysTools.Option "assembler"
                          , GHC.SysTools.Option "-c"
                          , GHC.SysTools.FileOption "" inputFilename
                          , GHC.SysTools.Option "-o"
                          , GHC.SysTools.FileOption "" temp_outputFilename
                          ] ++ extra_opts)

        -- debugTraceMsg logger 4 (text "Running the assembler")
        runAssembler input_fn output_fn

        return output_fn

stgPostModule :: StgOptions -> () -> IsMain -> TopLevelModuleName -> [(IsMain, Definition)] -> TCM ()
stgPostModule opts _ isMain modName defs | NE.last (moduleNameParts modName) /= "Primitive" = do

  liftIO $ putStrLn "postModule"

  let defToText _ = "" -- encodeOne printer . fromRich
      fileName  = prettyShow (NE.last $ moduleNameParts modName) ++ ".stg"
      asmFileName = prettyShow (NE.last $ moduleNameParts modName) ++ ".s"
      objectFileName = prettyShow (NE.last $ moduleNameParts modName) ++ ".s"
      this_mod = mkModule mainUnit (mkModuleName (prettyShow modName))

  runToStgM opts this_mod $ do
    -- init

    -- !hsc_env <- liftGhc getSession
    -- case lookupUnitId (hsc_units hsc_env) rtsUnitId of
    --   Nothing -> liftIO $ putStrLn "nothing"
    --   Just info -> liftIO $ putStrLn $ lookupPlatformConstants (fmap ST.unpack (unitIncludeDirs info))

    dflags <- liftGhc getSessionDynFlags
    liftGhc $ setSessionDynFlags dflags
    logger <- liftGhc getLogger
    dflags <- liftGhc getSessionDynFlags

    -- Convert Agda definitions to STG
    -- TODO? stgPreamble
    stg_binds <- catMaybes <$> traverse (\x -> liftIO (putStrLn "another def") >> defToStg x) (map snd defs)
    liftIO $ putStrLn "Done generating STG"

    -- Rest of the GHC pipeline

    let
      ic_inscope = [] -- in-scope variables from GHCi 
      for_bytecode = False

    -- First optimize and transform STG
    (stg_binds_with_fvs, stg_cg_info) <- liftIO $ stg2stg logger ic_inscope (initStgPipelineOpts dflags for_bytecode) this_mod stg_binds

    let (!stg_binds, _stg_deps) = unzip stg_binds_with_fvs
    
    -- Generate C--
    let data_tycons = [] -- TODO

    !hsc_env <- liftGhc getSession
    -- case lookupUnitId (hsc_units hsc_env) rtsUnitId of
    --   Nothing -> liftIO $ putStrLn "nothing"
    --   Just u -> liftIO $ putStrLn $ show (unitIncludeDirs u)
    
    !cmms <- liftIO $ doCodeGen hsc_env this_mod emptyInfoTableProvMap [] mempty stg_binds
    !rawccms0 <- liftIO $ cmmToRawCmm logger (targetProfile dflags) cmms
    
    !mod_basename <- liftIO $ encodeFS $ moduleNameSlashes $ moduleName this_mod
    !agdaSuf <- liftIO $ encodeFS "agda"

    let 
      dependencies = mempty -- TODO
      fopts = initFinderOpts dflags
      mod_location = OsPathModLocation
        { ml_hs_file_ospath = Just (mod_basename <.> agdaSuf)
        , ml_hi_file_ospath = mod_basename <.> finder_hiSuf fopts
        , ml_dyn_hi_file_ospath = mod_basename <.> finder_dynHiSuf fopts
        , ml_obj_file_ospath = mod_basename <.> finder_objectSuf fopts
        , ml_dyn_obj_file_ospath = mod_basename <.> finder_dynObjectSuf fopts
        , ml_hie_file_ospath = mod_basename <.> finder_hieSuf fopts
        }
      foreign_stubs _ = NoStubs
      foreign_files = []
      duniqsupply = initDUniqSupply 'a' 0

    -- Output ASM
    -- TODO: better filename
    (!asm_file, (_stub_h_exists, stub_c_exists), foreign_fps, cmm_cg_infos)
        <- liftIO $ codeOutput logger (hsc_tmpfs hsc_env) (hsc_llvm_config hsc_env) dflags (hsc_units hsc_env) this_mod asmFileName mod_location foreign_stubs foreign_files dependencies duniqsupply rawccms0

    -- stub_o <- liftIO $ mapM (compileStub hsc_env) mStub
    -- foreign_os <-
    -- fos <-
    --   liftIO $ mapM (uncurry (compileForeign hsc_env)) foreign_files
    -- let fos = maybe [] return stub_o ++ foreign_os

    object_file <- liftIO $ runGenericAsPhase [] False objectFileName hsc_env Nothing asm_file

    -- -- don't need this if only compiling one file:
    -- unlinked_time <- liftIO getCurrentTime
    -- final_unlinked <- DotO <$> use (T_MergeForeign pipe_env hsc_env o_fp fos)
    -- let !linkable = LM unlinked_time (ms_mod mod_sum) [final_unlinked]
    -- Add the object linkable to the potential bytecode linkable which was generated in HscBackend.
    -- return (mlinkable { homeMod_object = Just linkable })

    liftIO $ linkBinary logger (hsc_tmpfs hsc_env) dflags (hsc_unit_env hsc_env) [object_file] []

    return () -- $! T.pack $ concatMap showSDocUnsafe $ map (pprStgTopBinding (StgPprOpts False)) stg_binds

-- THE PIPELINE

-- hscGenBackendPipeline :: P m
--   => PipeEnv
--   -> HscEnv
--   -> ModSummary
--   -> HscBackendAction
--   -> m (ModIface, HomeModLinkable)
-- hscGenBackendPipeline pipe_env hsc_env mod_sum result = do
--   let mod_name = moduleName (ms_mod mod_sum)
--       src_flavour = (ms_hsc_src mod_sum)
--   let location = ms_location mod_sum
--   (fos, miface, mlinkable, o_file) <- use (T_HscBackend pipe_env hsc_env mod_name src_flavour location result)
--   final_fp <- hscPostBackendPipeline pipe_env hsc_env (ms_hsc_src mod_sum) (backend (hsc_dflags hsc_env)) (Just location) o_file
--   final_linkable <-
--     case final_fp of
--       -- No object file produced, bytecode or NoBackend
--       Nothing -> return mlinkable
--       Just o_fp -> do
--         unlinked_time <- liftIO (liftIO getCurrentTime)
--         final_unlinked <- DotO <$> use (T_MergeForeign pipe_env hsc_env o_fp fos)
--         let !linkable = LM unlinked_time (ms_mod mod_sum) [final_unlinked]
--         -- Add the object linkable to the potential bytecode linkable which was generated in HscBackend.
--         return (mlinkable { homeMod_object = Just linkable })
--   return (miface, final_linkable)

-- ghc -v3 will show all information that GHC passes to clang
-- make sure that my invocations match the normal compilation of e.g. HelloWorld.hs
-- ghc -keep-tmp-files can show the real main.c
-- need to link against ffi and rts

  -- liftIO $ putStrLn "Writing output..."

  -- liftIO $ T.writeFile fileName $! modText

  -- where
    -- printer :: SExprPrinter Text (SExpr Text)
    -- printer = basicPrint id

stgPostModule _ _ _ _ _ = pure ()

evaluationFlag :: EvaluationStrategy -> Flag StgOptions
evaluationFlag s o = return $ o { stgEvaluation = s }
