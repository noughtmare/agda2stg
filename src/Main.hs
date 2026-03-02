{-# OPTIONS_GHC -Wall #-}
module Main where

import Prelude hiding ( null )


import Agda.Compiler.Backend
    ( TCM,
      Backend'_boot(backendInteractHole, Backend', backendName, options,
                    commandLineFlags, isEnabled, preCompile, postCompile, preModule,
                    compileDef, postModule, backendVersion, scopeCheckingSuffices,
                    mayEraseType, backendInteractTop),
      Backend_boot(Backend),
      Recompile(Recompile),
      Flag,
      IsMain(..),
      TopLevelModuleName,
      EvaluationStrategy(..),
      Backend,
      Backend',
      Definition )

import Agda.Main ( runAgda )

import Agda.Compiler.ToStg
    ( defToStg,
      liftGhc,
      runToStgM,
      StgOptions(..),
      ToStgState(toStgTyCons) )

import Agda.Interaction.Options ( OptDescr(..) , ArgDescr(..) )

import Agda.Syntax.TopLevelModuleName
    ( TopLevelModuleName'(moduleNameParts) )


import Agda.Syntax.Common.Pretty ( prettyShow )


import Control.Monad.Reader ( MonadIO(liftIO) )
import Control.Monad.State ( gets )

import qualified Data.List.NonEmpty as NE
import qualified Data.Map as Map
import Data.Maybe ( catMaybes )

import GHC.Utils.Logger (HasLogger (getLogger))
import GHC (ModLocation (..), moduleNameSlashes, moduleName, getSessionDynFlags, setSessionDynFlags, GhcMonad (getSession))
import GHC.Driver.DynFlags (targetProfile)
import qualified GHC.Driver.DynFlags as GHC
import qualified GHC.SysTools
import GHC.Driver.Main (doCodeGen)
import GHC.Driver.Env (HscEnv(hsc_dflags, hsc_llvm_config, hsc_tmpfs, hsc_logger, hsc_unit_env), hsc_units)
import GHC.Stg.Pipeline (stg2stg)
import GHC.Driver.Config.Stg.Pipeline (initStgPipelineOpts)
import GHC.Types.IPE (emptyInfoTableProvMap)
import GHC.Cmm.Info (cmmToRawCmm)
import GHC.Driver.CodeOutput (codeOutput)
import GHC.Unit.Finder
    ( FinderOpts(finder_hieSuf, finder_hiSuf, finder_dynHiSuf,
                 finder_objectSuf, finder_dynObjectSuf) )
import GHC.Driver.Config.Finder (initFinderOpts)

import System.OsPath ( (<.>), encodeFS )
import GHC.Types.ForeignStubs (ForeignStubs(NoStubs))
import GHC.Cmm.UniqueRenamer (initDUniqSupply)
import qualified GHC.Driver.Session as GHC
import GHC.Plugins (withAtomicRename)
import GHC.Linker.Static (linkBinary)
import GHC.Builtin.Names (rOOT_MAIN)


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
                    GHC.SysTools.runAs
                       logger dflags
                       (all_includes
                       -- See Note [-fPIC for assembler]
                       ++ map GHC.SysTools.Option pic_c_flags
                      -- -- See Note [Produce big objects on Windows]
                       -- ++ [ GHC.SysTools.Option "-Wa,-mbig-obj"
                       --    | platformOS (targetPlatform dflags) == OSMinGW32
                       --    , not $ target32Bit (targetPlatform dflags)
                       --    ]

                       -- -- See Note [-Wa,--no-type-check on wasm32]
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
stgPostModule opts _ NotMain _ _ = pure () -- TODO
stgPostModule opts _ IsMain modName defs = do

  liftIO $ putStrLn "postModule"

  let defToText _ = "" -- encodeOne printer . fromRich
      fileName  = prettyShow (NE.last $ moduleNameParts modName) ++ ".stg"
      asmFileName = prettyShow (NE.last $ moduleNameParts modName) ++ ".s"
      objectFileName = prettyShow (NE.last $ moduleNameParts modName) ++ ".o"
      this_mod = rOOT_MAIN -- mkModule mainUnit mAIN_NAME -- (mkModuleName (prettyShow modName))

  runToStgM opts this_mod $ do
    dflags <- liftGhc getSessionDynFlags
    liftGhc $ setSessionDynFlags dflags
    -- liftGhc $ setSessionDynFlags (GHC.dopt_set dflags { GHC.verbosity = 0 } GHC.Opt_D_dump_cmm_from_stg)
    logger <- liftGhc getLogger
    dflags <- liftGhc getSessionDynFlags

    -- Convert Agda definitions to STG
    stg_binds <- catMaybes <$> traverse (defToStg . snd) defs

    -- First optimize and transform STG
    (stg_binds_with_fvs, _) <- liftIO $ stg2stg logger [] (initStgPipelineOpts dflags False) this_mod stg_binds

    let (!stg_binds, _) = unzip stg_binds_with_fvs

    -- Generate C--
    tyCons <- gets (Map.elems . toStgTyCons)

    !hsc_env <- liftGhc getSession
    !cmms <- liftIO $ doCodeGen hsc_env this_mod emptyInfoTableProvMap tyCons mempty stg_binds
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
    (!asm_file, _, _, _) <- liftIO $ codeOutput logger (hsc_tmpfs hsc_env) (hsc_llvm_config hsc_env) dflags (hsc_units hsc_env) this_mod asmFileName mod_location foreign_stubs foreign_files dependencies duniqsupply rawccms0

    object_file <- liftIO $ runGenericAsPhase [] False objectFileName hsc_env Nothing asm_file

    liftIO $ linkBinary logger (hsc_tmpfs hsc_env) dflags (hsc_unit_env hsc_env) [object_file] []

stgPostModule _ _ _ _ _ = pure ()

evaluationFlag :: EvaluationStrategy -> Flag StgOptions
evaluationFlag s o = return $ o { stgEvaluation = s }
