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
import Agda.Utils.Functor
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty ( prettyShow )

import Control.DeepSeq ( NFData )

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Function
import qualified Data.List.NonEmpty as NE
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import GHC.Generics ( Generic )
import GHC.Stg.Syntax (pprStgTopBinding, StgPprOpts (StgPprOpts))
import GHC.Driver.Ppr (showSDocUnsafe)
import GHC.Utils.Logger (initLogger)
import GHC (mkModule, mkModuleName, runGhc)
import GHC.Unit (mainUnit)
import GHC.Driver.DynFlags (defaultDynFlags, initDynFlags, targetProfile)
import GHC.Driver.Main (initHscEnv, doCodeGen)
import GHC.Driver.Env (HscEnv(hsc_dflags, hsc_llvm_config, hsc_tmpfs), hsc_units)
import GHC.Stg.Pipeline (stg2stg)
import GHC.Driver.Config.Stg.Pipeline (initStgPipelineOpts)
import GHC.Types.IPE (emptyInfoTableProvMap)
import GHC.Cmm.Info (cmmToRawCmm)
import GHC.Platform.Profile (Profile(Profile))
import GHC.Driver.CodeOutput (codeOutput)

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

stgPostModule :: StgOptions -> () -> IsMain -> TopLevelModuleName -> [(IsMain, Definition)] -> TCM ()
stgPostModule opts _ isMain modName defs = do
  liftIO $ putStrLn "postModule"

  let defToText _ = "" -- encodeOne printer . fromRich
      fileName  = prettyShow (NE.last $ moduleNameParts modName) ++ ".stg"

  modText <- runToStgM opts $ do
    -- ps  <- stgPreamble
    stg_binds <- catMaybes <$> traverse (\x -> liftIO (putStrLn "another def") >> defToStg x) (map snd defs)
    liftIO $ putStrLn "Done generating STG"

    -- Rest of the GHC pipeline
    liftIO $ do
      logger <- initLogger
      hsc_env <- initHscEnv Nothing

      let
        ic_inscope = [] -- in-scope variables from GHCi 
        dflags = hsc_dflags hsc_env
        for_bytecode = False
        this_mod = mkModule mainUnit (mkModuleName (prettyShow modName))

      -- First optimize and transform STG
      (stg_binds_with_fvs, stg_cg_info) <- stg2stg logger ic_inscope (initStgPipelineOpts dflags for_bytecode) this_mod stg_binds

      let (stg_binds, _stg_deps) = unzip stg_binds_with_fvs
      
      -- -- Generate C--
      -- let data_tycons = [] -- TODO
      -- 
      -- !cmms <- doCodeGen hsc_env this_mod emptyInfoTableProvMap [] mempty stg_binds
      -- rawccms0 <- cmmToRawCmm logger (targetProfile dflags) cmms
      -- 
      -- let dependencies = mempty -- TODO
      -- 
      -- -- Output ASM
      -- (output_filename, (_stub_h_exists, stub_c_exists), foreign_fps, cmm_cg_infos)
      --    <- codeOutput logger (hsc_tmpfs hsc_env) (hsc_llvm_config hsc_env) dflags (hsc_units hsc_env) this_mod fileName _mod_location _foreign_stubs _foreign_files dependencies _uniqsupply rawccms0

      return $! T.pack $ concatMap showSDocUnsafe $ map (pprStgTopBinding (StgPprOpts False)) stg_binds

  -- TODO: rest of the pipeline



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



  liftIO $ putStrLn "Writing output..."

  liftIO $ T.writeFile fileName modText

  where
    -- printer :: SExprPrinter Text (SExpr Text)
    -- printer = basicPrint id

evaluationFlag :: EvaluationStrategy -> Flag StgOptions
evaluationFlag s o = return $ o { stgEvaluation = s }
