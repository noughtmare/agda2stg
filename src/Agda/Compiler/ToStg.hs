{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -Wall #-}
module Agda.Compiler.ToStg where

import Prelude hiding ( null , empty )

import Agda.Compiler.Common
import Agda.Compiler.Erase ( runE , erasable , getFunInfo )
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.EliminateLiteralPatterns
import Agda.Compiler.Treeless.Erase
import Agda.Compiler.Treeless.GuardsToPrims

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Literal
import Agda.Syntax.Treeless

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive.Base

import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.List hiding ((!!))
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Utils.Singleton

import Control.Arrow ( first , second )
import Control.DeepSeq ( NFData )

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Char
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import GHC.Generics ( Generic )
import GHC.Stg.Syntax
import GHC.Types.Var
import GHC.Types.CostCentre (dontCareCCS)
import GHC.Builtin.Types
import GHC.Core.TyCon
import qualified GHC.Types.Literal as GHCLit
import Data.String (fromString)
import Data.Text.Encoding (encodeUtf8)
import GHC.Stg.Lift.Monad (mkStgBinding)
import Control.Monad (replicateM)
import GHC.Types.Id.Info (IdDetails(DataConWrapId, VanillaId), vanillaIdInfo)
import GHC.Core.DataCon (dataConWorkId, DataCon, dataConTyCon, mkDataCon, DataConRep (NoDataConRep))
import GHC.Core
import GHC.Types.Basic
import GHC.Core.TyCon (mkAlgTyCon, mkDataTyConRhs, AlgTyConFlav (VanillaAlgTyCon), PromDataConInfo (NoPromInfo))
import GHC (typeKind, Name, SrcSpan (UnhelpfulSpan))
import GHC.Tc.TyCl.Build (newTyConRepName)
import GHC.Types.Unique.Supply (UniqSupply, mkSplitUniqSupply, takeUniqFromSupply)
import GHC.Types.Id.Make (mkDataConWorkId)
import Data.Traversable (for)
import GHC.Types.Name as GHC (mkInternalName, mkOccName, varName, NameSpace, tcName, dataName)
import qualified GHC.Core.TyCon as GHC
import Agda.Syntax.Common.Pretty (prettyShow)
import GHC.Core.Multiplicity (Scaled(Scaled))
import qualified GHC.Builtin.Names as GHC
import Data.Foldable (for_)
import GHC.Plugins (UnhelpfulSpanReason(UnhelpfulNoLocationInfo), mkLocalId, mkGlobalId)
import GHC.Base (Multiplicity(Many))
import Debug.Trace (traceShow, traceWith, trace)

type StgAtom = Id
instance Show StgAtom where
  show _ = "atom"

stgError :: Text -> StgExpr
stgError msg = StgLit GHCLit.LitNullAddr -- StgOpApp (StgPrimCallOp _panic) _ _someconstantstring

-- stgAxiom :: StgAtom -> StgTopBinding
-- stgAxiom f = StgTopLifted (stgDefine f $ StgRhsClosure noExtFieldSilent dontCareCCS ReEntrant [] (stgError $ "encountered axiom: " <> (error "TODO ppr StgAtom") f) anyTy)

dropArgs :: [Bool] -> [a] -> [a]
dropArgs bs xs = map snd $ filter (not . fst) $ zip bs xs

-- stgPrimOp :: TPrim -> [StgForm] -> ToStgM StgForm
-- stgPrimOp p args = case p of
--   PAdd  -> stgOp 2 "+"   args
--   PSub  -> stgOp 2 "-"   args
--   PMul  -> stgOp 2 "*"   args
--   PQuot -> stgOp 2 "div" args
--   PRem  -> stgOp 2 "mod" args
--   PIf   -> stgOp 3 "if"  args
--   PEqI  -> stgOp 2 "="   args
--   PGeq  -> stgOp 2 ">="  args
--   PLt   -> stgOp 2 "<"   args
--   PSeq  -> stgOp 2 "seq" args
--   _     -> fail $ "not yet supported: primitive " ++ show p

-- stgPreamble :: ToStgM [StgForm]
-- stgPreamble = do
--   -- force <- makeForce
--   -- strat <- getEvaluationStrategy
--   return []
--   --  [ RSList
--   --    [ RSAtom "import"
--   --    , RSList [ RSAtom "only" , RSList [RSAtom "chezstg"] , RSAtom "record-case" ]
--   --    ]
--   --    -- TODO: put this in a separate file and import it here
--   --  , stgDefine "monus" ["x","y"] $
--   --      RSList [RSAtom "max", RSAtom "0", RSList [RSAtom "-", force (RSAtom "x"), force (RSAtom "y")]]
--   --  , stgDefine "seq" ["x","y"] $ case strat of
--   --      EagerEvaluation -> RSAtom "y"
--   --      LazyEvaluation  -> RSList [RSAtom "begin", force (RSAtom "x"), RSAtom "y"]
--   --  ]

deriving instance Generic EvaluationStrategy
deriving instance NFData  EvaluationStrategy

data StgOptions = StgOptions
  { stgEvaluation :: EvaluationStrategy
  }
  deriving (Generic, NFData)

data ToStgEnv = ToStgEnv
  { toStgOptions :: StgOptions
  , toStgVars    :: [StgAtom]
  }

initToStgEnv :: StgOptions -> ToStgEnv
initToStgEnv opts = ToStgEnv opts []

addBinding :: StgAtom -> ToStgEnv -> ToStgEnv
addBinding x env = env { toStgVars = x : toStgVars env }

instance Show DataCon where
  show _ = "datacon"

data ToStgDef = ToStgDef StgAtom Int [Bool]      -- Stg name + arity + erased args
  deriving Show
data ToStgCon = ToStgCon DataCon Int Bool [Bool]  -- Stg name + arity + erased tag + erased args
  deriving Show
data ToStgState = ToStgState
  { toStgDefs      :: Map QName ToStgDef
  , toStgCons      :: Map QName ToStgCon
  , toStgTyCons    :: Map QName TyCon
  , toStgUniqSupply :: UniqSupply
  }

initToStgState :: IO ToStgState
initToStgState = do
  us <- mkSplitUniqSupply 'a'
  pure $ ToStgState
    { toStgDefs      = Map.empty
    , toStgCons      = Map.empty
    , toStgTyCons     = Map.empty
    , toStgUniqSupply = us
    }

type ToStgM a = StateT ToStgState (ReaderT ToStgEnv TCM) a

runToStgM :: StgOptions -> ToStgM a -> TCM a
runToStgM opts x = do
  let e = initToStgEnv opts
  s <- liftIO initToStgState
  runReaderT (evalStateT x s) e

freshStgName :: NameSpace -> String -> ToStgM GHC.Name
freshStgName ns n = do
  s <- get
  let (u,us') = takeUniqFromSupply (toStgUniqSupply s) 
  put s { toStgUniqSupply = us' }
  pure $ mkInternalName u (mkOccName ns n) (UnhelpfulSpan UnhelpfulNoLocationInfo)

liftedAny = anyTypeOfKind liftedTypeKind

freshStgAtom :: ToStgM StgAtom
freshStgAtom = do
  name <- freshStgName GHC.varName "x"
  pure (mkLocalId name manyDataConTy liftedAny)

getEvaluationStrategy :: ToStgM EvaluationStrategy
getEvaluationStrategy = reader $ stgEvaluation . toStgOptions

getVar :: Int -> ToStgM StgAtom
getVar i | traceShow ("getVar", i) False = undefined
getVar i = reader $ (!! i) . toStgVars

withFreshVar :: (StgAtom -> ToStgM a) -> ToStgM a
withFreshVar f = do
  strat <- getEvaluationStrategy
  withFreshVar' strat f

withFreshVar' :: EvaluationStrategy -> (StgAtom -> ToStgM a) -> ToStgM a
withFreshVar' strat f = do
  x <- freshStgAtom
  local (addBinding x) $ f x

withFreshVars :: Int -> ([StgAtom] -> ToStgM a) -> ToStgM a
withFreshVars i f = do
  strat <- getEvaluationStrategy
  withFreshVars' strat i f

withFreshVars' :: EvaluationStrategy -> Int -> ([StgAtom] -> ToStgM a) -> ToStgM a
withFreshVars' strat i f
  | i <= 0    = f []
  | otherwise = withFreshVar' strat $ \x -> withFreshVars' strat (i-1) (f . (x:))

lookupStgDef :: QName -> ToStgM ToStgDef
lookupStgDef n = do
  defs <- gets toStgDefs
  case Map.lookup n defs of
    Nothing -> do
      fail $ "unbound name " <> show (P.pretty n) <> " ||| " <> show defs
    Just a  -> return a

lookupStgCon :: QName -> ToStgM ToStgCon
lookupStgCon n = do
  cons <- gets toStgCons
  case Map.lookup n cons of
    Nothing -> fail $ "unbound name " <> show (P.pretty n) <> " ||| " <> prettyShow (Map.keys cons)
    Just a  -> return a

lookupStgTyCon :: QName -> ToStgM TyCon
lookupStgTyCon n = do
  cons <- gets toStgTyCons
  case Map.lookup n cons of
    Nothing -> fail $ "unbound tycon " <> show (P.pretty n) <> " ||| " <> prettyShow (Map.keys cons)
    Just a  -> return a

setStgDef :: QName -> ToStgDef -> ToStgM ()
setStgDef n def = do
  modify $ \s -> s { toStgDefs = Map.insert n def (toStgDefs s) }

setStgCon :: QName -> ToStgCon -> ToStgM ()
setStgCon n con = do
  modify $ \s -> s { toStgCons = Map.insert n con (toStgCons s) }

setStgTyCon :: QName -> TyCon -> ToStgM ()
setStgTyCon n tycon = do
  modify $ \s -> s { toStgTyCons = Map.insert n tycon (toStgTyCons s)}

-- Creates a valid Stg name from a (qualified) Agda name.
-- Precondition: the given name is not already in toStgDefs.
makeStgName :: QName -> ToStgM StgAtom
makeStgName n = do
  name <- freshStgName GHC.varName (prettyShow (qnameName n)) 
  pure $ mkGlobalId VanillaId name liftedAny vanillaIdInfo

fourBitsToChar :: Int -> Char
fourBitsToChar i
  | i < 10 = chr (ord '0' + i)
  | otherwise = chr (ord 'A' + i - 10)
{-# INLINE fourBitsToChar #-}

class ToStg a b | a -> b where
  toStg :: a -> ToStgM b

-- We first convert all definitions to treeless and calculate their
-- arity and erasure info, before doing the actual translation to Stg.
defToStg :: Definition -> ToStgM (Maybe StgTopBinding)
defToStg def
  | defNoCompilation def ||
    not (usableModality $ getModality def) = return Nothing
  | otherwise = do
    let f = defName def
    liftIO $ putStrLn $ "Compiling definition: " <> prettyShow f
    reportSDoc "toStg" 5 $ "Compiling definition:" <> prettyTCM f
    case theDef def of
      Axiom{} -> do
        -- f' <- newStgDef f 0 []
        -- TODO
        return Nothing
      GeneralizableVar{} -> return Nothing
      d@Function{} | d ^. funInline -> return Nothing
      Function{} -> do
        liftIO $ putStrLn "Compiling function"
        strat <- getEvaluationStrategy
        maybeCompiled <- liftTCM $ toTreeless strat f
        case maybeCompiled of
          Just body -> do
            er <- erasureInfo f
            xs <- traverse (\bs -> topLevelStg bs f body) er
            -- liftIO $ putStrLn "HERE"
            pure xs
            -- case er of
            --   Nothing -> return Nothing
            --   Just bs -> do
            --     reportSDoc "toStg" 15 $ "Erasure info: " <> text (show bs)
            --     let (n, body') = lambdaView body
            --     unless (length bs >= n) __IMPOSSIBLE__
            --     f' <- newStgDef f n (take n bs)
            --     return $ Just (n, bs, f', body')
          Nothing -> return Nothing
      Primitive{} -> do
        -- f' <- newStgDef f 0 []
        return Nothing -- TODO!
      PrimitiveSort{} -> return Nothing
      Datatype{ dataCons = cs } -> do
        liftIO $ putStrLn "Datatype"
        tatom <- freshStgAtom -- GHC.tcName (prettyShow (qnameName (defName def)))
        let tname = GHC.Types.Var.varName tatom
        rname <- freshStgName GHC.varName ("$tc" ++ prettyShow (qnameName (defName def)))
        dataCons' <- for (zip [0..] cs) $ \(tag, c) -> do
          cdef <- getConstInfo c
          dname <- freshStgName GHC.dataName (prettyShow (qnameName (defName cdef)))
          case theDef cdef of
            Constructor{ conSrcCon = chead, conArity = arity } -> do
              let dc tyCon = mkDataCon dname False rname [] [] [] [] mempty [] [] [] (replicate arity (Scaled oneDataConTy liftedAny)) (GHC.mkTyConTy tyCon) NoPromInfo tyCon tag [] (mkDataConWorkId dname (dc tyCon)) NoDataConRep
              pure (\tc -> ToStgCon (dc tc) arity False (replicate arity False))
            _ -> __IMPOSSIBLE__
        let tyCon = mkAlgTyCon tname [] liftedTypeKind [] Nothing [] (mkDataTyConRhs (map ((\(ToStgCon x _ _ _) -> x) . ($ tyCon)) dataCons')) (VanillaAlgTyCon rname) True
        setStgTyCon f tyCon
        for_ (zip cs dataCons') $ \(c, dcf) -> do
          s <- get
          put s { toStgCons = Map.insert c (dcf tyCon) (toStgCons s) }
        -- let eraseTag = length cs == 1
        -- forM_ cs $ \c -> do
        --   cdef <- theDef <$> getConstInfo c
        --   case cdef of
        --     Constructor{ conSrcCon = chead, conArity = nargs } ->
        --       processCon chead nargs eraseTag
        --     _ -> __IMPOSSIBLE__
        return Nothing
      Record{ recConHead = chead, recFields = fs } -> do
        -- TODO: processCon chead (length fs) True
        return Nothing
      Constructor{} -> return Nothing
      AbstractDefn{} -> __IMPOSSIBLE__
      DataOrRecSig{} -> __IMPOSSIBLE__

-- TODO: use bs
topLevelStg :: [Bool] -> QName -> TTerm -> ToStgM StgTopBinding
topLevelStg _ f x | trace ("topLevelStg: " ++ prettyShow f ++ " ||| " ++ prettyShow x) False = undefined
topLevelStg _bs f body = do
  stgF <- makeStgName f
  setStgDef f (ToStgDef stgF (length _bs) _bs)
  (StgTopLifted . StgNonRec stgF) <$> rhsStg (convertGuards body)

rhsStg :: TTerm -> ToStgM StgRhs
rhsStg x | trace ("rhsStg: " ++ prettyShow x) False = undefined
rhsStg body = do
  let (n, body') = lambdaView body
  -- unless (length bs >= n) __IMPOSSIBLE__
  withFreshVars n $ \xs -> do
    body'' <- uncurry appStg (tAppView body')
    let !uf = if n == 0 then Updatable else ReEntrant
    pure (StgRhsClosure noExtFieldSilent dontCareCCS uf xs body'' liftedAny)

appStg :: TTerm -> [TTerm] -> ToStgM StgExpr
appStg x xs | trace ("appStg: " ++ prettyShow x ++ " ||| " ++ prettyShow xs) False = undefined
appStg (TCoerce w) args = appStg w args 
appStg (TApp w args1) args2 = appStg w (args1 ++ args2) 
appStg f args = bindsStg args $ \args' -> 
  case f of
    TVar i -> do
      !x <- getVar i
      pure (StgApp x [])
    TLam _ | (n, body) <- lambdaView f -> do
      withFreshVars n $ \vs -> do
        unless (null args) __IMPOSSIBLE__
        body' <- appStg body []
        v' <- freshStgAtom
        return $ StgLet noExtFieldSilent (StgNonRec v' (StgRhsClosure noExtFieldSilent dontCareCCS ReEntrant vs body' liftedAny)) (StgApp v' [])
    TLit l -> do
      unless (null args) __IMPOSSIBLE__
      litStg l
    TPrim _p -> error "TODO: primitives"
    TDef def -> do
      ToStgDef name _ _ <- lookupStgDef def
      pure $ StgApp name (map StgVarArg args')
    TCon c -> do
      ToStgCon name _ _ _ <- lookupStgCon c
      pure $ StgApp (dataConWorkId name) (map StgVarArg args')
    TLet rhs body -> do
      bindStg rhs (\x -> local (addBinding x) (appStg body []))
      -- rhs' <- appStg rhs []
      -- withFreshVar $ \v -> do
      --   body' <- appStg body [] -- TODO: apply args'

      --  return $ StgLet noExtFieldSilent (StgNonRec v (StgRhsClosure noExtFieldSilent dontCareCCS Updatable [] rhs' anyTy)) body'
    TCase scrut info fallback xs -> do
      !x' <- getVar scrut
      unused <- freshStgAtom -- TODO: can we do better?
      at <- caseToAltType (caseType info)
      y <- traverse altStg xs
      fallback' <- appStg fallback []
      pure $ StgCase (StgApp x' []) unused at 
        (if fallback == TError TUnreachable then y else GenStgAlt DEFAULT [] fallback' : y)
    TUnit -> do
      unless (null args) __IMPOSSIBLE__
      pure $ StgApp unitDataConId []
    TSort -> do
      unless (null args) __IMPOSSIBLE__
      pure $ StgApp unitDataConId []
    TErased -> pure $ StgApp unitDataConId []
    TError e -> do liftIO (putStrLn "TError"); pure $ stgError $ T.pack $ show e

caseToAltType :: CaseType -> ToStgM AltType
caseToAltType (CTData name) | trace ("caseToAltType: " ++ prettyShow name) False = undefined
caseToAltType (CTData name) = AlgAlt <$> lookupStgTyCon name
caseToAltType _ = error "TODO: support non-algebraic matching"

altStg :: TAlt -> ToStgM StgAlt
altStg (TACon name arity body) | trace ("altStg:" ++ prettyShow name ++ " ||| " ++ show arity ++ " ||| " ++ prettyShow body) False = undefined
altStg (TACon name arity body) = do 
  ToStgCon con _ _ _ <- lookupStgCon name
  withFreshVars arity $ \vars ->
    GenStgAlt (DataAlt con) vars <$> appStg body []
altStg _ = __IMPOSSIBLE__ -- we have already converted guards and eliminated literal patterns

-- TODO OPT: collect let bindings, avoid nested lets
bindStg :: TTerm -> (StgAtom -> ToStgM StgExpr) -> ToStgM StgExpr
bindStg x _ | trace ("bindStg: " ++ prettyShow x) False = undefined
bindStg (TDef x) k = do
  ToStgDef x' _ _ <- lookupStgDef x
  k x'
bindStg (TCon x) k = do
  ToStgCon x' _ _ _ <- lookupStgCon x
  k (dataConWorkId x')
bindStg TErased k = k unitDataConId
bindStg (TSort) k = k unitDataConId
bindStg (TUnit) k = k unitDataConId
bindStg (TVar x) k = k =<< getVar x
bindStg x k = do
  v <- freshStgAtom
  rhs <- rhsStg x
  k' <- k v
  return (StgLet noExtFieldSilent (StgNonRec v rhs) k')

bindsStg :: [TTerm] -> ([StgAtom] -> ToStgM StgExpr) -> ToStgM StgExpr
bindsStg [] k = k []
bindsStg (v:vs) k = bindStg v (\v' -> bindsStg vs (\vs' -> k (v' : vs')))

litStg :: Literal -> ToStgM StgExpr
litStg x | trace ("litStg: " ++ prettyShow x) False = undefined
litStg lit = case lit of
    LitNat    x -> return $ StgLit (GHCLit.LitNumber GHCLit.LitNumBigNat x)
    LitWord64 x -> return $ StgLit (GHCLit.LitNumber GHCLit.LitNumWord64 (fromIntegral x))
    LitFloat  x -> return $ StgLit (GHCLit.LitFloat (toRational x))
    LitString x -> return $ StgLit (GHCLit.LitString (encodeUtf8 x))
    LitChar   x -> return $ StgLit (GHCLit.LitChar x)
    LitQName  _ -> return __IMPOSSIBLE__
    LitMeta _ _ -> return __IMPOSSIBLE__

lambdaView :: TTerm -> (Int, TTerm)
lambdaView v = case v of
  TLam    w -> first (1+) $ lambdaView w
  TCoerce w -> lambdaView w
  _         -> (0, v)

-- `Just bs` means that the arguments for which the corresponding
-- position in `bs` is True can be erased
-- `Nothing` means that the entire function can be erased.
erasureInfo :: QName -> ToStgM (Maybe [Bool])
erasureInfo f = liftTCM $ runE $ do
  (bs, b) <- getFunInfo f
  if erasable b
    then return Nothing
    else return (Just $ map erasable bs)