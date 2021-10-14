{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Cone.Env where

import Cone.Parser.AST
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Effect.Sum
import Control.Lens
import Control.Lens.Plated
import Control.Monad
import qualified Data.Map as M
import qualified Data.List as L
import Data.Maybe
import Data.Map.Merge.Strict
import Debug.Trace
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe

type Eff s e = Fresh :+: State s :+: Error e

type TypeKinds = M.Map String Kind

type TypeAliases = M.Map String TypeAlias

type EffKinds = M.Map String EffKind

type EffIntfs = M.Map String [String]

type FuncTypes = M.Map String Type

type FuncEffs = M.Map String EffectType

type FuncImpls = M.Map String [(Expr, Type)]

type TypeBinds = M.Map String Type

type KindBinds = M.Map String Kind

type EffTypeBinds = M.Map String EffectType

type EffKindBinds = M.Map String EffKind

type DiffAdjs = M.Map String DiffDef

type FuncDefs = M.Map String FuncDef

-- | The environment
data Env = Env
  { _currentModuleName :: String,
    _typeKinds :: TypeKinds,
    _typeAliases :: TypeAliases,
    _funcTypes :: FuncTypes,
    _funcEffs :: FuncEffs,
    _funcImpls :: FuncImpls,
    _effKinds :: EffKinds,
    _effIntfs :: EffIntfs,
    _localState :: FuncTypes,
    _typeBinds :: TypeBinds,
    _kindBinds :: KindBinds,
    _effTypeBinds :: EffTypeBinds,
    _effKindBinds :: EffKindBinds,
    _diffAdjs :: DiffAdjs,
    _funcDefs :: FuncDefs,
    _specializedFuncs :: FuncDefs,
    _specializedFuncTypes :: FuncTypes
  }
  deriving (Show)

makeLenses ''Env

initialEnv =
  Env
    { _currentModuleName = "",
      _typeKinds = M.empty,
      _typeAliases = M.empty,
      _funcTypes = M.empty,
      _funcEffs = M.empty,
      _funcImpls = M.empty,
      _effKinds = M.empty,
      _effIntfs = M.empty,
      _localState = M.empty,
      _typeBinds = M.empty,
      _kindBinds = M.empty,
      _effTypeBinds = M.empty,
      _effKindBinds = M.empty,
      _diffAdjs = M.empty,
      _funcDefs = M.empty,
      _specializedFuncs = M.empty,
      _specializedFuncTypes = M.empty
    }

type EnvEff = Eff Env String

-- | Get value by a lens from env
getEnv :: (Has EnvEff sig m) => Getter Env a -> m a
getEnv l = do
  env <- get @Env
  return $ view l env

-- | Set value by a lens into env
setEnv :: (Has EnvEff sig m) => b -> Setter Env Env a b -> m ()
setEnv v l = do
  env <- get @Env
  put $ set l v env

addFuncImpl :: (Has EnvEff sig m) => String -> Expr -> Type -> m ()
addFuncImpl n e t = do
  impls <- getEnv $ funcImpls . at n
  forMOf _Nothing impls $ \_ -> setEnv (Just []) $ funcImpls . at n
  impls <- fromJust <$> getEnv (funcImpls . at n)
  setEnv (Just $ impls ++ [(e, t)]) $ funcImpls . at n

getFuncImpls :: (Has EnvEff sig m) => String -> m [(Expr, Type)]
getFuncImpls n = getEnv $ funcImpls . at n . non []

-- | Run under a local scope
underScope :: (Has EnvEff sig m) => m a -> m a
underScope f = do
  env <- get @Env
  res <- f
  tbs <- getEnv typeBinds
  kbs <- getEnv kindBinds
  ebs <- getEnv effTypeBinds
  ekbs <- getEnv effKindBinds
  sfs <- getEnv specializedFuncs
  sfts <- getEnv specializedFuncTypes
  let g1 = mapMaybeMissing $ \k v -> Just v
      g2 = mapMaybeMissing $ \k v -> Just v
      f = zipWithMaybeMatched $ \k v1 v2 -> Just v1
  put env {_typeBinds = tbs, _kindBinds = kbs, _effTypeBinds = ebs, _effKindBinds = ekbs, 
           _specializedFuncs=sfs,
           _specializedFuncTypes=sfts,
           _funcTypes = merge g1 g2 f (_funcTypes env) sfts}
  return res

-- | Add effect interface into env
addEffIntfs :: (Has EnvEff sig m) => String -> String -> m ()
addEffIntfs effName intfName = do
  ifs <- getEnv $ effIntfs . at effName
  setEnv
    ( Just $ case ifs of
        Just ifs -> intfName : ifs
        Nothing -> [intfName]
    )
    $ effIntfs . at effName

-- | Generate a free type variable name
freeVarName :: Int -> TVar
freeVarName i = s2n $ "$tvar" ++ show i

-- | Generate a free effect type variable name
freeEffVarName :: Int -> EffVar
freeEffVarName i = s2n $ "$evar" ++ show i

-- | Add all free type variables into bound variable list
closeType :: Type -> Bind [TVar] Type
closeType t =
  let fvars = t ^.. fv
   in bind fvars t

-- | Add all free eff type variables into bound variable list
closeEffType :: EffectType -> Bind [TVar] EffectType
closeEffType t =
  let fvars = t ^.. fv
   in bind fvars t

-- | Bind a type with type variables
bindTypeVar :: [(TVar, Maybe Kind)] -> Type -> Type
bindTypeVar bvs t = BoundType (bind bvs t) (_tloc t)

-- | Bind an effect type with type variables
bindTypeEffVar :: [EffVar] -> Type -> Type
bindTypeEffVar bvs t = BoundEffVarType (bind bvs t) (_tloc t)

-- | Refresh all bound type variables with new names
refreshTypeVar :: (Has EnvEff sig m) => [TVar] -> Expr -> m ([TVar], Expr)
refreshTypeVar vs e = do
  let pos = _eloc e
  nvs <- mapM (\_ -> freeVarName <$> fresh) vs
  return (nvs, substs [(f, TVar t pos) | f <- vs | t <- nvs] e)

-- | Refresh all bound eff type variables witn new names
refreshEffVar :: (Has EnvEff sig m) => [EffVar] -> Expr -> m ([EffVar], Expr)
refreshEffVar vs e = do
  let pos = _eloc e
  nvs <- mapM (\_ -> freeEffVarName <$> fresh) vs
  return (nvs, substs [(f, EffVar t pos) | f <- vs | t <- nvs] e)

-- | Unbind a type by all bound variables with new names
unbindType :: (Has EnvEff sig m) => Type -> m Type
unbindType b@BoundType {..} = do
  let (vs, t) = unsafeUnbind _boundType
      pos = _tloc
  nvs <- mapM (\_ -> freeVarName <$> fresh) vs
  unbindType $ substs [(f ^. _1, TVar t pos) | f <- vs | t <- nvs] t
unbindType b@BoundEffVarType {..} = do
  let (vs, t) = unsafeUnbind _boundEffVarType
      pos = _tloc
  nvs <- mapM (\_ -> freeEffVarName <$> fresh) vs
  unbindType $ substs [(f, EffVar t pos) | f <- vs | t <- nvs] t
unbindType t = return t

-- | Just simply unbind a type
unbindTypeSimple :: Type -> ([(TVar, Maybe Kind)], [EffVar], Type)
unbindTypeSimple b@BoundType {..} =
  let (bvs, t) = unsafeUnbind _boundType
      (bvs', evs, t') = unbindTypeSimple t
   in (bvs ++ bvs', evs, t')
unbindTypeSimple b@BoundEffVarType {..} =
  let (evs, t) = unsafeUnbind _boundEffVarType
      (bvs, evs', t') = unbindTypeSimple t
   in (bvs, evs ++ evs', t')
unbindTypeSimple t = ([], [], t)

bindEDef :: EffectDef -> EffectDef
bindEDef edef =
  let boundVars = L.nub $ edef ^.. effectArgs . traverse
      edef' = over (effectIntfs . traverse) (bindEffIntf boundVars) edef
   in BoundEffectDef (bind (boundVars ^.. traverse . _1) edef') (_effectLoc edef)

bindEffIntf :: [(TVar, Maybe Kind)] -> FuncIntf -> FuncIntf
bindEffIntf bvs intf =
  let boundVars = L.nub $ bvs ++ intf ^. intfBoundVars
      boundEffVars = L.nub $ intf ^. intfBoundEffVars
      loc = intf ^. intfLoc
   in BoundEffFuncIntf (bind boundEffVars $ BoundFuncIntf (bind (boundVars ^.. traverse . _1) intf) loc) loc

bindTDef :: TypeDef -> TypeDef
bindTDef tdef =
  let boundVars = L.nub $ tdef ^.. typeArgs . traverse . _1
   in BoundTypeDef (bind boundVars tdef) (_typeLoc tdef)

bindTAlias :: TypeAlias -> TypeAlias
bindTAlias talias =
  let boundVars = L.nub $ talias ^.. typeAliasArgs . traverse . _1
   in BoundTypeAlias (bind boundVars talias) (_typeAliasLoc talias)

bindFDef :: FuncDef -> FuncDef
bindFDef fdef =
  let boundVars = L.nub $ fdef ^. funcBoundVars
      boundEffVars = L.nub $ fdef ^. funcBoundEffVars
      loc = fdef ^. funcLoc
      expr = transform bindExpr <$> _funcExpr fdef
   in BoundEffFuncDef (bind boundEffVars $ BoundFuncDef (bind (boundVars ^.. traverse . _1) fdef {_funcExpr = expr}) loc) loc

bindExpr :: Expr -> Expr
bindExpr l@ELam {..} =
  let boundVars = L.nub _elamBoundVars
      boundEffVars = L.nub _elamBoundEffVars
   in  EBoundEffTypeVars (bind boundEffVars $ EBoundTypeVars (bind (boundVars ^.. traverse . _1) l) _eloc) _eloc
bindExpr expr = expr

-- | Add type bindings
addTypeBindings :: Module -> Module
addTypeBindings m =
  over (topStmts . traverse . _EDef) bindEDef $
    over (topStmts . traverse . _TDef) bindTDef $
      over (topStmts . traverse . _FDef) bindFDef $
        over (topStmts . traverse . _ImplFDef . implFunDef) bindFDef $
          over (topStmts . traverse . _TAlias) bindTAlias m

-- | Remove type bindings
removeTypeBindings :: Module -> Module
removeTypeBindings m =
  over (topStmts . traverse . _EDef) removeBindingsForEDef $
    over (topStmts . traverse . _TDef) removeBindingsForTDef $
      over (topStmts . traverse . _FDef) removeBindingsForFDef $
        over (topStmts . traverse . _ImplFDef . implFunDef) removeBindingsForFDef $
          over (topStmts . traverse . _TAlias) removeBindingsForTypeAlias m
  where
    removeBindingsForEDef (BoundEffectDef b _) =
      let (_, e) = unsafeUnbind b
       in removeBindingsForEDef e
    removeBindingsForEDef e =
      over (effectIntfs . traverse) removeBindingsForIntf e
    removeBindingsForIntf (BoundFuncIntf b _) =
      let (_, i) = unsafeUnbind b
       in removeBindingsForIntf i
    removeBindingsForIntf (BoundEffFuncIntf b _) =
      let (_, i) = unsafeUnbind b
       in removeBindingsForIntf i
    removeBindingsForIntf intf = intf
    removeBindingsForTDef (BoundTypeDef b _) =
      let (_, t) = unsafeUnbind b
       in removeBindingsForTDef t
    removeBindingsForTDef t = t
    removeBindingsForTypeAlias (BoundTypeAlias b _) =
      let (_, t) = unsafeUnbind b
       in removeBindingsForTypeAlias t
    removeBindingsForTypeAlias t = t
    removeBindingsForFDef (BoundFuncDef b _) =
      let (_, f) = unsafeUnbind b
       in removeBindingsForFDef f
    removeBindingsForFDef (BoundEffFuncDef b _) =
      let (_, f) = unsafeUnbind b
       in removeBindingsForFDef f
    removeBindingsForFDef fdef =
      let expr = removeBindingsForExpr <$> _funcExpr fdef
       in fdef {_funcExpr = expr}
    removeBindingsForExpr (EBoundTypeVars b _) =
      let (_, e) = unsafeUnbind b
       in removeBindingsForExpr e
    removeBindingsForExpr (EBoundEffTypeVars b _) =
      let (_, e) = unsafeUnbind b
       in removeBindingsForExpr e
    removeBindingsForExpr l@ELam {..} =
      l {_elamExpr = fmap removeBindingsForExpr _elamExpr}
    removeBindingsForExpr e@ECase {..} =
      e
        { _ecaseExpr = removeBindingsForExpr _ecaseExpr,
          _ecaseBody = over traverse removeBindingsForCase _ecaseBody
        }
    removeBindingsForExpr w@EWhile {..} =
      w
        { _ewhileCond = removeBindingsForExpr _ewhileCond,
          _ewhileBody = removeBindingsForExpr _ewhileBody
        }
    removeBindingsForExpr a@EApp {..} =
      a
        { _eappFunc = removeBindingsForExpr _eappFunc,
          _eappArgs = over traverse removeBindingsForExpr _eappArgs
        }
    removeBindingsForExpr l@ELet {..} =
      l
        { _eletExpr = removeBindingsForExpr _eletExpr,
          _eletPattern = removeBindingsForPattern _eletPattern,
          _eletBody = removeBindingsForExpr _eletBody
        }
    removeBindingsForExpr h@EHandle {..} =
      h
        { _ehandleScope = removeBindingsForExpr _ehandleScope,
          _ehandleBindings = map removeBindingsForFDef _ehandleBindings
        }
    removeBindingsForExpr s@ESeq {..} =
      s {_eseq = map removeBindingsForExpr _eseq}
    removeBindingsForExpr e@EAnn {..} =
      e {_eannExpr = removeBindingsForExpr _eannExpr}
    removeBindingsForExpr e@EAnnMeta {..} =
      e {_eannMetaExpr = removeBindingsForExpr _eannMetaExpr}
    removeBindingsForExpr expr = expr
    removeBindingsForPattern p@PExpr {..} =
      p {_pExpr = removeBindingsForExpr _pExpr}
    removeBindingsForPattern p = p
    removeBindingsForCase c@Case {..} =
      c
        { _caseExpr = removeBindingsForExpr _caseExpr,
          _casePattern = removeBindingsForPattern _casePattern
        }
    removeBindingsForCase c = c

-- | Add variable bindings
addVarBindings :: Module -> Module
addVarBindings m =
  over (topStmts . traverse . _FDef) bindFDef $
    over (topStmts . traverse . _ImplFDef . implFunDef) bindFDef $
      over (topStmts . traverse . _DDef) bindDiffDef m
  where
    bindFDef fdef =
      let boundVars = map s2n $ L.nub $ fdef ^.. funcArgs . traverse . _1
          loc = fdef ^. funcLoc
          expr = transform bindExpr <$> _funcExpr fdef
       in fdef {_funcExpr = fmap (\e -> EBoundVars (bind boundVars e) loc) expr}
    bindDiffDef ddef = BoundDiffDef (bind [] ddef) (_diffLoc ddef)
    bindExpr l@ELam {..} =
      let boundVars = map s2n $ L.nub $ _elamArgs ^.. traverse . _1
          loc = _eloc
       in l {_elamExpr = fmap (\e -> EBoundVars (bind boundVars e) loc) _elamExpr}
    bindExpr l@ELet {..} =
      let vs = map (s2n . name2String) ((l ^.. fv) :: [PVar])
       in EBoundVars (bind vs l) _eloc
    bindExpr c@ECase {..} =
      let ps =
            map
              ( \p ->
                  let vs = map (s2n . name2String) ((p ^.. fv) :: [PVar])
                   in BoundCase (bind vs p) (_caseLoc p)
              )
              _ecaseBody
       in c {_ecaseBody = ps}
    bindExpr expr = expr

-- | Remove variable bindings
removeVarBindings :: Module -> Module
removeVarBindings m =
  over (topStmts . traverse . _FDef . funcExpr . _Just) removeBindingsForExpr $
    over (topStmts . traverse . _ImplFDef . implFunDef . funcExpr . _Just) removeBindingsForExpr $
      over (topStmts . traverse . _DDef) removeBindingsForDiffDef m
  where
    removeBindingsForDiffDef (BoundDiffDef b _) =
      let (_, d) = unsafeUnbind b
       in removeBindingsForDiffDef d
    removeBindingsForDiffDef d = d 
    removeBindingsForExpr (EBoundVars b _) =
      let (_, e) = unsafeUnbind b
       in removeBindingsForExpr e
    removeBindingsForExpr l@ELam {..} =
      l {_elamExpr = fmap removeBindingsForExpr _elamExpr}
    removeBindingsForExpr e@ECase {..} =
      e
        { _ecaseExpr = removeBindingsForExpr _ecaseExpr,
          _ecaseBody = over traverse removeBindingsForCase _ecaseBody
        }
    removeBindingsForExpr w@EWhile {..} =
      w
        { _ewhileCond = removeBindingsForExpr _ewhileCond,
          _ewhileBody = removeBindingsForExpr _ewhileBody
        }
    removeBindingsForExpr a@EApp {..} =
      a
        { _eappFunc = removeBindingsForExpr _eappFunc,
          _eappArgs = over traverse removeBindingsForExpr _eappArgs
        }
    removeBindingsForExpr l@ELet {..} =
      l
        { _eletExpr = removeBindingsForExpr _eletExpr,
          _eletPattern = removeBindingsForPattern _eletPattern,
          _eletBody = removeBindingsForExpr _eletBody
        }
    removeBindingsForExpr h@EHandle {..} =
      h
        { _ehandleScope = removeBindingsForExpr _ehandleScope,
          _ehandleBindings = over (traverse . funcExpr . _Just) removeBindingsForExpr _ehandleBindings
        }
    removeBindingsForExpr s@ESeq {..} =
      s {_eseq = map removeBindingsForExpr _eseq}
    removeBindingsForExpr e@EAnn {..} =
      e {_eannExpr = removeBindingsForExpr _eannExpr}
    removeBindingsForExpr e@EAnnMeta {..} =
      e {_eannMetaExpr = removeBindingsForExpr _eannMetaExpr}
    removeBindingsForExpr expr = expr
    removeBindingsForPattern p@PExpr {..} =
      p {_pExpr = removeBindingsForExpr _pExpr}
    removeBindingsForPattern p = p
    removeBindingsForCase BoundCase {..} =
      let (_, c) = unsafeUnbind _boundCase
       in removeBindingsForCase c
    removeBindingsForCase c@Case {..} =
      c
        { _caseExpr = removeBindingsForExpr _caseExpr,
          _casePattern = removeBindingsForPattern _casePattern
        }
        