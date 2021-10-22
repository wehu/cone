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

type IntfFuncs = M.Map String [String]

type IntfImpl = (String,Type,Type,Int)

type IntfImpls = M.Map String [IntfImpl]

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
    _specializedFuncTypes :: FuncTypes,
    _intfFuncs :: IntfFuncs,
    _intfImpls :: IntfImpls
  }
  deriving (Show, Eq)

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
      _specializedFuncTypes = M.empty,
      _intfFuncs = M.empty,
      _intfImpls = M.empty
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
bindTypeVar :: [(TVar, Maybe Kind, [Type])] -> Type -> Type
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
unbindTypeSimple :: Type -> ([(TVar, Maybe Kind, [Type])], [EffVar], Type)
unbindTypeSimple b@BoundType {..} =
  let (bvs, t) = unsafeUnbind _boundType
      (bvs', evs, t') = unbindTypeSimple t
   in (bvs ++ bvs', evs, t')
unbindTypeSimple b@BoundEffVarType {..} =
  let (evs, t) = unsafeUnbind _boundEffVarType
      (bvs, evs', t') = unbindTypeSimple t
   in (bvs, evs ++ evs', t')
unbindTypeSimple t = ([], [], t)

bindTypeEDef :: EffectDef -> EffectDef
bindTypeEDef edef =
  let boundVars = L.nub $ edef ^.. effectArgs . traverse
      edef' = over (effectIntfs . traverse) (bindTypeEffIntf boundVars) edef
   in BoundEffectDef (bind (boundVars ^.. traverse . _1) edef') (_effectLoc edef)

bindTypeEffIntf :: [(TVar, Maybe Kind)] -> FuncIntf -> FuncIntf
bindTypeEffIntf bvs intf =
  let boundVars = L.nub $ bvs ^.. traverse . _1 ++ intf ^.. intfBoundVars . traverse . _1
      boundEffVars = L.nub $ intf ^. intfBoundEffVars
      loc = intf ^. intfLoc
   in BoundEffFuncIntf (bind boundEffVars $ BoundFuncIntf (bind boundVars intf) loc) loc

bindTypeTDef :: TypeDef -> TypeDef
bindTypeTDef tdef =
  let boundVars = L.nub $ tdef ^.. typeArgs . traverse . _1
   in BoundTypeDef (bind boundVars tdef) (_typeLoc tdef)

bindTypeTAlias :: TypeAlias -> TypeAlias
bindTypeTAlias talias =
  let boundVars = L.nub $ talias ^.. typeAliasArgs . traverse . _1
   in BoundTypeAlias (bind boundVars talias) (_typeAliasLoc talias)

bindTypeIDef :: InterfaceDef -> InterfaceDef
bindTypeIDef idef =
  let boundVars = [idef ^. interfaceTVar . _1]
   in BoundInterfaceDef (bind boundVars idef) (_interfaceLoc idef)

bindTypeImplIDef :: ImplInterfaceDef -> ImplInterfaceDef
bindTypeImplIDef idef =
  let boundVars = idef ^.. implInterfaceBoundVars . traverse . _1
   in BoundImplInterfaceDef (bind boundVars idef) (_implInterfaceLoc idef)

bindTypeFDef :: FuncDef -> FuncDef
bindTypeFDef fdef =
  let boundVars = L.nub $ fdef ^. funcBoundVars
      boundEffVars = L.nub $ fdef ^. funcBoundEffVars
      loc = fdef ^. funcLoc
      expr = transform bindTypeExpr <$> _funcExpr fdef
   in BoundEffFuncDef (bind boundEffVars $ BoundFuncDef (bind (boundVars ^.. traverse . _1) fdef {_funcExpr = expr}) loc) loc

bindTypeExpr :: Expr -> Expr
bindTypeExpr l@ELam {..} =
  let boundVars = L.nub _elamBoundVars
      boundEffVars = L.nub _elamBoundEffVars
   in  EBoundEffTypeVars (bind boundEffVars $ EBoundTypeVars (bind (boundVars ^.. traverse . _1) l) _eloc) _eloc
bindTypeExpr expr = expr

-- | Add type bindings
addTypeBindings :: Module -> Module
addTypeBindings m =
  over (topStmts . traverse . _EDef) bindTypeEDef $
    over (topStmts . traverse . _TDef) bindTypeTDef $
      over (topStmts . traverse . _FDef) bindTypeFDef $
        over (topStmts . traverse . _ImplFDef . implFunDef) bindTypeFDef $
          over (topStmts . traverse . _TAlias) bindTypeTAlias $
            over (topStmts . traverse . _IDef ) bindTypeIDef $
              over (topStmts . traverse . _ImplIDef) bindTypeImplIDef m

removeTypeBindingsForEDef :: EffectDef -> EffectDef
removeTypeBindingsForEDef (BoundEffectDef b _) =
  let (_, e) = unsafeUnbind b
   in removeTypeBindingsForEDef e
removeTypeBindingsForEDef e =
  over (effectIntfs . traverse) removeTypeBindingsForIntf e
  
removeTypeBindingsForIntf :: FuncIntf -> FuncIntf
removeTypeBindingsForIntf (BoundFuncIntf b _) =
  let (_, i) = unsafeUnbind b
   in removeTypeBindingsForIntf i
removeTypeBindingsForIntf (BoundEffFuncIntf b _) =
  let (_, i) = unsafeUnbind b
   in removeTypeBindingsForIntf i
removeTypeBindingsForIntf intf = intf

removeTypeBindingsForTDef :: TypeDef -> TypeDef
removeTypeBindingsForTDef (BoundTypeDef b _) =
  let (_, t) = unsafeUnbind b
   in removeTypeBindingsForTDef t
removeTypeBindingsForTDef t = t

removeTypeBindingsForIDef :: InterfaceDef -> InterfaceDef
removeTypeBindingsForIDef (BoundInterfaceDef b _) =
  let (_, t) = unsafeUnbind b
   in removeTypeBindingsForIDef t
removeTypeBindingsForIDef t = t

removeTypeBindingsForImplIDef :: ImplInterfaceDef -> ImplInterfaceDef
removeTypeBindingsForImplIDef (BoundImplInterfaceDef b _) =
  let (_, t) = unsafeUnbind b
   in removeTypeBindingsForImplIDef t
removeTypeBindingsForImplIDef t = t

removeTypeBindingsForTypeAlias :: TypeAlias -> TypeAlias
removeTypeBindingsForTypeAlias (BoundTypeAlias b _) =
  let (_, t) = unsafeUnbind b
   in removeTypeBindingsForTypeAlias t
removeTypeBindingsForTypeAlias t = t

removeTypeBindingsForFDef :: FuncDef -> FuncDef
removeTypeBindingsForFDef (BoundFuncDef b _) =
  let (_, f) = unsafeUnbind b
   in removeTypeBindingsForFDef f
removeTypeBindingsForFDef (BoundEffFuncDef b _) =
  let (_, f) = unsafeUnbind b
   in removeTypeBindingsForFDef f
removeTypeBindingsForFDef fdef =
  let expr = removeTypeBindingsForExpr <$> _funcExpr fdef
   in fdef {_funcExpr = expr}

removeTypeBindingsForExpr :: Expr -> Expr
removeTypeBindingsForExpr (EBoundTypeVars b _) =
  let (_, e) = unsafeUnbind b
   in removeTypeBindingsForExpr e
removeTypeBindingsForExpr (EBoundEffTypeVars b _) =
  let (_, e) = unsafeUnbind b
   in removeTypeBindingsForExpr e
removeTypeBindingsForExpr l@ELam {..} =
  l {_elamExpr = fmap removeTypeBindingsForExpr _elamExpr}
removeTypeBindingsForExpr e@ECase {..} =
  e
    { _ecaseExpr = removeTypeBindingsForExpr _ecaseExpr,
      _ecaseBody = over traverse removeTypeBindingsForCase _ecaseBody
    }
removeTypeBindingsForExpr w@EWhile {..} =
  w
    { _ewhileCond = removeTypeBindingsForExpr _ewhileCond,
      _ewhileBody = removeTypeBindingsForExpr _ewhileBody
    }
removeTypeBindingsForExpr a@EApp {..} =
  a
    { _eappFunc = removeTypeBindingsForExpr _eappFunc,
      _eappArgs = over traverse removeTypeBindingsForExpr _eappArgs
    }
removeTypeBindingsForExpr l@ELet {..} =
  l
    { _eletExpr = removeTypeBindingsForExpr _eletExpr,
      _eletPattern = removeTypeBindingsForPattern _eletPattern,
      _eletBody = removeTypeBindingsForExpr _eletBody
    }
removeTypeBindingsForExpr h@EHandle {..} =
  h
    { _ehandleScope = removeTypeBindingsForExpr _ehandleScope,
      _ehandleBindings = map removeTypeBindingsForFDef _ehandleBindings
    }
removeTypeBindingsForExpr s@ESeq {..} =
  s {_eseq = map removeTypeBindingsForExpr _eseq}
removeTypeBindingsForExpr e@EAnn {..} =
  e {_eannExpr = removeTypeBindingsForExpr _eannExpr}
removeTypeBindingsForExpr e@EAnnMeta {..} =
  e {_eannMetaExpr = removeTypeBindingsForExpr _eannMetaExpr}
removeTypeBindingsForExpr expr = expr

removeTypeBindingsForPattern :: Pattern -> Pattern
removeTypeBindingsForPattern p@PExpr {..} =
  p {_pExpr = removeTypeBindingsForExpr _pExpr}
removeTypeBindingsForPattern p = p

removeTypeBindingsForCase :: Case -> Case
removeTypeBindingsForCase c@Case {..} =
  c
    { _caseExpr = removeTypeBindingsForExpr _caseExpr,
      _casePattern = removeTypeBindingsForPattern _casePattern
    }
removeTypeBindingsForCase c = c

-- | Remove type bindings
removeTypeBindings :: Module -> Module
removeTypeBindings m =
  over (topStmts . traverse . _EDef) removeTypeBindingsForEDef $
    over (topStmts . traverse . _TDef) removeTypeBindingsForTDef $
      over (topStmts . traverse . _FDef) removeTypeBindingsForFDef $
        over (topStmts . traverse . _ImplFDef . implFunDef) removeTypeBindingsForFDef $
          over (topStmts . traverse . _TAlias) removeTypeBindingsForTypeAlias $
            over (topStmts . traverse ._IDef) removeTypeBindingsForIDef $
              over (topStmts . traverse . _ImplIDef) removeTypeBindingsForImplIDef m

bindVarExpr :: Expr -> Expr
bindVarExpr l@ELam {..} =
  let boundVars = map s2n $ L.nub $ _elamArgs ^.. traverse . _1
      loc = _eloc
   in l {_elamExpr = fmap (\e -> EBoundVars (bind boundVars e) loc) _elamExpr}
bindVarExpr l@ELet {..} =
  let vs = map (s2n . name2String) ((l ^.. fv) :: [PVar])
   in EBoundVars (bind vs l) _eloc
bindVarExpr c@ECase {..} =
  let ps =
        map
          ( \p ->
              let vs = map (s2n . name2String) ((p ^.. fv) :: [PVar])
               in BoundCase (bind vs p) (_caseLoc p)
          )
          _ecaseBody
   in c {_ecaseBody = ps}
bindVarExpr expr = expr

-- | Add variable bindings
addVarBindings :: Module -> Module
addVarBindings m =
  over (topStmts . traverse . _FDef) bindTypeFDef $
    over (topStmts . traverse . _ImplFDef . implFunDef) bindTypeFDef $
      over (topStmts . traverse . _DDef) bindDiffDef m
  where
    bindTypeFDef fdef =
      let boundVars = map s2n $ L.nub $ fdef ^.. funcArgs . traverse . _1
          loc = fdef ^. funcLoc
          expr = transform bindVarExpr <$> _funcExpr fdef
       in fdef {_funcExpr = fmap (\e -> EBoundVars (bind boundVars e) loc) expr}
    bindDiffDef ddef = BoundDiffDef (bind [] ddef) (_diffLoc ddef)

-- | Remove variable bindings
removeVarBindings :: Module -> Module
removeVarBindings m =
  over (topStmts . traverse . _FDef . funcExpr . _Just) removeVarBindingsForExpr $
    over (topStmts . traverse . _ImplFDef . implFunDef . funcExpr . _Just) removeVarBindingsForExpr $
      over (topStmts . traverse . _DDef) removeVarBindingsForDiffDef m

removeVarBindingsForDiffDef :: DiffDef -> DiffDef
removeVarBindingsForDiffDef (BoundDiffDef b _) =
  let (_, d) = unsafeUnbind b
   in removeVarBindingsForDiffDef d
removeVarBindingsForDiffDef d = d 

removeVarBindingsForExpr :: Expr -> Expr
removeVarBindingsForExpr (EBoundVars b _) =
  let (_, e) = unsafeUnbind b
   in removeVarBindingsForExpr e
removeVarBindingsForExpr l@ELam {..} =
  l {_elamExpr = fmap removeVarBindingsForExpr _elamExpr}
removeVarBindingsForExpr e@ECase {..} =
  e
    { _ecaseExpr = removeVarBindingsForExpr _ecaseExpr,
      _ecaseBody = over traverse removeVarBindingsForCase _ecaseBody
    }
removeVarBindingsForExpr w@EWhile {..} =
  w
    { _ewhileCond = removeVarBindingsForExpr _ewhileCond,
      _ewhileBody = removeVarBindingsForExpr _ewhileBody
    }
removeVarBindingsForExpr a@EApp {..} =
  a
    { _eappFunc = removeVarBindingsForExpr _eappFunc,
      _eappArgs = over traverse removeVarBindingsForExpr _eappArgs
    }
removeVarBindingsForExpr l@ELet {..} =
  l
    { _eletExpr = removeVarBindingsForExpr _eletExpr,
      _eletPattern = removeVarBindingsForPattern _eletPattern,
      _eletBody = removeVarBindingsForExpr _eletBody
    }
removeVarBindingsForExpr h@EHandle {..} =
  h
    { _ehandleScope = removeVarBindingsForExpr _ehandleScope,
      _ehandleBindings = over (traverse . funcExpr . _Just) removeVarBindingsForExpr _ehandleBindings
    }
removeVarBindingsForExpr s@ESeq {..} =
  s {_eseq = map removeVarBindingsForExpr _eseq}
removeVarBindingsForExpr e@EAnn {..} =
  e {_eannExpr = removeVarBindingsForExpr _eannExpr}
removeVarBindingsForExpr e@EAnnMeta {..} =
  e {_eannMetaExpr = removeVarBindingsForExpr _eannMetaExpr}
removeVarBindingsForExpr expr = expr

removeVarBindingsForPattern :: Pattern -> Pattern
removeVarBindingsForPattern p@PExpr {..} =
  p {_pExpr = removeVarBindingsForExpr _pExpr}
removeVarBindingsForPattern p = p

removeVarBindingsForCase :: Case -> Case
removeVarBindingsForCase BoundCase {..} =
  let (_, c) = unsafeUnbind _boundCase
   in removeVarBindingsForCase c
removeVarBindingsForCase c@Case {..} =
  c
    { _caseExpr = removeVarBindingsForExpr _caseExpr,
      _casePattern = removeVarBindingsForPattern _casePattern
    }
        