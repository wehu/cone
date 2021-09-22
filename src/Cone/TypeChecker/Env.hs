{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Cone.TypeChecker.Env where

import Cone.Parser.AST
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Effect.Sum
import Control.Lens
import Control.Lens.Plated
import Control.Monad
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe

type Eff s e = Fresh :+: State s :+: Error e

type TypeKinds = M.Map String Kind

type EffKinds = M.Map String EffKind

type EffIntfs = M.Map String [String]

type ExprTypes = M.Map String Type

type FuncImpls = M.Map String Expr

type TypeBinds = M.Map String Type

type KindBinds = M.Map String Kind

type EffTypeBinds = M.Map String EffectType

type EffKindBinds = M.Map String EffKind

-- | The environment
data Env = Env
  { _types :: TypeKinds,
    _funcs :: ExprTypes,
    _funcImpls :: FuncImpls,
    _effs :: EffKinds,
    _effIntfs :: EffIntfs,
    _localState :: ExprTypes,
    _typeBinds :: TypeBinds,
    _kindBinds :: KindBinds,
    _effTypeBinds :: EffTypeBinds,
    _effKindBinds :: EffKindBinds
  }
  deriving (Show)

makeLenses ''Env

initialEnv =
  Env
    { _types = M.empty,
      _funcs = M.empty,
      _funcImpls = M.empty,
      _effs = M.empty,
      _effIntfs = M.empty,
      _localState = M.empty,
      _typeBinds = M.empty,
      _kindBinds = M.empty,
      _effTypeBinds = M.empty,
      _effKindBinds = M.empty
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

-- | Run under a local scope
underScope :: (Has EnvEff sig m) => m a -> m a
underScope f = do
  env <- get @Env
  res <- f
  tbs <- getEnv typeBinds
  kbs <- getEnv kindBinds
  ebs <- getEnv effTypeBinds
  ekbs <- getEnv effKindBinds
  put env {_typeBinds = tbs, _kindBinds = kbs, _effTypeBinds = ebs, _effKindBinds = ekbs}
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
