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
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe

type Eff s e = Fresh :+: State s :+: Error e

type TypeKinds = M.Map String Kind

type EffKinds = M.Map String EffKind

type ExprTypes = M.Map String Type

data Env = Env
  { _types :: TypeKinds,
    _funcs :: ExprTypes,
    _effs :: EffKinds,
    _locals :: ExprTypes
  }
  deriving (Show)

makeLenses ''Env

initialEnv =
  Env
    { _types = M.empty,
      _funcs = M.empty,
      _effs = M.empty,
      _locals = M.empty
    }

type EnvEff = Eff Env String

getEnv :: (Has EnvEff sig m) => Getter Env a -> m a
getEnv l = do
  env <- get @Env
  return $ view l env

setEnv :: (Has EnvEff sig m) => b -> Setter Env Env a b -> m ()
setEnv v l = do
  env <- get @Env
  put $ set l v env

underScope :: (Has EnvEff sig m) => m a -> m a
underScope f = do
  env <- get @Env
  res <- f
  put env
  return res

freeVarName :: Int -> TVar
freeVarName i = makeName "$" $ toInteger i

closeType :: Type -> Bind [TVar] Type
closeType t =
  let fvars = t ^.. fv
   in bind fvars t

closeEffType :: EffectType -> Bind [TVar] EffectType
closeEffType t =
  let fvars = t ^.. fv
   in bind fvars t

bindType :: [TVar] -> Type -> Type
bindType bvs t = BoundType (bind bvs t) (_tloc t)

bindEffType :: [TVar] -> EffectType -> EffectType
bindEffType bvs t = BoundEffType (bind bvs t) (_effLoc t)

refresh :: (Has EnvEff sig m) => [TVar] -> Expr -> m ([TVar], Expr)
refresh vs e =
  foldM
    ( \(vs, e) v -> do
        nv <- freeVarName <$> fresh
        return (vs++[nv], subst v (TVar nv $ _eloc e) e)
    )
    ([], e)
    vs

unbindType :: (Has EnvEff sig m) => Type -> m Type
unbindType b@BoundType {..} = do
  let (ps, t) = unsafeUnbind _boundType
      pos = _tloc
  foldM
    ( \t p -> do
        np <- freeVarName <$> fresh
        return $ subst p (TVar np pos) t
    )
    t
    ps >>= unbindType
unbindType t = return t

unbindEffType :: (Has EnvEff sig m) => EffectType -> m EffectType
unbindEffType b@BoundEffType {..} = do
  let (ps, t) = unsafeUnbind _boundEffType
      pos = _effLoc
  foldM
    ( \t p -> do
        np <- freeVarName <$> fresh
        unbindEffType $ subst p (TVar np pos) t
    )
    t
    ps >>= unbindEffType
unbindEffType t = return t

unbindTypeSimple :: Type -> ([TVar], Type)
unbindTypeSimple b@BoundType {..} = unsafeUnbind _boundType
unbindTypeSimple t = ([], t)

unbindEffTypeSimple :: EffectType -> ([TVar], EffectType)
unbindEffTypeSimple b@BoundEffType {..} = unsafeUnbind _boundEffType
unbindEffTypeSimple t = ([], t)
