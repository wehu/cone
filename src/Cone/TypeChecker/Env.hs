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
import Debug.Trace

type Eff s e = Fresh :+: State s :+: Error e

type TypeKinds = M.Map String Kind

type EffKinds = M.Map String EffKind

type EffIntfs = M.Map String [String]

type ExprTypes = M.Map String Type

data Env = Env
  { _types :: TypeKinds,
    _funcs :: ExprTypes,
    _effs :: EffKinds,
    _effIntfs :: EffIntfs,
    _localState :: ExprTypes
  }
  deriving (Show)

makeLenses ''Env

initialEnv =
  Env
    { _types = M.empty,
      _funcs = M.empty,
      _effs = M.empty,
      _effIntfs = M.empty,
      _localState = M.empty
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

setFuncType :: (Has EnvEff sig m) => String -> Type -> m ()
setFuncType n t = do
  setEnv (Just t) $ funcs .at n
  l <- getEnv localState
  setEnv (M.delete n l) localState

getFuncType :: (Has EnvEff sig m) => String -> m Type
getFuncType n = do
  v <- getEnv $ localState .at n
  case v of
    Just v -> return v
    Nothing -> do
      v <- getEnv $ funcs .at n
      case v of
        Just v -> return v
        Nothing -> throwError $ "cannot find variable: " ++ n

addEffIntfs :: (Has EnvEff sig m) => String -> String -> m ()
addEffIntfs effName intfName = do
  is <- getEnv $ effIntfs . at effName
  case is of
    Just is -> setEnv (Just $ intfName:is) $ effIntfs . at effName
    Nothing -> setEnv (Just [intfName]) $ effIntfs . at effName

freeVarName :: Int -> TVar
freeVarName i = makeName "$tvar" $ toInteger i

freeEffVarName :: Int -> EffVar
freeEffVarName i = makeName "$effvar" $ toInteger i

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

bindTypeEffVar :: [EffVar] -> Type -> Type
bindTypeEffVar bvs t = BoundEffVarType (bind bvs t) (_tloc t)

refresh :: (Has EnvEff sig m) => [TVar] -> Expr -> m ([TVar], Expr)
refresh vs e = do
  let pos = _eloc e
  nvs <- mapM (\_ -> freeVarName <$> fresh) vs
  return (nvs, substs [(f, TVar t pos) | f <- vs | t <- nvs] e)

refreshEffVar :: (Has EnvEff sig m) => [EffVar] -> Expr -> m ([EffVar], Expr)
refreshEffVar vs e = do
  let pos = _eloc e
  nvs <- mapM (\_ -> freeEffVarName <$> fresh) vs
  return (nvs, substs [(f, EffVarName t pos) | f <- vs | t <- nvs] e)

unbindType :: (Has EnvEff sig m) => Type -> m Type
unbindType b@BoundType {..} = do
  let (vs, t) = unsafeUnbind _boundType
      pos = _tloc
  nvs <- mapM (\_ -> freeVarName <$> fresh) vs
  unbindType $ substs [(f, TVar t pos) | f <- vs | t <- nvs] t
unbindType b@BoundEffVarType {..} = do
  let (vs, t) = unsafeUnbind _boundEffVarType
      pos = _tloc
  nvs <- mapM (\_ -> freeEffVarName <$> fresh) vs
  unbindType $ substs [(f, EffVarName t pos) | f <- vs | t <- nvs] t
unbindType t = return t

unbindTypeSimple :: Type -> ([TVar], [EffVar], Type)
unbindTypeSimple b@BoundType {..} = 
  let (bvs, t) = unsafeUnbind _boundType
      (bvs', evs, t') = unbindTypeSimple t
   in (bvs ++ bvs', evs, t')
unbindTypeSimple b@BoundEffVarType {..} =
  let (evs, t) = unsafeUnbind _boundEffVarType
      (bvs, evs', t') = unbindTypeSimple t
   in (bvs, evs ++ evs', t')
unbindTypeSimple t = ([], [], t)
