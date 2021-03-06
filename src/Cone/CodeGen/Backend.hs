{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}

module Cone.CodeGen.Backend where

import Cone.Parser.AST
import Control.Carrier.Error.Either
import Control.Carrier.Fresh.Strict
import Control.Carrier.State.Strict
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Effect.Sum
import Control.Lens
import qualified Data.Map as M
import Data.Proxy
import Debug.Trace
import Prettyprinter
import qualified Data.Text as T

type Eff s e = Fresh :+: State s :+: Error e

data Env = Env
  { _currentModuleName :: String,
    _localState :: M.Map String Bool,
    _parameters :: M.Map String Bool
  }

makeLenses ''Env

initialEnv =
  Env
    { _currentModuleName = "",
      _localState = M.empty,
      _parameters = M.empty
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
  put env
  return res

replaceSpecialChars :: String -> String
replaceSpecialChars = T.unpack . T.replace (T.pack "$") (T.pack "_C_O_N_E_") . T.pack

-- | Targe proxy
data Target

-- | Backend interfaces
class Backend t where
  -- | Generate a module
  gen :: t Target -> Module -> Either String (Doc a)
  gen proxy m = do
    (env, (id, doc)) <- run . runError . runState initialEnv . runFresh 0 $ genModule proxy m
    return doc

  namePath :: t Target -> String -> Doc a

  typeN :: t Target -> String -> String -> Doc a

  funcN :: t Target -> String -> String -> Doc a

  genImport :: (Has EnvEff sig m) => t Target -> ImportStmt -> m (Doc a)

  genTypeDef :: (Has EnvEff sig m) => t Target -> TypeDef -> m (Doc a)

  genTypeCon :: (Has EnvEff sig m) => t Target -> String -> TypeCon -> m (Doc a)

  genEffectDef :: (Has EnvEff sig m) => t Target -> EffectDef -> m (Doc a)

  genFuncDef :: (Has EnvEff sig m) => t Target -> FuncDef -> m (Doc a)

  genExpr :: (Has EnvEff sig m) => t Target -> Expr -> m (Doc a)

  genPatternMatch :: (Has EnvEff sig m) => t Target -> Bool -> Pattern -> m (Doc a)

  genDiffDef :: (Has EnvEff sig m) => t Target -> DiffDef -> m (Doc a)
  genDiffDef _ _ = return emptyDoc 

  genPrologue :: (Has EnvEff sig m) => t Target -> m (Doc a)

  genEpilogue :: (Has EnvEff sig m) => t Target -> m (Doc a)

  genModule :: (Has EnvEff sig m) => t Target -> Module -> m (Doc a)

  genImplFuncDef :: (Has EnvEff sig m) => t Target -> ImplFuncDef -> m (Doc a)
  genImplFuncDef proxy ImplFuncDef {..} = genFuncDef proxy _implFunDef

  genTopStmt :: (Has EnvEff sig m) => t Target -> TopStmt -> m (Doc a)
  genTopStmt proxy TDef {..} = genTypeDef proxy _tdef
  genTopStmt proxy TAlias {} = return emptyDoc
  genTopStmt proxy EDef {..} = genEffectDef proxy _edef
  genTopStmt proxy FDef {..} = genFuncDef proxy _fdef
  genTopStmt proxy DDef {..} = genDiffDef proxy _ddef
  genTopStmt proxy ImplFDef {..} = genImplFuncDef proxy _implFdef
  genTopStmt proxy IDef{..} = return emptyDoc
  genTopStmt proxy ImplIDef{..} = return emptyDoc 

