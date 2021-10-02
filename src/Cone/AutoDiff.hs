{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Cone.AutoDiff where

import Cone.Env
import Cone.Parser.AST
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Carrier.Error.Either
import Control.Carrier.Fresh.Strict
import Control.Carrier.State.Strict
import Control.Lens
import Control.Lens.Plated
import Control.Monad
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe

genDiff :: (Has EnvEff sig m) => DiffDef -> FuncDef -> m FuncDef
genDiff d f@FuncDef{..} = return f
genDiff d BoundFuncDef{..} = do
  let (_, f) = unsafeUnbind _boundFuncDef
  genDiff d f
genDiff d BoundEffFuncDef {..} = do
  let (_, f) = unsafeUnbind _boundEffFuncDef
  genDiff d f

genDiffs :: (Has EnvEff sig m) => Module -> m Module
genDiffs m = do
  let fs = m ^.. topStmts . traverse . _FDef
  diffs <- foldM (\ds f -> do
    d <- getEnv $ diffAdjs . at (_funcName f)
    case d of
      Just d -> (\d -> FDef d:ds) <$> genDiff d f
      Nothing -> return ds)
    []
    fs
  return m{_topStmts=m^.topStmts ++ diffs}

autoDiffs :: Module -> Env -> Int -> Either String (Env, (Int, Module))
autoDiffs m env id =
  run . runError . runState env . runFresh id $
    do
      genDiffs m