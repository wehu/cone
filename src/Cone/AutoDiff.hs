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

genDiff :: (Has EnvEff sig m) => FuncDef -> m FuncDef
genDiff f@FuncDef{..} = do
  d <- getEnv $ diffAdjs . at _funcName
  case d of
    Just _ -> return f
    Nothing -> return f

genDiffs :: (Has EnvEff sig m) => Module -> m Module
genDiffs = mapMOf (topStmts . traverse . _FDef) genDiff

autoDiffs :: Module -> Env -> Int -> Either String (Env, (Int, Module))
autoDiffs m env id =
  run . runError . runState env . runFresh id $
    do
      genDiffs m