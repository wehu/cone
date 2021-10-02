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
genDiff d f@FuncDef{..} = do
  resultTypes <- foldM (\ts a -> do
    let i = L.findIndex (\(e, _) -> a == e) _funcArgs
    case i of
      Just i -> return $ ts ++ [_funcArgs !! i ^. _2]
      Nothing -> throwError $ "cannot find wrt " ++ a ++ " in " ++ ppr f ++ ppr _funcLoc
    ) [] (_diffWRT d)
  let t:ts = reverse resultTypes
      resType = L.foldl' (\t e -> TApp (TVar (s2n "core/prelude/pair") _funcLoc) [e, t] _funcLoc) t ts
      fType = TFunc (_funcArgs ^.. traverse . _2) (EffList [] _funcLoc) resType _funcLoc
  id <- fresh
  let fn = _funcName ++ "____diff" ++ show id
  return f{_funcName = fn, _funcArgs = _funcArgs, _funcResultType = resType}
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
      Just d ->
        if isn't _Just $ _diffAdj d
        then (\f -> (d ^. diffFunc, f):ds) <$> genDiff d f
        else return ds
      Nothing -> return ds)
    []
    fs
  mapMOf (topStmts . traverse . _DDef) (replace $ M.fromList diffs)
   m{_topStmts=m^.topStmts ++ map FDef (diffs ^.. traverse . _2)}
  where
    replace :: (Has EnvEff sig m) => M.Map String FuncDef -> DiffDef -> m DiffDef
    replace diffs d = do
      let n = _diffFunc d
      case diffs ^. at n of
        Just f -> do
          when (isn't _Nothing $ _diffAdj d) $
            throwError $ "diff adj conflict " ++ ppr (_diffAdj d) ++ " vs " ++ ppr f ++ ppr (_diffLoc d)
          return d{_diffAdj=Just $ EVar (s2n $ _funcName f) (_funcLoc f)}
        Nothing -> return d

replaceDiffFuncCalls :: (Has EnvEff sig m) => Module -> m Module
replaceDiffFuncCalls m = 
  mapMOf (topStmts . traverse . _FDef . funcExpr . _Just) replaceDiffFuncCall m
  >>= mapMOf (topStmts. traverse. _ImplFDef . implFunDef . funcExpr . _Just) replaceDiffFuncCall
  where replaceDiffFuncCall expr = transformM replace expr
        replace e@EApp{..} = do
          if _eappDiff then do
            when (isn't _EVar _eappFunc) $ 
               throwError $ "expected a function name, but got " ++ ppr _eappFunc ++ ppr _eloc
            let n = name2String $ _evarName _eappFunc
            d <- getEnv $ diffAdjs . at n
            case d of
              Just d -> return e{_eappFunc = fromJust $ _diffAdj d}
              Nothing -> throwError $ "cannot find diff rule for " ++ n ++ ppr _eloc
          else return e
        replace e = return e

autoDiffs :: Module -> Env -> Int -> Either String (Env, (Int, Module))
autoDiffs m env id =
  run . runError . runState env . runFresh id $
    do
      genDiffs m
      >>= replaceDiffFuncCalls