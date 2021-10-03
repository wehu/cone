{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Cone.AutoDiff where

import Cone.Env
import Cone.TypeChecker.Type
import Cone.TypeChecker.Expr
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

-- | Initializa diff rule
initDiffDef :: (Has EnvEff sig m) => String -> DiffDef -> m DiffDef
initDiffDef prefix d = do
  let pos = d ^. diffLoc
      fn = prefix ++ "/" ++ d ^. diffFunc
  o <- getEnv $ diffAdjs . at fn
  forMOf _Just o $ \o ->
    throwError $ "diff function redefine: " ++ fn ++ ppr pos
  let newDiff = d{_diffFunc = fn}
  setEnv (Just newDiff) $ diffAdjs . at fn
  return newDiff

-- | Initialize all diff function rules
initDiffDefs :: (Has EnvEff sig m) => Module -> m Module
initDiffDefs m = mapMOf (topStmts . traverse . _DDef) (initDiffDef $ m ^. moduleName) m

setupDiff :: (Has EnvEff sig m) => DiffDef -> FuncDef -> m FuncDef
setupDiff d f@FuncDef{..} = do
  resultTypes <- foldM (\ts a -> do
    let i = L.findIndex (\(e, _) -> a == e) _funcArgs
    case i of
      Just i -> return $ ts ++ [_funcArgs !! i ^. _2]
      Nothing -> throwError $ "cannot find wrt " ++ a ++ " in " ++ ppr f ++ ppr _funcLoc
    ) [] (_diffWRT d)
  let t:ts = reverse resultTypes
      resType = L.foldl' (\t e -> TApp (TVar (s2n "core/prelude/pair") _funcLoc) [e, t] _funcLoc) t ts
      fType = bindTypeEffVar _funcBoundEffVars $ bindTypeVar _funcBoundVars $
         TFunc (_funcArgs ^.. traverse . _2) (EffList [] _funcLoc) resType _funcLoc
  id <- fresh
  let fn = _funcName ++ "____diff" ++ show id
  setFuncType fn fType
  setEnv (Just _funcName) $ diffMapping . at fn
  return f{_funcName = fn, _funcArgs = _funcArgs, _funcResultType = resType, _funcExpr = Nothing}
setupDiff d BoundFuncDef{..} = do
  let (_, f) = unsafeUnbind _boundFuncDef
  setupDiff d f
setupDiff d BoundEffFuncDef {..} = do
  let (_, f) = unsafeUnbind _boundEffFuncDef
  setupDiff d f

setupDiffs :: (Has EnvEff sig m) => Module -> m Module
setupDiffs m = do
  let fs = m ^.. topStmts . traverse . _FDef
  diffs <- foldM (\ds f -> do
    d <- getEnv $ diffAdjs . at (_funcName f)
    case d of
      Just d ->
        if isn't _Just $ _diffAdj d
        then (\f -> (d ^. diffFunc, f):ds) <$> setupDiff d f
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
          let newDiff = d{_diffAdj=Just $ EVar (s2n $ _funcName f) (_funcLoc f)}
          setEnv (Just newDiff) $ diffAdjs . at n
          return newDiff
        Nothing -> return d

genConstantByType :: (Has EnvEff sig m) => String -> Type -> m Expr
genConstantByType c t@(TPrim pt _) = do
  let c' = case pt of
             F16 -> c ++ ".0"
             F32 -> c ++ ".0"
             F64 -> c ++ ".0"
             BF16 -> c ++ ".0"
             Pred -> if c == "0" then "false" else "true"
             _ -> c
  return $ ELit c' t (_tloc t)
genConstantByType c (TApp (TVar n _) [et, shape] loc) 
 | name2String n == "data/tensor/tensor" = do
  e <- genConstantByType c et
  return $ EApp False (EVar (s2n "data/tensor/full") loc) [shape, et] [e] loc
genConstantByType _ t = throwError $ "unsupported type " ++ ppr t ++ ppr (_tloc t)

genDiffForExpr :: (Has EnvEff sig m) => DiffDef -> Expr -> Expr -> m [Expr]
genDiffForExpr d f (EAnnMeta e@EVar{..} t _) = do
  zero <- genConstantByType "0" t
  let wrt = _diffWRT d
      diffs = map (\e -> if e == name2String _evarName then f else zero) wrt
  return diffs
genDiffForExpr _ _ e = throwError $ "unsupported expr for diff " ++ ppr e ++ ppr (_eloc e)

genDiff :: (Has EnvEff sig m) => M.Map String FuncDef -> FuncDef -> m FuncDef
genDiff fn2f f@FuncDef{} = do
  let loc = _funcLoc f
  orgFn <- getEnv $ diffMapping . at (_funcName f)
  case orgFn of
    Just orgFn -> do
      let orgF = fn2f ^. at orgFn
      forMOf _Nothing orgF $ \_ ->
        throwError $ "cannot find function by name " ++ ppr orgFn ++ ppr loc
      diff <- getEnv $ diffAdjs . at orgFn
      forMOf _Nothing diff $ \_ ->
        throwError $ "cannot find diff rule for " ++ ppr orgFn ++ ppr loc
      let d = fromJust diff
      e <- mapM (\e -> do
        c <- genConstantByType "1" (_funcResultType f)
        es <- genDiffForExpr d c e
        let e':es' = reverse es
        return $ L.foldl' (\t e -> EApp False (EVar (s2n "core/prelude/pair") loc) [] [t, e] loc) e' es')
        (_funcExpr $ fromJust orgF)
      return f{_funcExpr = e}
    Nothing -> return f
genDiff fn2f BoundFuncDef{..} = do
  let (vs, f) = unsafeUnbind _boundFuncDef
  f' <- genDiff fn2f f
  return $ BoundFuncDef (bind vs f') _funcLoc
genDiff fn2f BoundEffFuncDef {..} = do
  let (vs, f) = unsafeUnbind _boundEffFuncDef
  f' <- genDiff fn2f f
  return $ BoundEffFuncDef (bind vs f') _funcLoc

genDiffs :: (Has EnvEff sig m) => Module -> m Module
genDiffs m = do
  let fn2f = [(_funcName f, f)| f <- m ^..topStmts . traverse . _FDef]
  mapMOf (topStmts . traverse . _FDef) (genDiff $ M.fromList fn2f) m

replaceDiffFuncCalls :: (Has EnvEff sig m) => Module -> m Module
replaceDiffFuncCalls m = 
  mapMOf (topStmts . traverse . _FDef . funcExpr . _Just) replaceDiffFuncCall m
  >>= mapMOf (topStmts. traverse. _ImplFDef . implFunDef . funcExpr . _Just) replaceDiffFuncCall
  where replaceDiffFuncCall expr = transformM replace expr
        replace e@EApp{..} = do
          if _eappDiff then do
            let f = _eannMetaExpr _eappFunc
            when (isn't _EVar f) $ 
               throwError $ "expected a function name, but got " ++ ppr _eappFunc ++ ppr _eloc
            let n = name2String $ _evarName f
            d <- getEnv $ diffAdjs . at n
            case d of
              Just d -> return e{_eappFunc = fromJust $ _diffAdj d}
              Nothing -> throwError $ "cannot find diff rule for " ++ n ++ ppr _eloc
          else return e
        replace e = return e

setupAutoDiffs :: Module -> Env -> Int -> Either String (Env, (Int, Module))
setupAutoDiffs m env id =
  run . runError . runState env . runFresh id $
    do
      initDiffDefs m
      >>= setupDiffs

autoDiffs :: Module -> Env -> Int -> Either String (Env, (Int, Module))
autoDiffs m env id =
  run . runError . runState env . runFresh id $
    do
      genDiffs m
      >>= replaceDiffFuncCalls