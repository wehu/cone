{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Cone.AutoDiff (autoDiffs) where

import Cone.Env
import Cone.Parser.AST
import Cone.TypeChecker.Expr
import Cone.TypeChecker.Type
import Control.Carrier.Error.Either
import Control.Carrier.Fresh.Strict
import Control.Carrier.State.Strict
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
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
  let newDiff = d {_diffFunc = fn}
  setEnv (Just newDiff) $ diffAdjs . at fn
  return newDiff

-- | Initialize all diff function rules
initDiffDefs :: (Has EnvEff sig m) => Module -> m Module
initDiffDefs m = mapMOf (topStmts . traverse . _DDef) (initDiffDef $ m ^. moduleName) m

setupDiff :: (Has EnvEff sig m) => DiffDef -> FuncDef -> m FuncDef
setupDiff d f@FuncDef {..} = do
  argTypes <-
    mapM
      ( \a -> do
          let i = L.findIndex (\(e, _) -> a == e) _funcArgs
          case i of
            Just i -> return $ _funcArgs !! i ^. _2
            Nothing -> throwError $ "cannot find wrt " ++ a ++ " in " ++ ppr f ++ ppr _funcLoc
      )
      (_diffWRT d)
  let argT : resT = reverse argTypes
      resTypes = L.foldl' (\t e -> TApp (TVar (s2n "core/prelude/pair") (_tloc e)) [t, e] (_tloc e)) argT resT
      fType =
        bindTypeEffVar _funcBoundEffVars $
          bindTypeVar _funcBoundVars $
            TFunc (_funcArgs ^.. traverse . _2 ++ [_funcResultType]) (EffList [] _funcLoc) resTypes _funcLoc
  let fn = _funcName ++ "____diff"
  setFuncType fn fType
  return f {_funcName = fn, _funcArgs = _funcArgs ++ [("____output____diff", _funcResultType)]}
setupDiff d BoundFuncDef {..} = do
  let (_, f) = unsafeUnbind _boundFuncDef
  setupDiff d f
setupDiff d BoundEffFuncDef {..} = do
  let (_, f) = unsafeUnbind _boundEffFuncDef
  setupDiff d f

genDiffs :: (Has EnvEff sig m) => Module -> m Module
genDiffs m = do
  let fs = m ^.. topStmts . traverse . _FDef
  diffs <-
    foldM
      ( \ds f -> do
          d <- getEnv $ diffAdjs . at (_funcName f)
          case d of
            Just d ->
              if isn't _Just $ _diffAdj d
                then do
                  (\f -> (d ^. diffFunc, f) : ds) <$> (setupDiff d f >>= addTempVariables >>= genDiff d)
                else return ds
            Nothing -> return ds
      )
      []
      fs
  mapMOf
    (topStmts . traverse . _DDef)
    (replace $ M.fromList diffs)
    m {_topStmts = m ^. topStmts ++ map FDef (diffs ^.. traverse . _2)}
  where
    replace :: (Has EnvEff sig m) => M.Map String FuncDef -> DiffDef -> m DiffDef
    replace diffs d = do
      let n = _diffFunc d
      case diffs ^. at n of
        Just f -> do
          when (isn't _Nothing $ _diffAdj d) $
            throwError $ "diff adj conflict " ++ ppr (_diffAdj d) ++ " vs " ++ ppr f ++ ppr (_diffLoc d)
          let newDiff = d {_diffAdj = Just $ EVar (s2n $ _funcName f) (_funcLoc f)}
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
genConstantByType _ t = throwError $ "unsupported type " ++ ppr t ++ ppr (_tloc t)

addTempVariables :: (Has EnvEff sig m) => FuncDef -> m FuncDef
addTempVariables = transformMOn (funcExpr . _Just) addTempVar
  where
    addTempVar a@(EApp False _ targs args loc) = do
      tempVs <- mapM (\arg -> fresh >>= (\id -> return $ "____temp" ++ show id)) args
      let newApp = a {_eappArgs = map (\v -> EVar (s2n v) loc) tempVs}
      (_, e) <-
        foldM
          ( \(i, newApp) vn -> do
              return (i - 1, ELet (PVar (s2n vn) loc) (args !! i) newApp False loc)
          )
          (L.length args - 1, newApp)
          (reverse tempVs)
      return e
    addTempVar e = return e

genDiffForExpr :: (Has EnvEff sig m) => String -> Expr -> m (Expr, [(String, Type)])
genDiffForExpr outputD e@EVar {..} = do
  let diffN = name2String _evarName ++ "____diff"
      diff = EVar (s2n diffN) _eloc
  return
    ( EApp
        False
        (EVar (s2n "core/prelude/____assign") _eloc)
        []
        [ diff,
          EApp
            False
            (EVar (s2n "core/prelude/____add") _eloc)
            []
            [diff, EVar (s2n (outputD ++ "____diff")) _eloc]
            _eloc
        ]
        _eloc,
      [(diffN, TPrim F32 _eloc)]
    )
genDiffForExpr outputD a@(EApp False (EVar n _) targs args loc) = do
  let fn = name2String n
      od = EVar (s2n (outputD ++ "____diff")) loc
  f <- getEnv $ diffAdjs . at fn
  forMOf _Nothing f $ \_ ->
    throwError $ "cannot find diff adj for function " ++ ppr fn ++ ppr loc
  fdef <- getEnv $ funcDefs . at fn
  forMOf _Nothing f $ \_ ->
    throwError $ "cannot find finction " ++ ppr fn ++ ppr loc
  inputDs <-
    L.nub
      <$> foldM
        ( \all (arg, farg) -> case arg of
            EVar an _ -> if farg ^. _1 `elem` _diffWRT (fromJust f) then return $ all ++ [(name2String an ++ "____diff", farg ^. _2)] else return all
            e -> throwError $ "unsupported " ++ ppr e
        )
        []
        [(arg, farg) | arg <- args | farg <- fromJust fdef ^. funcArgs]
  diffs <- mapM (\_ -> fresh >>= (\id -> return $ "____temp" ++ show id)) inputDs
  let d : ds = reverse diffs
      p = L.foldl' (\s e -> PApp (EVar (s2n "core/prelude/pair") loc) [] [PVar (s2n e) loc, s] loc) (PVar (s2n d) loc) ds
      setDiffs =
        [ EApp
            False
            (EVar (s2n "core/prelude/____assign") loc)
            []
            [EVar (s2n n) loc, EApp False (EVar (s2n "core/prelude/____add") loc) [] [EVar (s2n n) loc, EVar (s2n t) loc] loc]
            loc
          | n <- inputDs ^.. traverse . _1
          | t <- diffs
        ]
  return (ELet p (EApp False (fromJust $ _diffAdj $ fromJust f) targs (args ++ [od]) loc) (ESeq setDiffs loc) False loc, inputDs)
genDiffForExpr outputD s@ESeq {..} = do
  es <- mapM (genDiffForExpr outputD) (reverse _eseq)
  return (s {_eseq = es ^.. traverse . _1}, join $ es ^.. traverse . _2)
genDiffForExpr outputD l@(ELet p@(PVar v _) e body s loc) = do
  (db, bvs) <- genDiffForExpr outputD body
  (de, evs) <- genDiffForExpr (name2String v) e
  return (l {_eletBody = ESeq [db, de] loc}, bvs ++ evs)
genDiffForExpr outputD w@EWhile {..} = do
  db <- genDiffForExpr outputD _ewhileBody
  return (w {_ewhileBody = db ^. _1}, db ^. _2)
genDiffForExpr
  outputD
  c@( ECase
        _
        [ t@(Case (PExpr (ELit "true" (TPrim Pred _) _) _) _ te _),
          f@(Case (PExpr (ELit "false" (TPrim Pred _) _) _) _ fe _)
          ]
        loc
      ) = do
    dte <- genDiffForExpr outputD te
    dfe <- genDiffForExpr outputD fe
    return (c {_ecaseBody = [t {_caseExpr = dte ^. _1}, f {_caseExpr = dfe ^. _1}]}, dte ^. _2 ++ dfe ^. _2)
genDiffForExpr outputD l@ELit {..} = (,[]) <$> genConstantByType "0" _litType
genDiffForExpr outputD a@EAnn {..} = do
  d <- genDiffForExpr outputD _eannExpr
  return (a {_eannExpr = d ^. _1}, d ^. _2)
genDiffForExpr outputD a@EAnnMeta {..} = do
  d <- genDiffForExpr outputD _eannMetaExpr
  return (a {_eannMetaExpr = d ^. _1}, d ^. _2)
genDiffForExpr outputD b@EBoundTypeVars {..} = do
  let (vs, e) = unsafeUnbind _eboundTypeVars
  d <- genDiffForExpr outputD e
  return (b {_eboundTypeVars = bind vs $ d ^. _1}, d ^. _2)
genDiffForExpr outputD b@EBoundEffTypeVars {..} = do
  let (vs, e) = unsafeUnbind _eboundEffTypeVars
  d <- genDiffForExpr outputD e
  return (b {_eboundEffTypeVars = bind vs $ d ^. _1}, d ^. _2)
genDiffForExpr outputD b@EBoundVars {..} = do
  let (vs, e) = unsafeUnbind _eboundVars
  d <- genDiffForExpr outputD e
  return (b {_eboundVars = bind vs $ d ^. _1}, d ^. _2)
genDiffForExpr outputD e = throwError $ "unsupported expr for diff " ++ ppr e ++ ppr (_eloc e)

genDiff :: (Has EnvEff sig m) => DiffDef -> FuncDef -> m FuncDef
genDiff diff f@FuncDef {} = do
  let loc = _funcLoc f
  case _funcExpr f of
    Just e -> do
      (e, vs) <- genDiffForExpr "____output" e
      let d : ds = _diffWRT diff
          diffs = L.foldl' (\s e -> EApp False (EVar (s2n "core/prelude/pair") loc) [] [EVar (s2n e) loc, s] loc) (EVar (s2n d) loc) ds
      e <-
        foldM
          ( \s (e, t) -> do
              c0 <- genConstantByType "0" (TPrim F32 loc)
              return $ ELet (PVar (s2n e) loc) c0 s True loc
          )
          (ESeq [e, diffs] loc)
          (L.nubBy (\a b -> fst a == fst b) vs)
      return f {_funcExpr = Just e}
    Nothing -> return f
genDiff d BoundFuncDef {..} = do
  let (vs, f) = unsafeUnbind _boundFuncDef
  f' <- genDiff d f
  return $ BoundFuncDef (bind vs f') _funcLoc
genDiff d BoundEffFuncDef {..} = do
  let (vs, f) = unsafeUnbind _boundEffFuncDef
  f' <- genDiff d f
  return $ BoundEffFuncDef (bind vs f') _funcLoc

replaceDiffFuncCalls :: (Has EnvEff sig m) => Module -> m Module
replaceDiffFuncCalls m =
  mapMOf (topStmts . traverse . _FDef . funcExpr . _Just) replaceDiffFuncCall m
    >>= mapMOf (topStmts . traverse . _ImplFDef . implFunDef . funcExpr . _Just) replaceDiffFuncCall
  where
    replaceDiffFuncCall expr = transformM replace expr
    replace e@EApp {..} = do
      if _eappDiff
        then do
          let f = _eappFunc
          when (isn't _EVar f) $
            throwError $ "expected a function name, but got " ++ ppr _eappFunc ++ ppr _eloc
          let n = name2String $ _evarName f
          d <- getEnv $ diffAdjs . at n
          case d of
            Just d -> return e {_eappFunc = fromJust $ _diffAdj d}
            Nothing -> throwError $ "cannot find diff rule for " ++ n ++ ppr _eloc
        else return e
    replace e = return e

autoDiffs :: Module -> Env -> Int -> Either String (Env, (Int, Module))
autoDiffs m env id =
  run . runError . runState env . runFresh id $
    do
      initDiffDefs m
      >>= genDiffs
      >>= replaceDiffFuncCalls
