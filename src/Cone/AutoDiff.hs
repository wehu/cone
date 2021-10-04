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
  argTypes <- mapM (\a -> do
    let i = L.findIndex (\(e, _) -> a == e) _funcArgs
    case i of
      Just i -> return (_funcArgs !! i ^. _1 ++ "____diff", _funcArgs !! i ^. _2)
      Nothing -> throwError $ "cannot find wrt " ++ a ++ " in " ++ ppr f ++ ppr _funcLoc
    ) (_diffWRT d)
  let fType = bindTypeEffVar _funcBoundEffVars $ bindTypeVar _funcBoundVars $
         TFunc (_funcArgs ^.. traverse . _2 ++ argTypes ^.. traverse . _2) (EffList [] _funcLoc) _funcResultType _funcLoc
  id <- fresh
  let fn = _funcName ++ "____diff" ++ show id
  setFuncType fn fType
  -- setEnv (Just _funcName) $ diffMapping . at fn
  return f{_funcName = fn, _funcArgs = _funcArgs ++ argTypes}
setupDiff d BoundFuncDef{..} = do
  let (_, f) = unsafeUnbind _boundFuncDef
  setupDiff d f
setupDiff d BoundEffFuncDef {..} = do
  let (_, f) = unsafeUnbind _boundEffFuncDef
  setupDiff d f

genDiffs :: (Has EnvEff sig m) => Module -> m Module
genDiffs m = do
  let fs = m ^.. topStmts . traverse . _FDef
  diffs <- foldM (\ds f -> do
    d <- getEnv $ diffAdjs . at (_funcName f)
    case d of
      Just d ->
        if isn't _Just $ _diffAdj d
        then do
          (\f -> (d ^. diffFunc, f):ds) <$> (setupDiff d f >>= genDiff)
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

genDiffForExpr :: (Has EnvEff sig m) => Expr -> m Expr
genDiffForExpr e@EVar{..} = return e{_evarName=s2n (name2String _evarName ++ "____diff")}
genDiffForExpr a@(EApp _ (EVar n _) targs args loc) = do
  let fn = name2String n
  f <- getEnv $ diffAdjs . at fn
  forMOf _Nothing f $ \_ ->
    throwError $ "cannot find diff adj for function " ++ ppr fn ++ ppr loc
  diffs <- mapM genDiffForExpr args
  return $ EApp False (fromJust $ _diffAdj $ fromJust f) targs (args ++ diffs) loc
genDiffForExpr s@ESeq{..} = do
  es <- mapM genDiffForExpr _eseq
  return s{_eseq=es}
genDiffForExpr l@(ELet (PVar v _) e body s loc) = do
  let vn = name2String v
      dvn = vn ++ "____diff"
  de <- genDiffForExpr e
  db <- genDiffForExpr body
  let newBody = ELet (PVar (s2n dvn) loc) de db s loc
  return l{_eletBody=newBody}
genDiffForExpr w@EWhile{..} = do
  db <- genDiffForExpr _ewhileBody
  return w{_ewhileBody=db}
genDiffForExpr c@(ECase cond
    [t@(Case (PExpr (ELit "true"  (TPrim Pred _) _) _) _ te _)
    ,f@(Case (PExpr (ELit "false" (TPrim Pred _) _) _) _ fe _)] loc) = do
  dte <- genDiffForExpr te
  dfe <- genDiffForExpr fe
  return c{_ecaseBody=[t{_caseExpr=dte}, f{_caseExpr=dfe}]}
genDiffForExpr l@ELit{} = return l
genDiffForExpr a@EAnn{..} = do
  d <- genDiffForExpr _eannExpr
  return a{_eannExpr=d}
genDiffForExpr a@EAnnMeta{..} = do
  d <- genDiffForExpr _eannMetaExpr
  return a{_eannMetaExpr=d}
genDiffForExpr b@EBoundTypeVars{..} = do
  let (vs, e) = unsafeUnbind _eboundTypeVars
  d <- genDiffForExpr e
  return b{_eboundTypeVars=bind vs d}
genDiffForExpr b@EBoundEffTypeVars{..} = do
  let (vs, e) = unsafeUnbind _eboundEffTypeVars
  d <- genDiffForExpr e
  return b{_eboundEffTypeVars=bind vs d}
genDiffForExpr b@EBoundVars{..} = do
  let (vs, e) = unsafeUnbind _eboundVars
  d <- genDiffForExpr e
  return b{_eboundVars=bind vs d}
genDiffForExpr e = throwError $ "unsupported expr for diff " ++ ppr e ++ ppr (_eloc e)

genDiff :: (Has EnvEff sig m) => FuncDef -> m FuncDef
genDiff f@FuncDef{} = do
  let loc = _funcLoc f
  e <- mapM genDiffForExpr (_funcExpr f)
  return f{_funcExpr = e}
genDiff BoundFuncDef{..} = do
  let (vs, f) = unsafeUnbind _boundFuncDef
  f' <- genDiff f
  return $ BoundFuncDef (bind vs f') _funcLoc
genDiff BoundEffFuncDef {..} = do
  let (vs, f) = unsafeUnbind _boundEffFuncDef
  f' <- genDiff f
  return $ BoundEffFuncDef (bind vs f') _funcLoc

replaceDiffFuncCalls :: (Has EnvEff sig m) => Module -> m Module
replaceDiffFuncCalls m = 
  mapMOf (topStmts . traverse . _FDef . funcExpr . _Just) replaceDiffFuncCall m
  >>= mapMOf (topStmts. traverse. _ImplFDef . implFunDef . funcExpr . _Just) replaceDiffFuncCall
  where replaceDiffFuncCall expr = transformM replace expr
        replace e@EApp{..} = do
          if _eappDiff then do
            let f = _eappFunc
            when (isn't _EVar f) $ 
               throwError $ "expected a function name, but got " ++ ppr _eappFunc ++ ppr _eloc
            let n = name2String $ _evarName f
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
      initDiffDefs m
      >>= genDiffs
      >>= replaceDiffFuncCalls