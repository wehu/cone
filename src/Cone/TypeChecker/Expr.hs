{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Cone.TypeChecker.Expr where

import Conduit
import Cone.Parser.AST
import Cone.TypeChecker.Env
import Cone.TypeChecker.Type
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Lens
import Control.Lens.Plated
import Control.Monad
import Control.Monad.ST
import Data.Default.Class (def)
import qualified Data.ExtendedReal as E
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Interval as I
import qualified Data.List as L
import Data.List.Split
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace
import GHC.Real
import ToySolver.Arith.BoundsInference
import ToySolver.Arith.Simplex
import qualified ToySolver.Data.LA as LA
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe

-- | Annotate expression with type
annotateExpr :: Expr -> Type -> Expr
annotateExpr e t = EAnnMeta e t (_eloc e)

-- | Return the type in annotation meta
typeOfExpr :: (Has EnvEff sig m) => Expr -> m Type
typeOfExpr (EAnnMeta _ t _) = return t
typeOfExpr e = throwError $ "expected an annotated expression, but got " ++ ppr e

-- | Select a function implementation based on type
selectFuncImpl :: (Has EnvEff sig m) => Expr -> m Expr
selectFuncImpl e@(EAnnMeta (EVar fn' _) t loc) = do
  let fn = name2String fn'
  catchError
    ( do
        let sel = uniqueFuncImplName fn t
        impls <- getEnv funcImpls
        case impls ^. at sel of
          Nothing -> throwError ""
          Just l -> return $ EAnnMeta l t loc
    )
    ( \(_ :: String) -> do
        getFuncType loc fn
        return e
    )
selectFuncImpl e = return e

-- | Infer expression's type
inferExprType :: (Has EnvEff sig m) => Expr -> m Expr
inferExprType e@EVar {..} = do
  t <- (getFuncType _eloc $ name2String _evarName) >>= inferType
  return $ annotateExpr e t
inferExprType a@EApp {..} = do
  -- check assign variable
  if (name2String $ _eappFunc ^. evarName) == "____assign"
    then do
      if L.length _eappArgs /= 2
        then throwError $ "expected 2 arguments: " ++ ppr a ++ ppr _eloc
        else
          if isn't _EVar $ head _eappArgs
            then throwError $ "cannot assign to an expression: " ++ ppr (head _eappArgs) ++ ppr _eloc
            else -- first argument is the assigned variable which should be in local state
            do
              let vn = name2String $ (head _eappArgs) ^. evarName
              v <- getEnv $ localState . at vn
              case v of
                Just v -> return ()
                Nothing -> throwError $ "cannot find local variable " ++ vn ++ ppr _eloc
    else return ()
  -- infer all type arguments
  mapM_ inferTypeKind _eappTypeArgs
  typeArgs <- mapM inferType _eappTypeArgs
  -- infer app function type
  appFunc <- inferExprType _eappFunc
  appFuncType <- typeOfExpr appFunc
  appFuncType <- applyTypeArgs appFuncType _eappTypeArgs >>= unbindType
  -- infer all arguments' types
  args <- mapM inferExprType _eappArgs
  argTypes <- mapM typeOfExpr args
  argKinds <- mapM inferTypeKind argTypes
  mapM_ checkTypeKind argKinds
  -- infer the result type
  (t, ft) <- inferAppResultType appFuncType typeArgs argTypes
  t <- inferType t
  appFunc <- selectFuncImpl appFunc {_eannMetaType = bindTypeEffVar [] $ bindTypeVar [] ft}
  return $ annotateExpr a {_eappFunc = appFunc, _eappArgs = args} t
inferExprType l@ELam {..} = underScope $ do
  -- clear localState, lambda cannot capture local state variables
  setEnv M.empty localState
  -- refresh all bound variables
  (bvs, newLam) <- refreshTypeVar (_elamBoundVars ^.. traverse . _1) l
  (evs, newLam) <- refreshEffVar _elamBoundEffVars newLam
  case newLam of
    l@ELam {..} -> do
      -- add all bound type variables into env
      mapM_
        (\(t, k) -> setEnv (Just $ k ^. non (KStar _eloc)) $ types . at (name2String t))
        [(t, k) | t <- bvs | k <- _elamBoundVars ^.. traverse . _2]
      -- add all bound eff type variables into env
      mapM_ (\t -> setEnv (Just $ EKStar _eloc) $ effs . at (name2String t)) evs
      -- infer arguments
      args <-
        mapM
          ( \(_, t) -> do
              k <- inferTypeKind t
              checkTypeKind k
              inferType t
          )
          _elamArgs
      -- infer effect type kind
      ek <- inferEffKind _elamEffType
      checkEffKind ek
      -- add lambda argument types into env's local scope
      mapM_
        (\(n, t) -> setFuncType n t)
        [(n, t) | (n, _) <- _elamArgs | t <- args]
      case _elamExpr of
        Just e -> return ()
        Nothing -> throwError $ "expected an expression for lambda" ++ ppr _eloc
      -- infer the lambda's expression type
      lamE <- (inferExprType $ fromJust _elamExpr)
      eType <- typeOfExpr lamE
      -- infer the lambda's result type
      k <- inferTypeKind _elamResultType
      checkTypeKind k
      checkTypeMatch eType _elamResultType
      -- return the lambda type
      t <-
        inferType $
          bindTypeEffVar evs $
            bindTypeVar
              [(t, k) | t <- bvs | k <- _elamBoundVars ^.. traverse . _2]
              $ TFunc args _elamEffType eType _eloc
      return $ annotateExpr l {_elamExpr = Just lamE} t
    _ -> throwError $ "should not be here"
inferExprType a@EAnn {..} = do
  et <- inferExprType _eannExpr
  t <- typeOfExpr et
  k <- inferTypeKind _eannType
  checkTypeKind k
  at <- inferType _eannType
  bindings <- collectVarBindings t at >>= checkVarBindings
  let aet = substs bindings t
  return $ annotateExpr a {_eannExpr = et} aet
inferExprType l@ELit {..} = do
  k <- inferTypeKind _litType
  checkTypeKind k
  t <- inferType _litType
  return $ annotateExpr l t
inferExprType s@ESeq {..} = do
  es <- mapM inferExprType _eseq
  ts <- mapM typeOfExpr es
  t <- inferType $ last ts
  return $ annotateExpr s {_eseq = es} t
inferExprType l@ELet {..} = do
  et <- bindPatternVarTypes _eletState _eletPattern _eletExpr
  bt <- inferExprType _eletBody
  t <- typeOfExpr bt >>= inferType
  return $ annotateExpr l {_eletExpr = et, _eletBody = bt} t
inferExprType c@ECase {..} = do
  -- infer case condition expression's type
  ce <- inferExprType _ecaseExpr
  ct <- typeOfExpr ce
  -- infer all case patterns' types
  ts <- forM _ecaseBody $ \c -> underScope $ do
    bindPatternVarTypes False (_casePattern c) _ecaseExpr
    pt <- inferPatternType $ _casePattern c
    e <- inferExprType $ _caseExpr c
    et <- typeOfExpr e
    return (pt, et, c {_caseExpr = e})
  -- check if condition's type match with case exprs' type or not
  sts <- getSpecialTypes (ts ^.. traverse . _2)
  if L.length sts /= 1 then throwError $ "case exprs type conflict: " ++ ppr [(t, _tloc t) | t <- sts]
  else return ()
  -- check if all pattern expressions' type match or not
  forM_ (ts ^.. traverse . _1) $ \e ->
    checkTypeMatch ct e
  -- return case's type
  t <- inferType $ (last sts)
  return $ annotateExpr c {_ecaseExpr = ce, _ecaseBody = ts ^.. traverse . _3} t
inferExprType w@EWhile {..} = do
  -- infer while condition's type
  c <- inferExprType _ewhileCond
  t <- typeOfExpr c >>= inferType
  if aeq t (TPrim Pred _eloc)
    then return ()
    else throwError $ "while expected a bool as condition, but got " ++ ppr t ++ ppr _eloc
  -- infer while's body type
  b <- underScope $ do
    e <- inferExprType _ewhileBody
    t <- typeOfExpr e
    k <- inferTypeKind t
    checkTypeKind k
    return e
  return $ annotateExpr w {_ewhileCond = c, _ewhileBody = b} (TPrim Unit _eloc)
inferExprType h@EHandle {..} = underScope $ do
  if not (isn't _EffList _ehandleEff)
    then throwError $ "expected an eff application, but got " ++ ppr _ehandleEff ++ ppr _eloc
    else return ()
  -- infer handle's effect kind
  ek <- inferEffKind _ehandleEff
  checkEffKind ek
  -- infer handle's expression's type
  scopeE <- inferExprType _ehandleScope
  resT <- typeOfExpr scopeE
  btk <- inferTypeKind resT
  checkTypeKind btk

  let effN = name2String $ if isn't _EffVar _ehandleEff then _ehandleEff ^. effAppName . effVar else _ehandleEff ^. effVar
      prefix = join $ L.intersperse "/" $ (init $ splitOn "/" effN)
  
  if effN == "core/prelude/io" || effN == "core/prelude/python"
    then throwError $ effN ++ " effect cannot be handled"
    else return ()

  bs <- forM _ehandleBindings $ \intf -> underScope $ do
    let fn =
          if prefix == (take (L.length prefix) (intf ^. funcName))
            then (intf ^. funcName)
            else prefix ++ "/" ++ (intf ^. funcName)
        emptyEff = EffList [] _eloc
        unit = TPrim Unit _eloc

    (handleT', intfWithT) <- underScope $ do
      setupEffIntfType intf

      -- get inteface effect type
      handleT <- unbindType $ funcDefType intf
      intfT <- getFuncType (intf ^. funcLoc) fn >>= unbindType

      -- add resume function type
      let resumeT =
            bindTypeEffVar [] $
              bindTypeVar [] $
                TFunc [_tfuncResult intfT] emptyEff resT _eloc
      setEnv (Just resumeT) $ funcs . at "resume"

      -- check if interface defintion match with implemention's or not
      let handleT' = handleT {_tfuncEff = emptyEff, _tfuncResult = unit}
          intfT' = intfT {_tfuncEff = emptyEff, _tfuncResult = unit}
      collectVarBindings intfT' handleT' >>= checkVarBindings

      -- check expression result type
      intfE <- inferExprType $ fromJust $ _funcExpr intf
      intfResT <- typeOfExpr intfE
      checkTypeMatch intfResT resT

      return (handleT', intf {_funcExpr = Just intfE, _funcName = fn})

    -- check scope expr again
    setEnv (Just handleT') $ funcs . at fn
    t <- inferExprType _ehandleScope >>= typeOfExpr
    k <- inferTypeKind t
    checkTypeKind k
    return intfWithT

  t <- inferType resT
  return $ annotateExpr h {_ehandleScope = scopeE, _ehandleBindings = bs} t
inferExprType a@EAnnMeta {..} = inferExprType _eannMetaExpr
inferExprType e = throwError $ "unsupported: " ++ ppr e ++ ppr (_eloc e)

-- | Infer a pattern's type
inferPatternType :: (Has EnvEff sig m) => Pattern -> m Type
inferPatternType PVar {..} = (inferExprType $ EVar (s2n $ name2String _pvar) _ploc) >>= typeOfExpr
inferPatternType PApp {..} = do
  args <- mapM inferPatternType _pappArgs
  mapM_ inferTypeKind _pappTypeArgs
  appFuncType <- inferExprType _pappName >>= typeOfExpr
  appFuncType <- applyTypeArgs appFuncType _pappTypeArgs >>= unbindType
  typeArgs <- mapM inferType _pappTypeArgs
  (t, _) <- inferAppResultType appFuncType typeArgs args
  inferType t
inferPatternType PExpr {..} = inferExprType _pExpr >>= typeOfExpr

-- | Bind a pattern's variables with real types
bindPatternVarTypes :: (Has EnvEff sig m) => Bool -> Pattern -> Expr -> m Expr
bindPatternVarTypes isState p e = do
  eWithType <- inferExprType e
  eType <- typeOfExpr eWithType
  typeBindings <- extracePatternVarTypes p eType
  foldM
    ( \bs (v, t) -> do
        let n = name2String v
        case bs ^. at n of
          Just _ -> throwError $ "pattern rebind a variable: " ++ n ++ ppr (_eloc e)
          Nothing -> do
            setFuncType n t
            -- set localState
            if isState
              then setEnv (Just t) $ localState . at n
              else return ()
            return $ bs & at n ?~ True
    )
    M.empty
    typeBindings
  return eWithType

extracePatternVarTypes :: (Has EnvEff sig m) => Pattern -> Type -> m [(TVar, Type)]
extracePatternVarTypes PVar {..} t = return [(s2n $ name2String _pvar, t)]
extracePatternVarTypes e@PExpr {..} t = do
  et <- inferExprType _pExpr >>= typeOfExpr
  checkTypeMatch et t
  return []
extracePatternVarTypes a@PApp {..} t = underScope $ do
  mapM_ inferTypeKind _pappTypeArgs
  typeArgs <- mapM inferType _pappTypeArgs
  appFuncType <- inferExprType _pappName >>= typeOfExpr
  appFuncType <- applyTypeArgs appFuncType _pappTypeArgs >>= unbindType
  let argTypes = appFuncType ^. tfuncArgs
      appResT = _tfuncResult appFuncType
  bindings <- collectVarBindings appResT t
  foldM
    ( \s e ->
        (++) <$> return s <*> e
    )
    []
    [extracePatternVarTypes arg argt | arg <- _pappArgs | argt <- substs bindings argTypes]

-- | Infer the expression's effect type
inferExprEffType :: (Has EnvEff sig m) => Expr -> m EffectType
inferExprEffType EVar {..} = return $ EffList [] _eloc
inferExprEffType ELit {..} = return $ EffList [] _eloc
inferExprEffType EAnn {..} = inferExprEffType _eannExpr
inferExprEffType EAnnMeta {..} = inferExprEffType _eannMetaExpr
inferExprEffType l@ELam {..} = do
  -- infer arguments
  args <-
    mapM
      ( \(_, t) -> do
          k <- inferTypeKind t
          checkTypeKind k
          inferType t
      )
      _elamArgs
  -- add lambda argument types into env's local scope
  mapM_
    (\(n, t) -> setFuncType n t)
    [(n, t) | (n, _) <- _elamArgs | t <- args]
  forMOf _Nothing _elamExpr $ \_ ->
    throwError $ "expected an expression for lambda" ++ ppr _eloc
  resultEffType <- inferExprEffType $ fromJust _elamExpr
  checkEffTypeMatch _elamEffType resultEffType
  return $ EffList [] _eloc
inferExprEffType ELet {..} = do
  bindPatternVarTypes _eletState _eletPattern _eletExpr
  e0 <- inferExprEffType _eletExpr
  e1 <- inferExprEffType _eletBody
  mergeEffs e0 e1
inferExprEffType ECase {..} = do
  ce <- inferExprEffType _ecaseExpr
  cse <- forM _ecaseBody $ \c -> underScope $ do
    bindPatternVarTypes False (_casePattern c) _ecaseExpr
    inferExprEffType $ _caseExpr c
  --let le : _ = cse
  --forM_ cse $ checkEffTypeMatch le
  foldM mergeEffs ce cse
-- mergeEffs ce le
inferExprEffType EWhile {..} = do
  ce <- inferExprEffType _ewhileCond
  be <- inferExprEffType _ewhileBody
  -- checkEffTypeMatch ce be
  mergeEffs ce be
inferExprEffType EApp {..} = do
  mapM_ inferTypeKind _eappTypeArgs
  appFuncType <- inferExprType _eappFunc >>= typeOfExpr
  inferExprEffType _eappFunc
  appFuncType <- applyTypeArgs appFuncType _eappTypeArgs >>= unbindType
  argTypes <- mapM (\e -> inferExprType e >>= typeOfExpr) _eappArgs
  argKinds <- mapM inferTypeKind argTypes
  mapM_ checkTypeKind argKinds
  mapM_ inferExprEffType _eappArgs
  typeArgs <- mapM inferType _eappTypeArgs
  inferAppResultEffType appFuncType typeArgs argTypes
inferExprEffType ESeq {..} =
  -- merge effects
  foldM
    ( \s e -> do
        et <- inferExprEffType e
        mergeEffs s et
    )
    (EffList [] _eloc)
    _eseq
inferExprEffType EHandle {..} = underScope $ do
  effs <- inferExprEffType _ehandleScope

  -- check intefaces
  effName <-
    if not $ isn't _EffVar _ehandleEff
      then return $ name2String $ _ehandleEff ^. effVar
      else
        if not $ isn't _EffApp _ehandleEff
          then return $ name2String $ _effVar $ _effAppName _ehandleEff
          else throwError $ "expected an eff variable or application, but got " ++ ppr _ehandleEff ++ ppr _eloc
  intfs <- getEnv $ effIntfs . at effName
  let effN = name2String $ _ehandleEff ^. effAppName . effVar
  case intfs of
    Just ifs -> do
      let intfNames = map _funcName _ehandleBindings
      if L.sort ifs == L.sort intfNames
        then return ()
        else throwError $ "eff interfaces mismatch: " ++ ppr ifs ++ " vs " ++ ppr intfNames ++ ppr _eloc
    Nothing -> do
      throwError $ "cannot find effect: " ++ ppr _ehandleEff ++ ppr _eloc
  -- remove the handled effects
  removeEff effs _ehandleEff

-- | Setup for effect inferface type
setupEffIntfType :: (Has EnvEff sig m) => FuncDef -> m ()
setupEffIntfType f = do
  let pos = f ^. funcLoc
      bvars = fmap (\t -> (name2String (t ^. _1), t ^. _2 . non (KStar pos))) $ f ^.. funcBoundVars . traverse
      bevars = fmap (\t -> (name2String t, EKStar pos)) $ f ^. funcBoundEffVars
  forM_ bvars $ \(n, k) -> setEnv (Just k) $ types . at n
  forM_ bevars $ \(n, k) -> setEnv (Just k) $ effs . at n
  mapM_
    (\(n, t) -> setFuncType n t)
    (f ^. funcArgs)
