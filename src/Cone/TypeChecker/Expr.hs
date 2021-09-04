{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Cone.TypeChecker.Expr where

import Cone.Parser.AST
import Cone.TypeChecker.Env
import Cone.TypeChecker.Type
import Control.Carrier.Error.Either
import Control.Carrier.Fresh.Strict
import Control.Carrier.State.Strict
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Effect.Sum
import Control.Lens
import Control.Lens.Plated
import Control.Monad
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe

checkFuncType :: (Has EnvEff sig m) => FuncDef -> m ()
checkFuncType f = underScope $ do
  let pos = f ^. funcLoc
      bvars = fmap (\t -> (name2String t, KStar pos)) $ f ^. funcBoundVars
  forM_ bvars $ \(n, k) -> setEnv (Just k) $ types . at n
  mapM_
    (\(n, t) -> setFuncType n t)
    (f ^. funcArgs)
  case f ^. funcExpr of
    Just e -> do
      eType <- inferExprType e
      resultType <- inferType $ f ^. funcResultType
      checkTypeMatch eType resultType
      effType <- inferExprEffType e
      let fEff = case f ^. funcEffectType of
              Just et -> et
              Nothing -> EffTotal pos
      checkEffTypeMatch effType fEff
    Nothing -> return ()

checkFuncDef :: (Has EnvEff sig m) => FuncDef -> m ()
checkFuncDef f = underScope $ do
  let pos = f ^. funcLoc
      ft = funcDefType f
  k <- inferTypeKind ft
  checkTypeKind k
  checkFuncType f

inferExprType :: (Has EnvEff sig m) => Expr -> m Type
inferExprType EVar {..} = do
  getFuncType _evarName
inferExprType a@EApp {..} = do
  -- check assign variable
  if _eappFunc ^.evarName == "____assign"
  then do
    if L.length _eappArgs /= 2
    then throwError $ "expected 2 arguments: " ++ ppr a
    else if isn't _EVar $ head _eappArgs
         then throwError $ "cannot assign to an expression: " ++ ppr (head _eappArgs)
         else do let vn = (head _eappArgs) ^.evarName
                 v <- getEnv $ localState . at vn
                 case v of
                  Just v -> return ()
                  Nothing -> throwError $ "cannot find local variable " ++ vn
  else return ()
  --
  appTypeArgKinds <- mapM inferTypeKind _eappTypeArgs
  mapM_ checkTypeKind appTypeArgKinds
  appFuncType <- inferExprType _eappFunc
  appFuncType <- applyTypeArgs appFuncType _eappTypeArgs >>= unbindType
  argTypes <- mapM inferExprType _eappArgs
  argKinds <- mapM inferTypeKind argTypes
  mapM_ checkTypeKind argKinds
  inferAppResultType appFuncType _eappTypeArgs argTypes >>= inferType
inferExprType l@ELam {..} = underScope $ do
  -- clear localState, lambda cannot capture local state variables
  setEnv M.empty localState
  -- refresh
  (bvs, newLam) <- refresh _elamBoundVars l
  case newLam of
    l@ELam{..} -> do
      mapM_ (\t -> setEnv (Just $ KStar _eloc) $ types . at (name2String t)) bvs
      args <-
        mapM
          ( \(_, t) -> do
              k <- inferTypeKind t
              checkTypeKind k
              return t
          )
          _elamArgs
      eff <- case _elamEffType of
        Just e -> do
          inferEffKind e
          return e
        Nothing -> return $ EffTotal _eloc
      mapM_
        (\(n, t) -> setFuncType n t)
        [(n, t) | (n, _) <- _elamArgs | t <- args]
      case _elamExpr of
        Just e -> return ()
        Nothing -> throwError $ "expected an expression for lambda" ++ ppr _eloc
      eType <- inferExprType $ fromJust _elamExpr
      k <- inferTypeKind _elamResultType
      checkTypeKind k
      checkTypeMatch eType _elamResultType
      inferType $ bindType bvs $ TFunc args (Just eff) eType _eloc
    _ -> throwError $ "should not be here"
inferExprType a@EAnn {..} = do
  t <- inferExprType _eannExpr
  k <- inferTypeKind _eannType
  checkTypeKind k
  checkTypeMatch t _eannType
  inferType _eannType
inferExprType ELit {..} = do
  k <- inferTypeKind _litType
  checkTypeKind k
  inferType _litType
inferExprType ESeq {..} = do
  ts <- mapM inferExprType _eseq
  inferType $ last ts
inferExprType ELet {..} =
  bindPatternVarTypes _eletState _eletPattern _eletExpr >>= inferType
inferExprType ECase {..} = do
  ct <- inferExprType _ecaseExpr
  ts <- forM _ecaseBody $ \c -> underScope $ do
    bindPatternVarTypes False (c ^. casePattern) _ecaseExpr
    pt <- inferPatternType $ c ^. casePattern
    et <- inferExprType $ c ^. caseExpr
    return (pt, et)
  let t : rest = ts
  forM_ (rest ^.. traverse . _2) $ \_ ->
    checkTypeMatch ct (t ^. _1)
  forM_ (ts ^.. traverse . _1) $ \e ->
    checkTypeMatch ct e
  inferType $ (last ts) ^. _2
inferExprType EWhile {..} = do
  t <- inferExprType _ewhileCond
  if aeq t (TPrim Pred _eloc)
    then return t
    else throwError $ "while expected a bool as condition, but got " ++ ppr t ++ ppr _eloc
  underScope $ do
    t <- inferExprType _ewhileBody
    k <- inferTypeKind t
    checkTypeKind k
  return $ TPrim Unit _eloc
inferExprType EHandle {..} = do
  ek <- inferEffKind _ehandleEff
  checkEffKind ek
  bodyType <- inferExprType _ehandleScope
  btk <- inferTypeKind bodyType
  checkTypeKind btk
  underScope $ forM_ _ehandleBindings checkFuncDef
  inferType bodyType
inferExprType (ETC e@TCApp{..} _) = do
  let v:e:[] = _tcAppArgs
  if _tcAppName /= "=" && _tcAppName /= "+=" &&
     _tcAppName /= "-=" && _tcAppName /= "*=" &&
     _tcAppName /= "/=" && _tcAppName /= "%="
  then throwError $ "unsupported tc assign operator " ++ _tcAppName ++ ppr _tcloc
  else inferTCExprType v e >>= inferType
inferExprType e = throwError $ "unsupported: " ++ ppr e ++ ppr (_eloc e)

collectTCExprTypeInfo :: (Has EnvEff sig m) => TCExpr -> m (Type, [(String, Type)])
collectTCExprTypeInfo TCAccess{..} = do
  v <- getFuncType _tcVarName
  (t, shape) <- extractTensorInfo v
  if L.length _tcIndices /= L.length shape
  then throwError $ "type shape rank mismatch: " ++ ppr shape ++
            " vs " ++ ppr _tcIndices ++ ppr _tcloc
  else return (t, [(name2String n, d) | n <- _tcIndices | d <- shape])
collectTCExprTypeInfo TCApp{..} = do
  args' <- mapM collectTCExprTypeInfo _tcAppArgs
  let arg:args = args'
  case _tcAppName of
    an | an == "+" ||
         an == "-" ||
         an == "*" ||
         an == "/" ||
         an == "%" -> foldM (\(t, is) (et, eis) -> do
                     k0 <- inferTypeKind t
                     checkTypeKind k0
                     k1 <- inferTypeKind et
                     checkTypeKind k1
                     if aeq t et then return (et, is ++ eis)
                     else throwError $ "+ expected same types, but got " ++ ppr t ++ " vs " ++ ppr et) arg args
    _ -> throwError $ "unsupported tc function: " ++ _tcAppName ++ ppr _tcloc
collectTCExprTypeInfo TCVar{..} = do
  t <- getFuncType _tcVarName
  return (t, [])

inferTCExprType :: (Has EnvEff sig m) => TCExpr -> TCExpr -> m Type
inferTCExprType a@TCAccess{..} e = do
  info <- collectTCExprTypeInfo e
  let (t, indices) = info
  dims <- foldM (\s (n, t) -> do
    case s ^. at n of
      Just ot -> 
        if aeq ot t then return $ s & at n ?~ t
        else throwError $ "dim size conflict for " ++ n ++ " : " ++ ppr ot ++ ppr (_tloc ot) ++ " vs " ++ ppr t ++ ppr (_tloc t)
      Nothing -> return $ s & at n ?~ t
    ) M.empty indices
  shape <- foldM (\s i -> do
                case dims ^. at (name2String i) of
                  Just t -> return $ s++[t]
                  Nothing -> throwError $ "cannot index var: " ++ ppr i) [] _tcIndices
  tt <- toTensorType t shape
  setFuncType _tcVarName tt
  return tt
inferTCExprType t0 t1 = throwError $ "unsupported tc expr: " ++ ppr t0 ++ " and " ++ ppr t1 ++ ppr (_tcloc t0)

inferPatternType :: (Has EnvEff sig m) => Pattern -> m Type
inferPatternType PVar {..} = inferExprType $ EVar _pvar _ploc
inferPatternType PApp {..} = do
  args <- mapM inferPatternType _pappArgs
  appTypeArgKinds <- mapM inferTypeKind _pappTypeArgs
  mapM_ checkTypeKind appTypeArgKinds
  appFuncType <- inferExprType (EVar _pappName _ploc) 
  appFuncType <- applyTypeArgs appFuncType _pappTypeArgs >>= unbindType
  inferAppResultType appFuncType _pappTypeArgs args
inferPatternType PExpr {..} = inferExprType _pExpr

bindPatternVarTypes :: (Has EnvEff sig m) => Bool -> Pattern -> Expr -> m Type
bindPatternVarTypes isState p e = do
  eType <- inferExprType e
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
  return eType

extracePatternVarTypes :: (Has EnvEff sig m) => Pattern -> Type -> m [(TVar, Type)]
extracePatternVarTypes PVar {..} t = return [(s2n _pvar, t)]
extracePatternVarTypes PExpr {..} t = return []
extracePatternVarTypes a@PApp {..} t = underScope $ do
  appTypeArgKinds <- mapM inferTypeKind _pappTypeArgs
  mapM_ checkTypeKind appTypeArgKinds
  appFuncType <- inferExprType (EVar _pappName _ploc) 
  appFuncType <- applyTypeArgs appFuncType _pappTypeArgs >>= unbindType
  let cntr =
        ( \arg ->
            let newTVar = do
                  fvn <- fresh
                  let vn = name2String $ freeVarName fvn
                      t = TVar (s2n vn) _ploc
                  setFuncType vn t
                  return t
             in case arg of
                  TVar {..} -> do
                    gt <- getEnv $ types . at (name2String _tvar)
                    case gt of
                      Just _ -> return arg
                      Nothing -> newTVar
                  tp@TApp {..} -> do
                    as <- mapM cntr _tappArgs
                    return $ tp {_tappArgs = as}
                  _ -> newTVar
        )
  argTypes <- mapM cntr (appFuncType ^. tfuncArgs)
  appT <- inferAppResultType appFuncType _pappTypeArgs argTypes
  bindings <- collectVarBindings appT t
  foldM
    ( \s e ->
        (++) <$> return s <*> e
    )
    []
    [extracePatternVarTypes arg argt | arg <- _pappArgs | argt <- substs bindings argTypes]

inferExprEffType :: (Has EnvEff sig m) => Expr -> m EffectType
inferExprEffType EVar {..} = return $ EffTotal _eloc
inferExprEffType ELit {..} = return $ EffTotal _eloc
inferExprEffType EAnn {..} = inferExprEffType _eannExpr
inferExprEffType l@ELam {..} = do
  let et = case _elamEffType of
        Just et -> et
        Nothing -> EffTotal _eloc
  forMOf _Nothing _elamExpr $ \_ ->
    throwError $ "expected an expression for lambda" ++ ppr _eloc
  resultEffType <- inferExprEffType $ fromJust _elamExpr
  checkEffTypeMatch et resultEffType
  return $ EffTotal _eloc
inferExprEffType ELet {..} = inferExprEffType _eletExpr
inferExprEffType ECase {..} = do
  ce <- inferExprEffType _ecaseExpr
  cse <- mapM inferExprEffType $ _ecaseBody ^.. traverse . caseExpr
  let le : _ = cse
  forM_ cse $ checkEffTypeMatch le
  mergeEffs ce le
inferExprEffType EWhile {..} = do
  ce <- inferExprEffType _ewhileCond
  be <- inferExprEffType _ewhileBody
  checkEffTypeMatch ce be
  mergeEffs ce be
inferExprEffType EApp {..} = do
  appTypeArgKinds <- mapM inferTypeKind _eappTypeArgs
  mapM_ checkTypeKind appTypeArgKinds
  appFuncType <- inferExprType _eappFunc
  appFuncType <- applyTypeArgs appFuncType _eappTypeArgs >>= unbindType
  argTypes <- mapM inferExprType _eappArgs
  argKinds <- mapM inferTypeKind argTypes
  mapM_ checkTypeKind argKinds
  inferAppResultEffType appFuncType _eappTypeArgs argTypes
inferExprEffType ESeq {..} =
  foldM
    ( \s e -> do
        et <- inferExprEffType e
        mergeEffs s et
    )
    (EffTotal $ _eloc)
    _eseq
inferExprEffType EHandle {..} = underScope $ do
  et <- inferExprEffType _ehandleScope
  forM_ _ehandleBindings $ \intf -> do
    let fn = (intf ^. funcName)
    checkFuncDef intf
    ft <- unbindType $ funcDefType intf
    intfT <- getFuncType fn >>= unbindType
    binds <- collectVarBindings intfT ft
    checkVarBindings binds
    eff <- case ft of
      ft@TFunc {..} -> case _tfuncEff of
        Just et -> return et
        Nothing -> return $ EffTotal _eloc
      t -> throwError $ "expected a function type, but got " ++ ppr t ++ ppr _eloc
    intfEff <- (case intfT of
                 ft@TFunc {..} -> case _tfuncEff of
                   Just et -> return et
                   Nothing -> return $ EffTotal _eloc
                 t -> throwError $ "expected a function type, but got " ++ ppr t ++ ppr _eloc)
                 >>= mergeEffs (EffTotal _eloc)
    effs <- mergeEffs eff _ehandleEff >>= mergeEffs (EffTotal _eloc)
    checkEffTypeMatch et effs
    --if aeq (closeEffType effs) (closeEffType intfEff)
    --  then return ()
    --  else throwError $ "eff type mismatch: " ++ ppr effs ++ " vs " ++ ppr intfEff ++ ppr _eloc
    let (bts, ft) = unbindTypeSimple $ funcDefType intf
    setEnv (Just $ bindType bts $ ft {_tfuncEff = Just effs}) $ funcs . at fn
  -- et <- inferExprEffType _ehandleScope
  -- check intefaces
  effName <- if not $ isn't _EffApp _ehandleEff then return $ _ehandleEff ^.effAppName
             else if not $ isn't _EffVar _ehandleEff then return $ name2String $ _ehandleEff ^.effVarName
                  else throwError $ "expected an eff variable or application, but got " ++ ppr _ehandleEff ++ ppr _eloc
  intfs <- getEnv $ effIntfs . at effName
  case intfs of
    Just is -> do let intfNames = map (\e -> e ^.funcName) _ehandleBindings 
                  if L.sort is == L.sort intfNames then return ()
                  else throwError $ "eff interfaces mismatch: " ++ ppr is ++ " vs " ++ ppr intfNames
    Nothing -> do
      throwError $ "cannot find effect: " ++ ppr _ehandleEff ++ ppr _eloc
  removeEff et _ehandleEff
inferExprEffType ETC{..} = return $ EffTotal _eloc
