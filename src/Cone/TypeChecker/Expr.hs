{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}

module Cone.TypeChecker.Expr where

import Cone.Parser.AST
import Cone.TypeChecker.Env
import Cone.TypeChecker.Type
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

-- | Annotate expression with type
annotateExpr :: Expr -> Type -> Expr
annotateExpr e t = EAnn e t (_eloc e)

typeOfExpr :: (Has EnvEff sig m) => Expr -> m Type
typeOfExpr (EAnn _ t _) = return t
typeOfExpr e = throwError $ "expected an annotated expression, but got " ++ ppr e

-- | Infer expression's type
inferExprType :: (Has EnvEff sig m) => Expr -> m Expr
inferExprType e@EVar {..} = do
  t <- getFuncType _eloc _evarName
  return $ annotateExpr e t
inferExprType a@EApp {..} = do
  -- check assign variable
  if _eappFunc ^. evarName == "____assign"
    then do
      if L.length _eappArgs /= 2
        then throwError $ "expected 2 arguments: " ++ ppr a ++ ppr _eloc
        else
          if isn't _EVar $ head _eappArgs
            then throwError $ "cannot assign to an expression: " ++ ppr (head _eappArgs) ++ ppr _eloc
            else -- first argument is the assigned variable which should be in local state
            do
              let vn = (head _eappArgs) ^. evarName
              v <- getEnv $ localState . at vn
              case v of
                Just v -> return ()
                Nothing -> throwError $ "cannot find local variable " ++ vn ++ ppr _eloc
    else return ()
  -- infer all type arguments
  appTypeArgKinds <- mapM inferTypeKind _eappTypeArgs
  mapM_ checkTypeKind appTypeArgKinds
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
  t <- inferAppResultType appFuncType _eappTypeArgs argTypes >>= inferType
  return $ annotateExpr a{_eappFunc=appFunc, _eappArgs=args} t
inferExprType l@ELam {..} = underScope $ do
  -- clear localState, lambda cannot capture local state variables
  setEnv M.empty localState
  -- refresh all bound variables
  (bvs, newLam) <- refresh _elamBoundVars l
  (evs, newLam) <- refreshEffVar _elamBoundEffVars newLam
  case newLam of
    l@ELam {..} -> do
      -- add all bound type variables into env
      mapM_ (\t -> setEnv (Just $ KStar _eloc) $ types . at (name2String t)) bvs
      -- add all bound eff type variables into env
      mapM_ (\t -> setEnv (Just $ EKStar _eloc) $ effs . at (name2String t)) evs
      -- infer arguments
      args <-
        mapM
          ( \(_, t) -> do
              k <- inferTypeKind t
              checkTypeKind k
              return t
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
      t <- inferType $ bindTypeEffVar evs $ bindType bvs $ TFunc args _elamEffType eType _eloc
      return $ annotateExpr l{_elamExpr=Just lamE} t
    _ -> throwError $ "should not be here"
inferExprType a@EAnn {..} = do
  et <- inferExprType _eannExpr
  t <- typeOfExpr et
  k <- inferTypeKind _eannType
  checkTypeKind k
  checkTypeMatch t _eannType
  t <- inferType _eannType
  return $ annotateExpr a{_eannExpr=et} t
inferExprType l@ELit {..} = do
  k <- inferTypeKind _litType
  checkTypeKind k
  t <- inferType _litType
  return $ annotateExpr l t
inferExprType s@ESeq {..} = do
  es <- mapM inferExprType _eseq
  ts <- mapM typeOfExpr es
  t <- inferType $ last ts
  return $ annotateExpr s{_eseq=es} t
inferExprType l@ELet {..} = do
  et <- bindPatternVarTypes _eletState _eletPattern _eletExpr
  t <- typeOfExpr et >>= inferType
  return $ annotateExpr l{_eletExpr=et} t
inferExprType c@ECase {..} = do
  -- infer case condition expression's type
  ce <- inferExprType _ecaseExpr 
  ct <- typeOfExpr ce
  -- infer all case patterns' types
  ts <- forM _ecaseBody $ \c -> underScope $ do
    bindPatternVarTypes False (c ^. casePattern) _ecaseExpr
    pt <- inferPatternType $ c ^. casePattern
    e <- inferExprType $ c ^. caseExpr
    et <- typeOfExpr e
    return (pt, et, c{_caseExpr=e})
  let t : rest = ts
  -- check if condition's type match with case exprs' type or not
  forM_ (rest ^.. traverse . _2) $ \et ->
    checkTypeMatch et (t ^. _2)
  -- check if all pattern expressions' type match or not
  forM_ (ts ^.. traverse . _1) $ \e ->
    checkTypeMatch ct e
  -- return case's type
  t <- inferType $ (last ts) ^. _2
  return $ annotateExpr c{_ecaseExpr=ce, _ecaseBody=ts ^..traverse._3} t
inferExprType w@EWhile {..} = do
  -- infer while condition's type
  c <- inferExprType _ewhileCond 
  t <- typeOfExpr c
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
  return $ annotateExpr w{_ewhileCond=c, _ewhileBody=b} (TPrim Unit _eloc)
inferExprType h@EHandle {..} = underScope $ do
  -- infer handle's effect kind
  ek <- inferEffKind _ehandleEff
  checkEffKind ek
  -- infer handle's expression's type
  scopeE <- inferExprType _ehandleScope 
  resT <- typeOfExpr scopeE
  btk <- inferTypeKind resT
  checkTypeKind btk
  bs <- forM _ehandleBindings $ \intf -> underScope $ do
    let fn = (intf ^. funcName)
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
              bindType [] $
                TFunc [_tfuncResult intfT] emptyEff resT _eloc
      setEnv (Just resumeT) $ funcs . at "resume"

      -- check if interface defintion match with implemention's or not
      let handleT' = handleT {_tfuncEff = emptyEff, _tfuncResult = unit}
          intfT' = intfT {_tfuncEff = emptyEff, _tfuncResult = unit}
      binds <- collectVarBindings intfT' handleT'
      checkVarBindings binds

      -- check expression result type
      intfE <- inferExprType $ fromJust $ _funcExpr intf
      intfResT <- typeOfExpr intfE
      checkTypeMatch intfResT resT

      return (handleT', intf{_funcExpr=Just intfE})

    -- check scope expr again
    setEnv (Just handleT') $ funcs . at fn
    t <- inferExprType _ehandleScope >>= typeOfExpr
    k <- inferTypeKind t
    checkTypeKind k
    return intfWithT

  t <- inferType resT
  return $ annotateExpr h{_ehandleScope=scopeE, _ehandleBindings=bs} t
inferExprType etc@(ETC e@TCApp {..} _) = do
  let v : e : [] = _tcAppArgs
  if _tcAppName /= "=" && _tcAppName /= "+="
    && _tcAppName /= "-="
    && _tcAppName /= "*="
    && _tcAppName /= "/="
    && _tcAppName /= "%="
    then throwError $ "unsupported tc assign operator " ++ _tcAppName ++ ppr _tcloc
    else do 
      t <- inferTCExprType v e >>= inferType
      return $ annotateExpr etc t
inferExprType e = throwError $ "unsupported: " ++ ppr e ++ ppr (_eloc e)

-- | Collect the tensor informations
collectTCExprTypeInfo :: (Has EnvEff sig m) => TCExpr -> m (Type, [(String, Type)])
collectTCExprTypeInfo TCAccess {..} = do
  v <- getFuncType _tcloc _tcVarName
  (t, shape) <- extractTensorInfo v
  if L.length _tcIndices /= L.length shape
    then
      throwError $
        "type shape rank mismatch: " ++ ppr shape
          ++ " vs "
          ++ ppr _tcIndices
          ++ ppr _tcloc
    else return (t, [(name2String n, d) | n <- _tcIndices | d <- shape])
collectTCExprTypeInfo TCApp {..} = do
  args' <- mapM collectTCExprTypeInfo _tcAppArgs
  let arg : args = args'
  case _tcAppName of
    an
      | an == "+"
          || an == "-"
          || an == "*"
          || an == "/"
          || an == "%" ->
        foldM
          ( \(t, is) (et, eis) -> do
              k0 <- inferTypeKind t
              checkTypeKind k0
              k1 <- inferTypeKind et
              checkTypeKind k1
              if aeq t et
                then return (et, is ++ eis)
                else throwError $ "+ expected same types, but got " ++ ppr t ++ " vs " ++ ppr et ++ ppr _tcloc
          )
          arg
          args
    _ -> throwError $ "unsupported tc function: " ++ _tcAppName ++ ppr _tcloc
collectTCExprTypeInfo TCVar {..} = do
  t <- getFuncType _tcloc _tcVarName
  return (t, [])

-- | Infer a tensor comprehensive expression's type
inferTCExprType :: (Has EnvEff sig m) => TCExpr -> TCExpr -> m Type
inferTCExprType a@TCAccess {..} e = do
  info <- collectTCExprTypeInfo e
  let (t, indices) = info
  dims <-
    foldM
      ( \s (n, t) -> do
          case s ^. at n of
            Just ot ->
              if aeq ot t
                then return $ s & at n ?~ t
                else throwError $ "dim size conflict for " ++ n ++ " : " ++ ppr ot ++ ppr (_tloc ot) ++ " vs " ++ ppr t ++ ppr (_tloc t)
            Nothing -> return $ s & at n ?~ t
      )
      M.empty
      indices
  shape <-
    foldM
      ( \s i -> do
          case dims ^. at (name2String i) of
            Just t -> return $ s ++ [t]
            Nothing -> throwError $ "cannot index var: " ++ ppr i ++ ppr _tcloc
      )
      []
      _tcIndices
  tt <- toTensorType t shape
  setFuncType _tcVarName tt
  return tt
inferTCExprType t0 t1 = throwError $ "unsupported tc expr: " ++ ppr t0 ++ " and " ++ ppr t1 ++ ppr (_tcloc t0)

-- | Infer a pattern's type
inferPatternType :: (Has EnvEff sig m) => Pattern -> m Type
inferPatternType PVar {..} = (inferExprType $ EVar _pvar _ploc) >>= typeOfExpr
inferPatternType PApp {..} = do
  args <- mapM inferPatternType _pappArgs
  appTypeArgKinds <- mapM inferTypeKind _pappTypeArgs
  mapM_ checkTypeKind appTypeArgKinds
  appFuncType <- inferExprType (EVar _pappName _ploc) >>= typeOfExpr
  appFuncType <- applyTypeArgs appFuncType _pappTypeArgs >>= unbindType
  inferAppResultType appFuncType _pappTypeArgs args
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
extracePatternVarTypes PVar {..} t = return [(s2n _pvar, t)]
extracePatternVarTypes PExpr {..} t = return []
extracePatternVarTypes a@PApp {..} t = underScope $ do
  appTypeArgKinds <- mapM inferTypeKind _pappTypeArgs
  mapM_ checkTypeKind appTypeArgKinds
  appFuncType <- inferExprType (EVar _pappName _ploc) >>= typeOfExpr
  appFuncType <- applyTypeArgs appFuncType _pappTypeArgs >>= unbindType
  let cntr =
        ( \arg ->
            -- construct a type with type variables
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
                  t@TPrim{..} -> return t
                  _ -> newTVar
        )
  argTypes <- mapM cntr (appFuncType ^. tfuncArgs)
  appResT <- inferAppResultType appFuncType _pappTypeArgs argTypes
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
inferExprEffType l@ELam {..} = do
  forMOf _Nothing _elamExpr $ \_ ->
    throwError $ "expected an expression for lambda" ++ ppr _eloc
  resultEffType <- inferExprEffType $ fromJust _elamExpr
  checkEffTypeMatch _elamEffType resultEffType
  return $ EffList [] _eloc
inferExprEffType ELet {..} = do
  bindPatternVarTypes _eletState _eletPattern _eletExpr
  inferExprEffType _eletExpr
inferExprEffType ECase {..} = do
  ce <- inferExprEffType _ecaseExpr
  cse <- forM _ecaseBody $ \c -> underScope $ do
    bindPatternVarTypes False (c ^. casePattern) _ecaseExpr
    inferExprEffType $ c ^. caseExpr
  let le : _ = cse
  forM_ cse $ checkEffTypeMatch le
  mergeEffs ce le
inferExprEffType EWhile {..} = do
  ce <- inferExprEffType _ewhileCond
  be <- inferExprEffType _ewhileBody
  -- checkEffTypeMatch ce be
  mergeEffs ce be
inferExprEffType EApp {..} = do
  appTypeArgKinds <- mapM inferTypeKind _eappTypeArgs
  mapM_ checkTypeKind appTypeArgKinds
  appFuncType <- inferExprType _eappFunc >>= typeOfExpr
  inferExprEffType _eappFunc
  appFuncType <- applyTypeArgs appFuncType _eappTypeArgs >>= unbindType
  argTypes <- mapM (\e -> inferExprType e >>= typeOfExpr) _eappArgs
  argKinds <- mapM inferTypeKind argTypes
  mapM_ checkTypeKind argKinds
  mapM_ inferExprEffType _eappArgs
  inferAppResultEffType appFuncType _eappTypeArgs argTypes
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
          then return $ _ehandleEff ^. effAppName
          else throwError $ "expected an eff variable or application, but got " ++ ppr _ehandleEff ++ ppr _eloc
  intfs <- getEnv $ effIntfs . at effName
  case intfs of
    Just ifs -> do
      let intfNames = map (\e -> e ^. funcName) _ehandleBindings
      if L.sort ifs == L.sort intfNames
        then return ()
        else throwError $ "eff interfaces mismatch: " ++ ppr ifs ++ " vs " ++ ppr intfNames ++ ppr _eloc
    Nothing -> do
      throwError $ "cannot find effect: " ++ ppr _ehandleEff ++ ppr _eloc
  -- remove the handled effects
  removeEff effs _ehandleEff
inferExprEffType ETC {..} = return $ EffList [] _eloc

-- | Setup for effect inferface type
setupEffIntfType :: (Has EnvEff sig m) => FuncDef -> m ()
setupEffIntfType f = do
  let pos = f ^. funcLoc
      bvars = fmap (\t -> (name2String t, KStar pos)) $ f ^. funcBoundVars
      bevars = fmap (\t -> (name2String t, EKStar pos)) $ f ^. funcBoundEffVars
  forM_ bvars $ \(n, k) -> setEnv (Just k) $ types . at n
  forM_ bevars $ \(n, k) -> setEnv (Just k) $ effs . at n
  mapM_
    (\(n, t) -> setFuncType n t)
    (f ^. funcArgs)

selectFuncImpl :: (Has EnvEff sig m) => Expr -> m Expr
selectFuncImpl e = transformM selectImpl e
  where selectImpl e@(EApp (EAnn (EVar fn _) t _) targs args loc) = do
          impls <- getEnv funcImpls
          case impls ^. at fn of
            Nothing -> return e
            Just is -> do
              case is ^. at t of
                Just l -> return $ EApp l targs args loc
                Nothing -> return e
        selectImpl e = return e

selectFuncImpls :: (Has EnvEff sig m) => Module -> m Module
selectFuncImpls m =
  transformMOn (topStmts . traverse . _FDef . funcExpr . _Just) selectFuncImpl m
  >>= transformMOn (topStmts . traverse . _ImplFDef . implFunDef . funcExpr . _Just) selectFuncImpl