{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Cone.TypeChecker.Expr where

import Cone.Parser.AST
import Cone.Env
import Cone.TypeChecker.Type
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Lens
import Control.Lens.Plated
import Control.Monad
import qualified Data.List as L
import Data.List.Split
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace
import GHC.Real
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe

-- | Annotate expression with type
annotateExpr :: Expr -> Type -> EffectType -> Expr
annotateExpr e t eff = EAnnMeta e t eff (_eloc e)

-- | Return the type in annotation meta
typeOfExpr :: (Has EnvEff sig m) => Expr -> m Type
typeOfExpr (EAnnMeta _ t _ _) = return t
typeOfExpr e = throwError $ "expected an annotated expression, but got " ++ ppr e

-- | Return the effect type in annotation meta
effTypeOfExpr :: (Has EnvEff sig m) => Expr -> m EffectType
effTypeOfExpr (EAnnMeta _ _ eff _) = return eff
effTypeOfExpr e = throwError $ "expected an annotated expression, but got " ++ ppr e

-- | Check a function type
checkFuncType :: (Has EnvEff sig m) => FuncDef -> m FuncDef
checkFuncType f = underScope $ do
  globalTypes <- fmap s2n . M.keys <$> getEnv typeKinds
  globalEffTypes <- fmap s2n . M.keys <$> getEnv effKinds
  let pos = f ^. funcLoc
      star = KStar pos
      btvars = fmap (\t -> (name2String (t ^. _1), t ^. _2 . non star)) $ f ^. funcBoundVars
      bevars = fmap (\t -> (name2String t, EKStar pos)) $ f ^. funcBoundEffVars
      bt = bind (globalTypes::[TVar]) (bindFDef f)
      be = bind (globalEffTypes::[EffVar]) (bindFDef f)
      ftvars = (bt ^.. fv) :: [TVar]
      fevars = (be ^.. fv) :: [EffVar]
  -- check if has free type variables
  when (ftvars /= []) $
    throwError $
      "function type variables should "
        ++ "only exists in function type arguments: "
        ++ ppr ftvars ++ ppr (_funcLoc f)
  when (fevars /= []) $
    throwError $
      "function eff type variables should "
        ++ "only exists in function eff type arguments: "
        ++ ppr fevars ++ ppr (_funcLoc f)
  -- add all bound type variables into env
  forM_ btvars $ \(n, k) -> setEnv (Just k) $ typeKinds . at n
  -- add all bound eff type variables into env
  forM_ bevars $ \(n, k) -> setEnv (Just k) $ effKinds . at n
  -- add function type into env
  mapM_
    (uncurry setFuncType)
    (f ^. funcArgs)
  case _funcExpr f of
    Just e -> do
      -- infer function expression type
      eWithType <- inferExprType e
      eType <- typeOfExpr eWithType
      effType <- effTypeOfExpr eWithType
      resultType <- inferType $ _funcResultType f
      checkTypeMatch eType resultType
      let fEff = _funcEffectType f
      restEffs <- removeEff effType fEff
      -- check if all effects are handled or not
      if aeq restEffs (EffList [] pos)
        then return f {_funcExpr = Just eWithType}
        else throwError $ "func result effs mismatch: " ++ ppr effType ++ " vs " ++ ppr fEff ++ ppr pos
    Nothing -> return f

-- | Check a function definiton
checkFuncDef :: (Has EnvEff sig m) => FuncDef -> m FuncDef
checkFuncDef f = underScope $ do
  setEnv M.empty typeBinds
  setEnv M.empty kindBinds
  setEnv M.empty effTypeBinds
  setEnv M.empty effKindBinds
  let pos = f ^. funcLoc
      ft = funcDefType f
  k <- inferTypeKind ft
  checkTypeKind k
  checkFuncType f

getSpecializedFunc :: (Has EnvEff sig m) => [Type] -> String -> Type -> m String
getSpecializedFunc targs fn t = do
  if isConcreteType t then do
    mn <- getEnv currentModuleName
    let fSel = mn ++ "/" ++ last (splitOn "/" $ uniqueFuncImplName fn t)
    f <- getEnv $ specializedFuncs . at fSel
    case f of
      Nothing -> do
        fdef <- getEnv $ funcDefs . at fn
        case fdef of
          Just fdef -> do
            if isn't _Nothing (_funcExpr fdef) && not (null (_funcBoundVars fdef) && null (_funcBoundEffVars fdef))
            then underScope $ do
              fdef <- applyTArgs fdef
              bs <- foldM (\s (v, _) -> do
                  vn <- freeVarName <$> fresh
                  return $ s ++ [(v, TVar vn (_tloc t))]) [] (_funcBoundVars fdef)
              effBs <- foldM (\s v -> do
                  vn <- freeEffVarName <$> fresh
                  return $ s ++ [(v, EffVar vn (_tloc t))]) [] (_funcBoundEffVars fdef)
              let newFdef = (substs effBs $ substs bs fdef){_funcBoundVars=[], _funcBoundEffVars=[]}
                  ft = funcDefType newFdef
              gt <- unbindType ft >>= inferType
              ut <- unbindType t
              binds <- collectVarBindings False gt ut
              checkAndAddTypeVarBindings binds
              bindEffs <- collectEffVarBindings False (_tfuncEff gt) (_tfuncEff ut)
              checkAndAddEffVarBindings bindEffs
              let newF = (substs bindEffs $ substs binds newFdef){_funcName = fSel}
                  newT = bindTypeEffVar (_funcBoundEffVars newF) $ bindTypeVar (_funcBoundVars newF) ut
              setEnv (Just newT) $ funcTypes . at fSel
              setEnv (Just newT) $ specializedFuncTypes . at fSel
              setEnv (Just newF) $ specializedFuncs . at fSel
              newF <- checkFuncDef newF
              setEnv (Just newF) $ specializedFuncs . at fSel
              return fSel
            else return fn
          Nothing -> return fn
      Just _ -> return fSel
    else return fn
  where
    applyTArgs fdef = do
      let argsLen = L.length targs
          bts = _funcBoundVars fdef
          binds = [(n ^. _1, t) | n <- L.take argsLen bts | t <- targs]
          ts = [(n ^. _2 . non (KStar (_tloc t)), t) | n <- L.take argsLen bts | t <- targs]
      forM_ ts $ \(k, t) -> do
        tk <- inferTypeKind t
        checkKindMatch k tk
      return $ substs binds fdef {_funcBoundVars = L.drop argsLen bts}

-- | Select a function implementation based on type
selectFuncImpl :: (Has EnvEff sig m) => [Type] -> Expr -> Location -> m Expr
selectFuncImpl targs e@(EAnnMeta (EVar fn' _) t eff _) loc = do
  let fn = name2String fn'
  impls <- getFuncImpls fn
  impls <- findSuperImpls impls >>= findBestImpls
  newFn <- if L.length impls == 1
    then return $ name2String $ _evarName $ head impls ^. _1 -- return $ EAnnMeta (head impls ^. _1) t loc
    else
      if L.length impls > 1
        then throwError $ "ambiguous implementations for " ++ fn ++ ppr impls ++ ppr loc
        else return fn
  f <- getEnv $ funcDefs . at newFn
  when (fn /= "resume" &&
        fn /= "data/tensor/full" && -- TODO should be removed
        fn /= "core/prelude/inline_python" &&
        fn /= "core/prelude/____assign" &&
        fn /= "core/prelude/____zeros" &&
        isConcreteType t && isn't _Nothing f && isn't _Just (_funcExpr $ fromJust f)) $
    throwError $ "cannot find function implemenation for " ++ fn ++ " of type " ++ ppr t ++ ppr loc
  newFn <- getSpecializedFunc targs newFn t
  return $ EAnnMeta (EVar (s2n newFn) loc) t eff loc
  where
    findSuperImpls impls =
      foldM
        ( \f (e, it) -> do
            is <- isEqOrSubType t it
            if is
              then return $ f ++ [(e, it)]
              else return f
        )
        []
        impls
    findBestImpls impls' = do
      let impls = L.nubBy aeq impls'
      indegrees <-
        foldM
          ( \s (a, b) -> do
              is <- isSubType (a ^. _2) (b ^. _2)
              if is
                then return $ s & at b ?~ (1 + fromJust (s ^. at b))
                else do
                  is <- isSubType (b ^. _2) (a ^. _2)
                  if is
                    then return $ s & at a ?~ (1 + fromJust (s ^. at a))
                    else return s
          )
          (L.foldl' (\s e -> s & at e ?~ (0 :: Int)) M.empty impls)
          [(a, b) | a <- impls, b <- impls]
      foldM
        ( \s (i, c) ->
            if c == 0
              then return $ s ++ [i]
              else return s
        )
        []
        (M.toList indegrees)
selectFuncImpl _ e _ = return e

-- | Infer expression's type
inferExprType :: (Has EnvEff sig m) => Expr -> m Expr
inferExprType e@EVar {..} = do
  t <- getFuncType _eloc (name2String _evarName) >>= inferType
  eff <- getEnv (funcEffs . at (name2String _evarName) . non (EffList [] _eloc)) >>= inferEffType
  return $ annotateExpr e t eff
inferExprType a@EApp {..} = do
  -- check assign variable
  when (name2String (_eappFunc ^. evarName) == "core/prelude/____assign") $ do
    if L.length _eappArgs /= 2
      then throwError $ "expected 2 arguments: " ++ ppr a ++ ppr _eloc
      else
        if isn't _EVar $ head _eappArgs
          then throwError $ "cannot assign to an expression: " ++ ppr (head _eappArgs) ++ ppr _eloc
          else -- first argument is the assigned variable which should be in local state
          do
            let vn = name2String $ head _eappArgs ^. evarName
            v <- getEnv $ localState . at vn
            case v of
              Just v -> return ()
              Nothing -> throwError $ "cannot find local variable " ++ vn ++ ppr _eloc
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
  eff <- inferAppResultEffType appFuncType typeArgs argTypes >>= inferEffType
  (t, ft) <- inferAppResultType appFuncType typeArgs argTypes
  t <- inferType t
  ft <- inferType ft
  appFunc <- selectFuncImpl typeArgs appFunc {_eannMetaType = bindTypeEffVar [] $ bindTypeVar [] ft} _eloc
  return $ annotateExpr a {_eappFunc = appFunc, _eappArgs = args} t eff
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
        (\(t, k) -> setEnv (Just $ k ^. non (KStar _eloc)) $ typeKinds . at (name2String t))
        [(t, k) | t <- bvs | k <- _elamBoundVars ^.. traverse . _2]
      -- add all bound eff type variables into env
      mapM_ (\t -> setEnv (Just $ EKStar _eloc) $ effKinds . at (name2String t)) evs
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
        (uncurry setFuncType)
        [(n, t) | (n, _) <- _elamArgs | t <- args]
      case _elamExpr of
        Just e -> return ()
        Nothing -> throwError $ "expected an expression for lambda" ++ ppr _eloc
      -- infer the lambda's expression type
      lamE <- inferExprType $ fromJust _elamExpr
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
      -- infer effects
      eff <- effTypeOfExpr lamE >>= inferEffType
      checkEffTypeMatch _elamEffType eff
      return $ annotateExpr l {_elamExpr = Just lamE} t (EffList [] _eloc)
    _ -> throwError "should not be here"
inferExprType a@EAnn {..} = do
  et <- inferExprType _eannExpr
  t <- typeOfExpr et
  eff <- effTypeOfExpr et >>= inferEffType
  k <- inferTypeKind _eannType
  checkTypeKind k
  at <- inferType _eannType
  bindings <- collectVarBindings False t at >>= checkAndAddTypeVarBindings
  let aet = substs bindings t
  return $ annotateExpr a {_eannExpr = et} aet eff
inferExprType l@ELit {..} = do
  k <- inferTypeKind _litType
  checkTypeKind k
  t <- inferType _litType
  return $ annotateExpr l t (EffList [] _eloc)
inferExprType s@ESeq {..} = do
  es <- mapM inferExprType _eseq
  ts <- mapM typeOfExpr es
  effs <- mapM effTypeOfExpr es
  t <- inferType $ last ts
  effs <- foldM
    ( \s e -> do
        mergeEffs s e
    )
    (EffList [] _eloc)
    effs >>= inferEffType
  return $ annotateExpr s {_eseq = es} t effs
inferExprType l@ELet {..} = do
  p <- inferExprInPattern _eletPattern
  et <- bindPatternVarTypes _eletState p _eletExpr
  bt <- inferExprType _eletBody
  t <- typeOfExpr bt >>= inferType
  e0 <- effTypeOfExpr bt
  e1 <- inferExprType _eletExpr >>= effTypeOfExpr >>= inferEffType
  eff <- mergeEffs e0 e1
  return $ annotateExpr l {_eletPattern = p, _eletExpr = et, _eletBody = bt} t eff
inferExprType c@ECase {..} = do
  -- infer case condition expression's type
  ce <- inferExprType _ecaseExpr
  ct <- typeOfExpr ce
  ceff <- effTypeOfExpr ce >>= inferEffType
  -- infer all case patterns' types
  ts <- forM _ecaseBody $ \c -> underScope $ do
    bindPatternVarTypes False (_casePattern c) _ecaseExpr
    p <- inferExprInPattern $ _casePattern c
    pt <- inferPatternType p
    e <- inferExprType $ _caseExpr c
    et <- typeOfExpr e
    eff <- effTypeOfExpr e >>= inferEffType
    return (pt, et, eff, c {_casePattern = p, _caseExpr = e})
  -- check if condition's type match with case exprs' type or not
  sts <- getSpecialTypes (ts ^.. traverse . _2)
  when (L.length sts /= 1) $ throwError $ "case exprs type conflict: " ++ ppr [(t, _tloc t) | t <- sts]
  -- check if all pattern expressions' type match or not
  forM_ (ts ^.. traverse . _1) $ \e ->
    checkTypeMatch ct e
  -- return case's type
  t <- inferType $ last sts
  -- infer effects
  effs <- foldM mergeEffs ceff (ts ^.. traverse . _3) >>= inferEffType
  return $ annotateExpr c {_ecaseExpr = ce, _ecaseBody = ts ^.. traverse . _4} t effs
inferExprType w@EWhile {..} = do
  -- infer while condition's type
  c <- inferExprType _ewhileCond
  t <- typeOfExpr c >>= inferType
  ce <- effTypeOfExpr c >>= inferEffType
  if aeq t (TPrim Pred _eloc)
    then return ()
    else throwError $ "while expected a bool as condition, but got " ++ ppr t ++ ppr _eloc
  -- infer while's body type
  (b, be) <- underScope $ do
    e <- inferExprType _ewhileBody
    t <- typeOfExpr e
    eff <- effTypeOfExpr e
    k <- inferTypeKind t
    checkTypeKind k
    return (e, eff)
  -- infer effects
  eff <- mergeEffs ce be
  return $ annotateExpr w {_ewhileCond = c, _ewhileBody = b} (TPrim Unit _eloc) eff
inferExprType h@EHandle {..} = underScope $ do
  unless (isn't _EffList _ehandleEff) $ throwError $ "expected an eff application, but got " ++ ppr _ehandleEff ++ ppr _eloc
  -- infer handle's effect kind
  ek <- inferEffKind _ehandleEff
  checkEffKind ek
  -- infer handle's expression's type
  scopeE <- inferExprType _ehandleScope
  resT <- typeOfExpr scopeE >>= inferType
  effs <- effTypeOfExpr scopeE >>= inferEffType
  btk <- inferTypeKind resT
  checkTypeKind btk

  let effN = name2String $ if isn't _EffVar _ehandleEff then _ehandleEff ^. effAppName . effVar else _ehandleEff ^. effVar
      prefix = join $ L.intersperse "/" $ init (splitOn "/" effN)

  when (effN == "core/prelude/io") $
    throwError $ effN ++ " effect cannot be handled"

  bs <- forM _ehandleBindings $ \intf -> underScope $ do
    let fn =
          if prefix == take (L.length prefix) (intf ^. funcName)
            then intf ^. funcName
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
      setEnv (Just resumeT) $ funcTypes . at "resume"

      -- check if interface defintion match with implemention's or not
      let handleT' = handleT {_tfuncEff = emptyEff, _tfuncResult = unit}
          intfT' = intfT {_tfuncEff = emptyEff, _tfuncResult = unit}
      collectVarBindings False intfT' handleT' >>= checkAndAddTypeVarBindings

      -- check expression result type
      intfE <- inferExprType $ fromJust $ _funcExpr intf
      intfResT <- typeOfExpr intfE
      checkTypeMatch intfResT resT

      return (handleT', intf {_funcExpr = Just intfE, _funcName = fn})

    -- check scope expr again
    --setEnv (Just handleT') $ funcs . at fn
    --t <- inferExprType _ehandleScope >>= typeOfExpr
    --k <- inferTypeKind t
    --checkTypeKind k
    return intfWithT

  -- check intefaces
  effName <-
    if not $ isn't _EffVar _ehandleEff
      then return $ name2String $ _ehandleEff ^. effVar
      else
        if not $ isn't _EffApp _ehandleEff
          then return $ name2String $ _effVar $ _effAppName _ehandleEff
          else throwError $ "expected an eff variable or application, but got " ++ ppr _ehandleEff ++ ppr _eloc
  intfs <- getEnv $ effIntfs . at effName
  case intfs of
    Just ifs -> do
      let intfNames = map (\i -> prefix ++ "/" ++ _funcName i) _ehandleBindings
      if L.sort ifs == L.sort intfNames
        then return ()
        else throwError $ "eff interfaces mismatch: " ++ ppr ifs ++ " vs " ++ ppr intfNames ++ ppr _eloc
    Nothing -> do
      throwError $ "cannot find effect: " ++ ppr _ehandleEff ++ ppr _eloc
  -- remove the handled effects
  effs <- removeEff effs _ehandleEff >>= inferEffType
  return $ annotateExpr h {_ehandleScope = scopeE, _ehandleBindings = bs} resT effs
inferExprType a@EAnnMeta {..} = inferExprType _eannMetaExpr
inferExprType e = throwError $ "unsupported: " ++ ppr e ++ ppr (_eloc e)

inferExprInPattern :: (Has EnvEff sig m) => Pattern -> m Pattern
inferExprInPattern p@PVar {..} = return p
inferExprInPattern p@PApp {..} = do
  args <- mapM inferExprInPattern _pappArgs
  return p{_pappArgs = args}
inferExprInPattern p@PExpr {..} = do
  e <- inferExprType _pExpr
  return p{_pExpr = e}

-- | Infer a pattern's type
inferPatternType :: (Has EnvEff sig m) => Pattern -> m Type
inferPatternType PVar {..} = inferExprType (EVar (s2n $ name2String _pvar) _ploc) >>= typeOfExpr
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
  eff <- effTypeOfExpr eWithType
  typeBindings <- extracePatternVarTypes p eType
  foldM_
    ( \bs (v, t) -> do
        let n = name2String v
        case bs ^. at n of
          Just _ -> throwError $ "pattern rebind a variable: " ++ n ++ ppr (_eloc e)
          Nothing -> do
            setFuncType n t
            setEnv (Just eff) $ funcEffs . at n
            -- set localState
            when isState $ setEnv (Just t) $ localState . at n
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
  bindings <- collectVarBindings False appResT t
  foldM
    ( \s e ->
        (++) s <$> e
    )
    []
    [extracePatternVarTypes arg argt | arg <- _pappArgs | argt <- substs bindings argTypes]

-- | Setup for effect inferface type
setupEffIntfType :: (Has EnvEff sig m) => FuncDef -> m ()
setupEffIntfType f = do
  let pos = f ^. funcLoc
      bvars = fmap (\t -> (name2String (t ^. _1), t ^. _2 . non (KStar pos))) $ f ^.. funcBoundVars . traverse
      bevars = fmap (\t -> (name2String t, EKStar pos)) $ f ^. funcBoundEffVars
  forM_ bvars $ \(n, k) -> setEnv (Just k) $ typeKinds . at n
  forM_ bevars $ \(n, k) -> setEnv (Just k) $ effKinds . at n
  mapM_
    (uncurry setFuncType)
    (f ^. funcArgs)
