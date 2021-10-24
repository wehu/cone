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
import Data.Digest.Pure.MD5
import qualified Data.ByteString.Lazy.UTF8 as BLU
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
      bt = bind (globalTypes::[TVar]) (bindTypeFDef f)
      be = bind (globalEffTypes::[EffVar]) (bindTypeFDef f)
      ftvars = L.nubBy aeq (bt ^.. fv) :: [TVar]
      fevars = L.nubBy aeq (be ^.. fv) :: [EffVar]
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
  --setEnv M.empty typeBinds
  --setEnv M.empty kindBinds
  --setEnv M.empty effTypeBinds
  --setEnv M.empty effKindBinds
  let pos = f ^. funcLoc
      ft = funcDefType f
  k <- inferTypeKind ft
  checkTypeKind k
  checkFuncType f

getSpecializedFunc :: (Has EnvEff sig m) => [Type] -> String -> Type -> m String
getSpecializedFunc targs fn t = do
  if isConcreteType t then do
    mn <- getEnv currentModuleName
    let fSel = mn ++ "/" ++ last (splitOn "/" $ uniqueFuncImplName fn t) ++ join (map (uniqueFuncImplName "_") targs)
    f <- getEnv $ specializedFuncs . at fSel
    case f of
      Nothing -> do
        fdef <- getEnv $ funcDefs . at fn
        case fdef of
          Just fdef -> do
            if isn't _Nothing (_funcExpr fdef) && not (null (_funcBoundVars fdef) && null (_funcBoundEffVars fdef))
            then underScope $ do
              fdef <- applyTArgs fdef
              bs <- foldM (\s (v, _, _) -> do
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

  -- add implicit argument placeholders
  placeHolders <- genImplicitArgPlaceHolders appFuncType

  appFuncType <- applyTypeArgs appFuncType _eappTypeArgs >>= unbindType

  -- infer all arguments' types
  args <- mapM inferExprType $ if isn't _TFunc appFuncType || L.length (_tfuncArgs appFuncType) == L.length _eappArgs then _eappArgs else placeHolders ++ _eappArgs
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
  -- refresh all bound variables
  (bvs, newLam') <- refreshTypeVar (_elamBoundVars ^.. traverse . _1) l{_elamExpr=fmap bindTypeExpr _elamExpr}
  (evs, newLam') <- refreshEffVar _elamBoundEffVars newLam'
  let newLam = removeTypeBindingsForExpr newLam'
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
      -- forM_ _elamBoundVars $ \(_, _, cs) ->
      --   unless (null cs) $
      --     throwError $ "lambda does not support constraints yes " ++ ppr cs ++ ppr _eloc
      -- return the lambda type
      let nbvs = [(t, k, cs) | t <- bvs | (_, k, cs) <- _elamBoundVars]
      t <-
        inferType $
          bindTypeEffVar evs $
            bindTypeVar
              nbvs
              $ TFunc args _elamEffType eType _eloc
      -- infer effects
      eff <- effTypeOfExpr lamE >>= inferEffType
      checkEffTypeMatch _elamEffType eff
      return $ annotateExpr l {_elamBoundVars=nbvs, _elamBoundEffVars = evs, _elamExpr = Just lamE} t (EffList [] _eloc)
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

genImplicitArgPlaceHolders :: (Has EnvEff sig m) => Type -> m [Expr]
genImplicitArgPlaceHolders BoundEffVarType{..} = do
  let (_, t) = unsafeUnbind _boundEffVarType
  genImplicitArgPlaceHolders t
genImplicitArgPlaceHolders BoundType{..} = do
  let (bvs, t) = unsafeUnbind _boundType
  foldM (\s (n, t, cs) -> do
    foldM (\s c -> do
      let cn = name2String (_tvar c) ++ "_$dict"
          pos = _tloc
      return $ s++[EApp False (EVar (s2n cn) pos) [] [] pos]) s cs)
    []
    bvs
genImplicitArgPlaceHolders t = throwError $ "unsupported type " ++ ppr t ++ ppr (_tloc t)

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

isExprWithFuncType :: Expr -> Bool
isExprWithFuncType (EAnnMeta e TFunc{} eff loc) = True
isExprWithFuncType _ = False

collectLastFuncTypeExpr :: Expr -> [Expr]
collectLastFuncTypeExpr ESeq{..} = [last _eseq | isExprWithFuncType (last _eseq)]
collectLastFuncTypeExpr ELet{..} = collectLastFuncTypeExpr _eletBody
collectLastFuncTypeExpr ECase{..} = join $ map (collectLastFuncTypeExpr . _caseExpr) _ecaseBody
collectLastFuncTypeExpr EHandle{..} = collectLastFuncTypeExpr _ehandleScope
collectLastFuncTypeExpr e | isExprWithFuncType e = [e]
collectLastFuncTypeExpr _ = []

checkLocalState :: (Has EnvEff sig m) => Expr -> m Expr
checkLocalState l@ELet{..} | _eletState = do
  let fs = collectLastFuncTypeExpr l
  forM_ fs $ \f -> do
    let bf = bindVarExpr f
        vs = map name2String (bf ^.. fv :: [EVar])
        ps = map name2String (_eletPattern ^.. fv :: [PVar])
    unless (null $ ps `L.intersect` vs) $ do
      throwError $ "a functional expression includes local state which would be out of scope " ++ ppr l ++ ppr (f ^.eloc)
  return l
checkLocalState e = return e

-- | Get real name if there is alias prefix
getNamePath :: (Has EnvEff sig m) => Module -> String -> m String
getNamePath m n = do
  aliases <-
    foldM
      ( \s i ->
          case i ^. importAlias of
            Just alias -> do
              let old = s ^. at alias
              case old of
                Just old -> throwError $ "import alias conflict: import " ++ ppr old ++ " as " ++ ppr alias ++ " vs " ++ ppr i ++ ppr (_importLoc i)
                Nothing -> return $ s & at alias ?~ i ^. importPath
            Nothing -> return s
      )
      M.empty
      $ m ^. imports
  let n' = last $ splitOn "/" n
      ns = join $ L.intersperse "/" $ L.init $ splitOn "/" n
  case aliases ^. at ns of
    Just prefix -> return $ prefix ++ "/" ++ n'
    Nothing -> return n

filterOutAliasImports :: Module -> String -> [String] -> [String]
filterOutAliasImports m n ns =
  let aliasImports =
        L.nub $
          L.foldl'
            ( \s i ->
                case i ^. importAlias of
                  Just alias -> s ++ [(i ^. importPath) ++ "/" ++ n]
                  Nothing -> s
            )
            []
            $ m ^. imports
   in L.nub ns L.\\ aliasImports

-- | Func implementation selector
funcImplSelector :: Type -> String
-- TODO md5 is not good, better just replace the special chars
funcImplSelector t = show $ md5 $ BLU.fromString $ ppr t

uniqueFuncImplName :: String -> Type -> String
uniqueFuncImplName fn t = fn ++ funcImplSelector t

searchFunc :: (Has EnvEff sig m) => Module -> String -> Location -> m String
searchFunc m fn loc = do
  let prefixes =
        L.nub $
          "" :
          (m ^. moduleName ++ "/") :
          "core/prelude/" :
          map (\i -> i ^. importPath ++ "/") (m ^. imports)
  n <- getNamePath m fn
  fs <- getEnv funcTypes
  found <-
    filterOutAliasImports m n
      <$> foldM
        ( \f p -> do
            let ffn = p ++ n
            case fs ^. at ffn of
              Just _ -> return $ f ++ [ffn]
              Nothing -> return f
        )
        []
        prefixes
  if null found
    then throwError $ "no function definition found for : " ++ fn ++ ppr loc
    else
      if L.length found == 1
        then return $ head found
        else throwError $ "found more than one function for " ++ fn ++ ppr found ++ ppr loc

-- | Set a function implementation
setFuncImpl :: (Has EnvEff sig m) => Module -> ImplFuncDef -> m ImplFuncDef
setFuncImpl m impl = do
  prefix <- getEnv currentModuleName
  let funcD = impl ^. implFunDef
      fn = prefix ++ "/" ++ funcD ^. funcName
      loc = funcD ^. funcLoc
      t =
        bindTypeEffVar (funcD ^. funcBoundEffVars) $
          bindTypeVar (funcD ^. funcBoundVars) $
            TFunc (funcD ^.. funcArgs . traverse . _2) (_funcEffectType funcD) (_funcResultType funcD) loc
  intfn <- searchFunc m (funcD ^. funcName) loc
  ft <- fromJust <$> getEnv (funcTypes . at intfn)
  isSubT <- isSubType t ft
  if isSubT
    then return ()
    else
      throwError $
        "implementation type is not subtype of general type: "
          ++ ppr t
          ++ ppr loc
          ++ " vs "
          ++ ppr ft
          ++ ppr (_tloc ft)
  let sel = uniqueFuncImplName fn t
      i = EVar (s2n sel) loc
  addFuncImpl intfn i t
  return impl {_implFunDef = funcD {_funcName = fn}}

searchInterface :: (Has EnvEff sig m) => Module -> String -> Location -> m String
searchInterface m iname loc = do
  let prefixes =
        L.nub $
          "" :
          (m ^. moduleName ++ "/") :
          "core/prelude/" :
          map (\i -> i ^. importPath ++ "/") (m ^. imports)
  n <- getNamePath m iname
  is <- getEnv intfFuncs
  found <-
    filterOutAliasImports m n
      <$> foldM
        ( \f p -> do
            let iin = p ++ n
            case is ^. at iin of
              Just _ -> return $ f ++ [iin]
              Nothing -> return f
        )
        []
        prefixes
  if null found
    then throwError $ "no interface definition found for : " ++ iname ++ ppr loc
    else
      if L.length found == 1
        then return $ head found
        else throwError $ "found more than one interface for " ++ iname ++ ppr found ++ ppr loc

selectIntf :: (Has EnvEff sig m) => Expr -> m Expr
selectIntf v@(EAnnMeta EVar{..} t et loc) = do
  t <- inferType t
  impls <- getEnv $ intfImpls . at (name2String _evarName)
  case impls of
    Just impls -> do
      fs <- findSuperIntfImpls t impls >>= findBestIntfImpls t
      when (null fs) $ throwError $ "cannot find interface implementation " ++ ppr v ++ ppr loc
      when (L.length fs > 1) $ throwError $ "there are more than one interface implemention matched " ++ show fs ++ ppr loc
      let (cntr, ft, index) = head fs
      return v
    Nothing -> return v
selectIntf l@ELit{..} = return l
selectIntf l@ELam{..} = underScope $ do
  -- add all bound type variables into env
  mapM_
    (\(t, k, []) -> setEnv (Just $ k ^. non (KStar _eloc)) $ typeKinds . at (name2String t)) _elamBoundVars
  -- add all bound eff type variables into env
  mapM_ (\t -> setEnv (Just $ EKStar _eloc) $ effKinds . at (name2String t)) _elamBoundEffVars
  setupIntfEnvs _elamBoundVars _elamArgs
  underScope $ mapMOf (elamExpr . _Just) selectIntf l
selectIntf c@ECase{..} = do
  e <- selectIntf _ecaseExpr
  cs <- underScope $ mapMOf (traverse . caseExpr) selectIntf _ecaseBody
  return c{_ecaseExpr=e, _ecaseBody=cs}
selectIntf w@EWhile{..} = do
  c <- selectIntf _ewhileCond
  b <- underScope $ selectIntf _ewhileBody
  return w{_ewhileCond=c, _ewhileBody=b}
selectIntf a@EApp{..} = do
  f <- selectIntf _eappFunc
  args <- mapM selectIntf _eappArgs
  return a{_eappFunc=f, _eappArgs=args}
selectIntf l@ELet{..} = do
  e <- selectIntf _eletExpr
  b <- underScope $ selectIntf _eletBody
  return l{_eletExpr=e, _eletBody=b}
selectIntf h@EHandle{..} = underScope $ do
  e <- selectIntf _ehandleScope
  binds <- mapM selectIntfForFunc _ehandleBindings
  return h{_ehandleScope = e, _ehandleBindings = binds}
selectIntf s@ESeq{..} = mapMOf (eseq . traverse) selectIntf s
selectIntf a@EAnn{..} = mapMOf eannExpr selectIntf a
selectIntf a@EAnnMeta{..} = mapMOf eannMetaExpr selectIntf a
selectIntf b@EBoundTypeVars {..} = do
  let (vs, e) = unsafeUnbind _eboundTypeVars
  e <- selectIntf e
  return b{_eboundTypeVars=bind vs e}
selectIntf b@EBoundEffTypeVars {..} = do
  let (vs, e) = unsafeUnbind _eboundEffTypeVars
  e <- selectIntf e
  return b{_eboundEffTypeVars=bind vs e}
selectIntf b@EBoundVars{..} = do
  let (vs, e) = unsafeUnbind _eboundVars
  e <- selectIntf e
  return b{_eboundVars=bind vs e}
selectIntf e = return e

findSuperIntfImpls :: (Has EnvEff sig m) => Type -> [(String, Type, Int)] -> m [(String, Type, Int)]
findSuperIntfImpls t = foldM
    ( \f (e, it, i) -> do
        is <- isEqOrSubType t it
        if is
          then return $ f ++ [(e, it, i)]
          else return f
    )
    []

findBestIntfImpls :: (Has EnvEff sig m) => Type -> [(String, Type, Int)] -> m [(String, Type, Int)]
findBestIntfImpls t impls' = do
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

selectIntfForFunc :: (Has EnvEff sig m) => FuncDef -> m FuncDef
selectIntfForFunc f@FuncDef {..} = underScope $ do
  let pos = _funcLoc
      star = KStar pos
      btvars = fmap (\t -> (name2String (t ^. _1), t ^. _2 . non star)) $ f ^. funcBoundVars
      bevars = fmap (\t -> (name2String t, EKStar pos)) $ f ^. funcBoundEffVars
  -- add all bound type variables into env
  forM_ btvars $ \(n, k) -> setEnv (Just k) $ typeKinds . at n
  -- add all bound eff type variables into env
  forM_ bevars $ \(n, k) -> setEnv (Just k) $ effKinds . at n
  setupIntfEnvs _funcBoundVars _funcArgs
  mapMOf (funcExpr . _Just) selectIntf f
selectIntfForFunc f = return f

setupIntfEnvs :: (Has EnvEff sig m) => [(TVar, Maybe Kind, [Type])] -> [(String, Type)] -> m ()
setupIntfEnvs boundVars funcArgs =
  foldM_
    ( \i (v, k, cs) -> do
        foldM
          ( \i c -> do
              case c of
                t@(TVar n loc) -> do
                  let cntrN = name2String n ++ "_$dict"
                      cntr = (funcArgs !! i ^. _1, TApp t [TVar v loc] loc)
                  oldCntrs <- getEnv $ intfCntrs . at cntrN . non []
                  setEnv (Just $ cntr : oldCntrs) $ intfCntrs . at cntrN

                  let intfN = name2String n
                  intfs <- getEnv $ intfFuncs . at intfN
                  when (isn't _Just intfs) $ throwError $ "cannot find interface " ++ ppr n ++ ppr loc
                  let prefix = join $ L.intersperse "/" $ init $ splitOn "/" intfN
                  impls <-
                    mapM
                      ( \(n, t', index) -> do
                          t <- applyTypeArgs t' [TVar v loc]
                          return (prefix ++ "/" ++ n, (funcArgs !! i ^. _1, t, index))
                      )
                      (fromJust intfs)
                  forM_ impls $ \(intf, impl) -> do
                    oldImpls <- getEnv $ intfImpls . at intf . non []
                    setEnv (Just $ impl : oldImpls) $ intfImpls . at intf
                  return $ i + 1
                _ -> throwError $ "expect a type var, but got " ++ ppr c ++ ppr (_tloc c)
          )
          i
          cs
    )
    (0 :: Int)
    boundVars