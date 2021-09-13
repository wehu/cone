{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}

module Cone.TypeChecker (Env (..), types, funcs, effs, effIntfs, funcImpls, initialEnv, initModule, checkType) where

import Cone.Parser.AST
import Cone.TypeChecker.Env
import Cone.TypeChecker.Type
import Cone.TypeChecker.Expr
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

-- | Initialize type definition and add the kind for the type into env
initTypeDef :: (Has EnvEff sig m) => String -> TypeDef -> m TypeDef
initTypeDef prefix t = do
  let tn = prefix ++ "/" ++ t ^. typeName
  ot <- getEnv $ types . at tn
  -- check if it exists or not
  forMOf _Just ot $ \ot ->
    throwError $
      "redefine a type: " ++ tn ++ " vs " ++ ppr ot ++ (ppr $ _typeLoc t)
  -- record the kind of type
  let k = Just $ typeKindOf t
  setEnv k $ types . at tn
  return t{_typeName = tn}
  where
    typeKindOf t =
      let loc = _typeLoc t
          args = t ^. typeArgs
          star = KStar loc
       in if args == []  -- if no arguments, it is just a simple enum
            then star
            else KFunc (args ^.. traverse . _2 . non star) star loc

-- | Initialize all type definitions
initTypeDefs :: (Has EnvEff sig m) => Module -> m Module
initTypeDefs m = transformMOn (topStmts . traverse . _TDef) (initTypeDef $ m ^. moduleName) m

-- | Initialize a constructor in type definition
initTypeConDef :: (Has EnvEff sig m) => TypeDef -> m ()
initTypeConDef t = do
  globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
  forM_ (t ^. typeCons) $ \c -> do
    let cn = c ^. typeConName
        cargs = c ^. typeConArgs
        pos = c ^. typeConLoc
        -- find all free type variables
        targs = (t ^.. typeArgs . traverse . _1) ++ globalTypes
        b = bind targs cargs
        fvars = (b ^.. fv) :: [TVar]
    if fvars /= [] -- if there are any free type variable, it failed
      then
        throwError $
          "type constructor's type variables should "
            ++ "only exists in type arguments: "
            ++ ppr fvars
      else return ()
    -- check if the type constructor exists or not
    ot <- getEnv $ funcs . at cn
    forMOf _Just ot $ \t ->
      throwError $
        "type construct has conflict name: " ++ cn ++ " vs " ++ ppr t ++ ppr pos
    -- record the constructor's type
    let bt = tconType c t
    setEnv (Just bt) $ funcs . at cn
  where
    tconType c t =
      let targs = c ^. typeConArgs
          tn = t ^. typeName
          pos = c ^. typeConLoc
          tvars = t ^.. typeArgs . traverse . _1
          rt =
            if tvars == []
              then TVar (s2n tn) pos
              else TApp (TVar (s2n tn) pos) (fmap (\t -> TVar t pos) tvars) pos
          bt =
            bindType tvars $
              if targs == []
                then rt
                else TFunc targs (EffList [] pos) rt pos
       in bindTypeEffVar [] bt

-- | Initialize all type constructors
initTypeConDefs :: (Has EnvEff sig m) => Module -> m ()
initTypeConDefs m = mapM_ initTypeConDef $ m ^.. topStmts . traverse . _TDef

-- | Check the type constructor's type
checkTypeConDef :: (Has EnvEff sig m) => TypeDef -> m ()
checkTypeConDef t =
  forM_ (t ^. typeCons) $ \c -> do
    let cn = c ^. typeConName
    tt <- getEnv $ funcs . at cn
    forMOf _Nothing tt $ \_ ->
      throwError $
        "cannot find type constructor : " ++ cn ++ (ppr $ _typeLoc t)
    k <- underScope $ inferTypeKind $ fromJust tt
    checkTypeKind k

-- | Check all type constructor's types
checkTypeConDefs :: (Has EnvEff sig m) => Module -> m ()
checkTypeConDefs m = mapM_ checkTypeConDef $ m ^.. topStmts . traverse . _TDef

-- | Initializa effect type definition
initEffTypeDef :: (Has EnvEff sig m) => String -> EffectDef -> m EffectDef
initEffTypeDef prefix e = do
  let en = prefix ++ "/" ++ e ^. effectName
  oe <- getEnv $ effs . at en
  forMOf _Just oe $ \oe ->
    throwError $
      "redefine an effect: " ++ en ++ " vs " ++ ppr oe ++ (ppr $ _effectLoc e)
  setEnv (Just $ effKind e) $ effs . at en
  return e{_effectName=en}
  where
    effKind e =
      let loc = _effectLoc e
          args = e ^. effectArgs
          star = KStar loc
          estar = EKStar loc
       in if args == []
            then estar
            else EKFunc (args ^.. traverse . _2 . non star) estar loc

-- | Initialize all effect type difinitions
initEffTypeDefs :: (Has EnvEff sig m) => Module -> m Module
initEffTypeDefs m = transformMOn (topStmts . traverse . _EDef) (initEffTypeDef $ m ^. moduleName) m 

-- | Initialize effect inteface definitions
initEffIntfDef :: (Has EnvEff sig m) => EffectDef -> m ()
initEffIntfDef e = do
  globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
  let is = e ^. effectIntfs
      en = e ^. effectName
      f = \i -> do
        let intfn = i ^. intfName
            iargs = i ^. intfArgs
            iresult = _intfResultType i
            pos = i ^. intfLoc
            bvars = (i ^. intfBoundVars)
            targs = (e ^.. effectArgs . traverse . _1) ++ globalTypes
            b = bind (targs ++ bvars) $ iresult : iargs
            fvars = (b ^.. fv) :: [TVar]
        addEffIntfs en intfn
        -- check if has free type variables
        if fvars /= []
          then
            throwError $
              "eff interfaces's type variables should "
                ++ "only exists in eff type arguments: "
                ++ ppr fvars ++ ppr pos
          else return ()
        -- check if inteface exists or not
        ot <- getEnv $ funcs . at intfn
        forMOf _Just ot $ \t ->
          throwError $
            "eff interface has conflict name: " ++ intfn ++ " vs " ++ ppr t ++ ppr pos
        -- get effect type
        let eff = _intfEffectType i
        effs <- 
          mergeEffs eff $
            if e ^. effectArgs  == []
            then EffVar (s2n $ e ^. effectName) pos
            else EffApp
                  (EffVar (s2n $ e ^. effectName) pos)
                  (map (\v -> TVar v pos) $ e ^.. effectArgs . traverse . _1)
                  pos
        --  add effect type to interface's effect list
        let bt = intfType i e effs
        setEnv (Just bt) $ funcs . at intfn
  mapM_ f is
  where
    intfType i e eff =
      let iargs = i ^. intfArgs
          iresult = _intfResultType i
          intfn = i ^. intfName
          bvars = i ^. intfBoundVars
          pos = i ^. intfLoc
          tvars = e ^.. effectArgs . traverse . _1
          evars = i ^. intfBoundEffVars
       in bindTypeEffVar evars $ bindType tvars $
              bindType bvars $ TFunc iargs eff iresult pos

-- | Initialize all effect interfaces
initEffIntfDefs :: (Has EnvEff sig m) => Module -> m ()
initEffIntfDefs m = mapM_ initEffIntfDef $ m ^.. topStmts . traverse . _EDef

-- | Check an effect interface
checkEffIntfDef :: (Has EnvEff sig m) => EffectDef -> m ()
checkEffIntfDef e = do
  globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
  let is = e ^. effectIntfs
      en = e ^. effectName
      f = \i -> do
        let intfn = i ^. intfName
        t <- getEnv $ funcs . at intfn
        forMOf _Nothing t $ \t ->
          throwError $
            "cannot find eff interface: " ++ intfn ++ ppr (_effectLoc e)
        k <- underScope $ inferTypeKind $ fromJust t
        checkTypeKind k
  mapM_ f is

-- | Check all effect interfaces
checkEffIntfDefs :: (Has EnvEff sig m) => Module -> m ()
checkEffIntfDefs m = mapM_ checkEffIntfDef $ m ^.. topStmts . traverse . _EDef

-- | Initializa function definition
initFuncDef :: (Has EnvEff sig m) => FuncDef -> m ()
initFuncDef f = do
  let pos = f ^. funcLoc
      fn = f ^. funcName
      ft = funcDefType f
  k <- inferTypeKind ft
  checkTypeKind k
  oft <- getEnv $ funcs . at fn
  forMOf _Just oft $ \oft ->
    throwError $ "function redefine: " ++ fn ++ ppr pos
  setEnv (Just ft) $ funcs . at fn

-- | Initialize all function definitons
initFuncDefs :: (Has EnvEff sig m) => Module -> m ()
initFuncDefs m = mapM_ initFuncDef $ m ^.. topStmts . traverse . _FDef

-- | Check a function type
checkFuncType :: (Has EnvEff sig m) => FuncDef -> m FuncDef
checkFuncType f = underScope $ do
  let pos = f ^. funcLoc
      btvars = fmap (\t -> (name2String t, KStar pos)) $ f ^. funcBoundVars
      bevars = fmap (\t -> (name2String t, EKStar pos)) $ f ^. funcBoundEffVars
  -- add all bound type variables into env
  forM_ btvars $ \(n, k) -> setEnv (Just k) $ types . at n
  -- add all bound eff type variables into env
  forM_ bevars $ \(n, k) -> setEnv (Just k) $ effs . at n
  -- add function type into env
  mapM_
    (\(n, t) -> setFuncType n t)
    (f ^. funcArgs)
  case _funcExpr f of
    Just e -> do
      -- infer function expression type
      eWithType <- inferExprType e
      eType <- typeOfExpr eWithType
      resultType <- inferType $ _funcResultType f
      checkTypeMatch eType resultType
      effType <- inferExprEffType e
      let fEff = _funcEffectType f
      restEffs <- removeEff effType fEff
      -- check if all effects are handled or not
      if aeq restEffs (EffList [] pos) then return f{_funcExpr=Just eWithType}
      else throwError $ "func result effs mismatch: " ++ ppr effType ++ " vs " ++ ppr fEff ++ ppr pos
    Nothing -> return f

-- | Check a function definiton
checkFuncDef :: (Has EnvEff sig m) => FuncDef -> m FuncDef
checkFuncDef f = underScope $ do
  let pos = f ^. funcLoc
      ft = funcDefType f
  k <- inferTypeKind ft
  checkTypeKind k
  checkFuncType f

-- | Check all function definitons
checkFuncDefs :: (Has EnvEff sig m) => Module -> m [FuncDef]
checkFuncDefs m = mapM checkFuncDef $ m ^.. topStmts . traverse . _FDef

-- | Init a function implementation
initImplFuncDef :: (Has EnvEff sig m) => ImplFuncDef -> m ()
initImplFuncDef f = setFuncImpl f

-- | Init function implementations
initImplFuncDefs :: (Has EnvEff sig m) => Module -> m ()
initImplFuncDefs m = mapM_ initImplFuncDef $ m ^.. topStmts . traverse . _ImplFDef

-- | Check a function implementation
checkImplFuncDef :: (Has EnvEff sig m) => FuncDef -> m FuncDef
checkImplFuncDef f = underScope $ do
  let ft = funcDefType f
  k <- inferTypeKind ft
  checkTypeKind k
  checkFuncType f

-- | Check all function implementations
checkImplFuncDefs :: (Has EnvEff sig m) => Module -> m [ImplFuncDef]
checkImplFuncDefs m = mapM (\f -> ImplFuncDef <$> checkImplFuncDef f) $ m ^.. topStmts . traverse . _ImplFDef . implFunDef

-- | Remove meta annotation
removeAnn :: Expr -> Expr
removeAnn e = transform remove e
  where remove (EAnnMeta e _ _) = e
        remove (EAnn e _ _) = e
        remove e = e

-- | Remove all meta annotations
removeAnns :: Module -> Module
removeAnns m =
  transformOn (topStmts . traverse . _FDef . funcExpr . _Just) removeAnn $
  transformOn (topStmts . traverse . _ImplFDef . implFunDef . funcExpr . _Just) removeAnn m

-- | Rename func implementation names
convertFuncImplToFuncs :: Module -> Module
convertFuncImplToFuncs m =
  let tops = (m ^..  topStmts . traverse)
      fs = map
            (\f ->
              let fn = f ^. funcName
                  ft = funcDefType f
                  n = uniqueFuncImplName fn ft
               in FDef f{_funcName = n})
               (m ^.. topStmts . traverse . _ImplFDef . implFunDef)
    in m{_topStmts=tops ++ fs}

addTypeBindingsForExprs :: Module -> Module
addTypeBindingsForExprs m =
  transformOn (topStmts . traverse. _EDef) bindEDef $
  transformOn (topStmts . traverse. _TDef) bindTDef $
  transformOn (topStmts . traverse. _FDef) bindFDef $
  transformOn (topStmts . traverse. _ImplFDef . implFunDef) bindFDef m
  where
    bindEDef edef =
      let boundVars = edef ^.. effectArgs . traverse . _1
       in BoundEffectDef (bind boundVars edef) (_effectLoc edef)
    bindTDef tdef = 
     let boundVars = tdef ^.. typeArgs . traverse . _1
      in BoundTypeDef (bind boundVars tdef) (_typeLoc tdef) 
    bindFDef fdef = 
     let boundVars = fdef ^. funcBoundVars
         boundEffVars = fdef ^. funcBoundEffVars
         loc = fdef ^. funcLoc
         expr = fmap (transform bindExpr) $ _funcExpr fdef
      in BoundFuncDef (bind boundVars fdef{_funcExpr = expr}) loc
    bindExpr l@ELam{..} = 
      let boundVars = _elamBoundVars
          boundEffVars = _elamBoundEffVars
       in l{_elamExpr = fmap (\e -> 
             EBoundEffTypeVars (bind boundEffVars $ EBoundTypeVars (bind boundVars e) _eloc) _eloc) _elamExpr}
    bindExpr expr = expr

removeTypeBindingsForExprs :: Module -> Module
removeTypeBindingsForExprs m =
  transformOn (topStmts . traverse. _EDef) removeBindingsForEDef $
  transformOn (topStmts . traverse. _TDef) removeBindingsForTDef $
  transformOn (topStmts . traverse. _FDef) removeBindingsForFDef $
  transformOn (topStmts . traverse. _ImplFDef . implFunDef) removeBindingsForFDef m
  where
    removeBindingsForEDef (BoundEffectDef b _) =
      let (_, e) = unsafeUnbind b
       in removeBindingsForEDef e
    removeBindingsForEDef e = e
    removeBindingsForTDef (BoundTypeDef b _) =
      let (_, t) = unsafeUnbind b
       in removeBindingsForTDef t
    removeBindingsForTDef t = t
    removeBindingsForFDef (BoundFuncDef b _) = 
      let (_, f) = unsafeUnbind b
       in removeBindingsForFDef f
    removeBindingsForFDef (BoundEffFuncDef b _) = 
      let (_, f) = unsafeUnbind b
       in removeBindingsForFDef f
    removeBindingsForFDef fdef = 
     let expr = fmap (transform removeBindingsForExpr) $ _funcExpr fdef
      in fdef{_funcExpr = expr}
    removeBindingsForExpr (EBoundTypeVars b _) =
      let (_, e) = unsafeUnbind b
       in removeBindingsForExpr e
    removeBindingsForExpr (EBoundEffTypeVars b _) =
      let (_, e) = unsafeUnbind b
       in removeBindingsForExpr e
    removeBindingsForExpr expr = expr

addPrefixForTypes :: (Has EnvEff sig m) => Module -> m Module
addPrefixForTypes m' = do
  let m = addTypeBindingsForExprs m'
  let allGlobalVars = (reverse . L.nub . reverse) (m ^.. fv) :: [TVar]
      allGlobalEffVars = (reverse . L.nub . reverse) (m ^.. fv) :: [EffVar]
      prefixes = (m ^. moduleName ++ "/") :
                 "core/prelude/" : 
                 (map (\i -> i ^.importPath ++ "/") $ m ^. imports)
      loc = m ^. moduleLoc
  -- trace (show allGlobalVars) $ return ()
  ts <- getEnv types
  es <- getEnv effs
  bindTs <- foldM (
      \s v -> do
        found <- foldM (
                    \f p -> do
                      let vn = p ++ (name2String v)
                      case ts ^. at vn of
                        Just _ -> return $ f ++ [(v, TVar (s2n vn) loc)]
                        Nothing -> return f
                    )
                    []
                    prefixes
        if found == [] then return s
        else if L.length found == 1 then return $ s ++ found
             else throwError $ "found more than one type for " ++ ppr v ++ ppr found
      ) [] allGlobalVars
  bindEffs <- foldM (
      \s v -> do
        found <- foldM (
                    \f p -> do
                      let vn = p ++ (name2String v)
                      case es ^. at vn of
                        Just _ -> return $ f ++ [(v, EffVar (s2n vn) loc)]
                        Nothing -> return f
                    )
                    []
                    prefixes
        if found == [] then return s
        else if L.length found == 1 then return $ s ++ found
             else throwError $ "found more than one eff type for " ++ ppr v ++ ppr found
      ) [] allGlobalEffVars
  return $ removeTypeBindingsForExprs $ substs bindEffs $ substs bindTs m

-- | Initialize a module
initModule :: Module -> Env -> Int -> Either String (Env, (Int, Module))
initModule m env id = run . runError . (runState env) . runFresh id $ do
  m <- (return $ convertFuncImplToFuncs m)
       >>= initTypeDefs
       >>= initEffTypeDefs
       >>= addPrefixForTypes
  initTypeConDefs m
  initEffIntfDefs m
  initFuncDefs m
  initImplFuncDefs m
  return m

-- | Type checking a module
checkType :: Module -> Env -> Int -> Either String (Env, (Int, Module))
checkType m env id = run . runError . (runState env) . runFresh id $ do
  checkTypeConDefs m
  checkEffIntfDefs m
  let ts = map TDef $ m ^.. topStmts . traverse . _TDef 
      es = map EDef $ m ^.. topStmts . traverse . _EDef
  fs <- map FDef <$> checkFuncDefs m
  ifs <- map ImplFDef <$> checkImplFuncDefs m
  return $ removeAnns m{_topStmts=ts ++ es ++ fs ++ ifs}
