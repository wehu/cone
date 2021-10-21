{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Cone.TypeChecker (initModule, checkType) where

import Cone.Parser.AST
import Cone.Env
import Cone.TypeChecker.Expr
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
import Data.List.Split
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe

-- | Initialize type definition and add the kind for the type into env
initTypeDef :: (Has EnvEff sig m) => TypeDef -> m TypeDef
initTypeDef t = do
  prefix <- getEnv currentModuleName
  let tn = prefix ++ "/" ++ t ^. typeName
  ot <- getEnv $ typeKinds . at tn
  -- check if it exists or not
  forMOf _Just ot $ \ot ->
    throwError $
      "redefine a type: " ++ tn ++ " vs " ++ ppr ot ++ ppr (_typeLoc t)
  -- record the kind of type
  let k = Just $ typeKindOf t
  setEnv k $ typeKinds . at tn
  return t {_typeName = tn}
  where
    typeKindOf t =
      let loc = _typeLoc t
          args = t ^. typeArgs
          star = KStar loc
          num = KNum loc
          resK = case t ^. typeName of
            "neg" -> num
            "add" -> num
            "sub" -> num
            "mul" -> num
            "div" -> num
            "mod" -> num
            "max" -> num
            "min" -> num
            "cons" -> KList num loc
            "nil" -> KList num loc
            _ -> star
       in if null args && t ^. typeName /= "nil" -- if no arguments, it is just a simple enum
            then star
            else KFunc (args ^.. traverse . _2 . non star) resK loc

-- | Initialize all type definitions
initTypeDefs :: (Has EnvEff sig m) => Module -> m Module
initTypeDefs = mapMOf (topStmts . traverse . _TDef) initTypeDef

-- | Initialize a constructor in type definition
initTypeConDef :: (Has EnvEff sig m) => TypeDef -> m TypeDef
initTypeConDef t = do
  prefix <- getEnv currentModuleName
  globalTypes <- fmap s2n . M.keys <$> getEnv typeKinds
  -- find all free type variables
  let b = bind (globalTypes::[TVar]) (bindTDef t)
      fvars = (b ^.. fv) :: [TVar]
  when (fvars /= []) $
          throwError $
            "type constructor's type variables should "
              ++ "only exists in type arguments: "
              ++ ppr fvars
  mapMOf
    (typeCons . traverse)
    ( \c -> do
        let cn = prefix ++ "/" ++ c ^. typeConName
            cargs = c ^. typeConArgs
            pos = c ^. typeConLoc
        -- check if the type constructor exists or not
        ot <- getEnv $ funcTypes . at cn
        forMOf _Just ot $ \t ->
          throwError $
            "type construct has conflict name: " ++ cn ++ " vs " ++ ppr t ++ ppr pos
        -- record the constructor's type
        let bt = tconType c t
        setEnv (Just bt) $ funcTypes . at cn
        return c {_typeConName = cn}
    )
    t
  where
    tconType c t =
      let targs = c ^. typeConArgs
          tn = t ^. typeName
          pos = c ^. typeConLoc
          tvars = t ^. typeArgs
          rt =
            if null tvars
              then TVar (s2n tn) pos
              else TApp (TVar (s2n tn) pos) (fmap (\t -> TVar (t ^. _1) pos) tvars) pos
          bt =
            bindTypeVar tvars $
              if null targs
                then rt
                else TFunc targs (EffList [] pos) rt pos
       in bindTypeEffVar [] bt

-- | Initialize all type constructors
initTypeConDefs :: (Has EnvEff sig m) => Module -> m Module
initTypeConDefs = mapMOf (topStmts . traverse . _TDef) initTypeConDef

-- | Check the type constructor's type
checkTypeConDef :: (Has EnvEff sig m) => TypeDef -> m TypeDef
checkTypeConDef t =
  forMOf (typeCons . traverse) t $ \c -> do
    let cn = c ^. typeConName
    tt <- getEnv $ funcTypes . at cn
    forMOf _Nothing tt $ \_ ->
      throwError $
        "cannot find type constructor : " ++ cn ++ ppr (_typeLoc t)
    k <- underScope $ inferTypeKind $ fromJust tt
    checkTypeKind k
    return c

-- | Check all type constructor's types
checkTypeConDefs :: (Has EnvEff sig m) => Module -> m Module
checkTypeConDefs = mapMOf (topStmts . traverse . _TDef) checkTypeConDef

-- | Initialize type alias definitions
preInitTypeAlias :: (Has EnvEff sig m) => TypeAlias -> m TypeAlias
preInitTypeAlias t = do
  prefix <- getEnv currentModuleName
  let args = t ^. typeAliasArgs
      name = prefix ++ "/" ++ t ^. typeAliasName
      pos = _typeAliasLoc t
      star = KStar pos
      kind =
        if null args -- if no arguments, it is just a simple enum
          then star
          else KFunc (args ^.. traverse . _2 . non star) star pos
  -- check if inteface exists or not
  ot <- getEnv $ typeKinds . at name
  forMOf _Just ot $ \t ->
    throwError $
      "type alias has conflict name: " ++ name ++ " vs " ++ ppr t ++ ppr pos
  setEnv (Just kind) $ typeKinds . at name
  return t {_typeAliasName = name}

-- | Initialize all type aliases
preInitTypeAliases :: (Has EnvEff sig m) => Module -> m Module
preInitTypeAliases = mapMOf (topStmts . traverse . _TAlias) preInitTypeAlias

-- | Check type alias
initTypeAlias :: (Has EnvEff sig m) => TypeAlias -> m TypeAlias
initTypeAlias t = do
  globalTypes <- fmap s2n . M.keys <$> getEnv typeKinds
  let args = t ^.. typeAliasArgs . traverse . _1
      aliasType = _typeAliasType t
      name = t ^. typeAliasName
      b = bind (globalTypes::[TVar]) (bindTAlias t)
      fvars = (b ^.. fv) :: [TVar]
      pos = _typeAliasLoc t
  -- check if has free type variables
  when (fvars /= []) $
    throwError $
      "type alias's type variables should "
        ++ "only exists in eff type arguments: "
        ++ ppr fvars
        ++ ppr pos
  -- check if inteface exists or not
  ot <- getEnv $ typeAliases . at name
  forMOf _Just ot $ \t ->
    throwError $
      "type alias has conflict name: " ++ name ++ " vs " ++ ppr t ++ ppr pos
  setEnv (Just t) $ typeAliases . at name
  return t

-- | Initialize all effect interfaces
initTypeAliases :: (Has EnvEff sig m) => Module -> m Module
initTypeAliases = mapMOf (topStmts . traverse . _TAlias) initTypeAlias

-- | Initializa effect type definition
initEffTypeDef :: (Has EnvEff sig m) => EffectDef -> m EffectDef
initEffTypeDef e = do
  prefix <- getEnv currentModuleName
  let en = prefix ++ "/" ++ e ^. effectName
  oe <- getEnv $ effKinds . at en
  forMOf _Just oe $ \oe ->
    throwError $
      "redefine an effect: " ++ en ++ " vs " ++ ppr oe ++ ppr (_effectLoc e)
  setEnv (Just $ effKind e) $ effKinds . at en
  return e {_effectName = en}
  where
    effKind e =
      let loc = _effectLoc e
          args = e ^. effectArgs
          star = KStar loc
          estar = EKStar loc
       in if null args
            then estar
            else EKFunc (args ^.. traverse . _2 . non star) estar loc

-- | Initialize all effect type difinitions
initEffTypeDefs :: (Has EnvEff sig m) => Module -> m Module
initEffTypeDefs = mapMOf (topStmts . traverse . _EDef) initEffTypeDef

-- | Initialize effect inteface definitions
initEffIntfDef :: (Has EnvEff sig m) => EffectDef -> m EffectDef
initEffIntfDef e = do
  prefix <- getEnv currentModuleName
  globalTypes <- fmap s2n . M.keys <$> getEnv typeKinds
  globalEffTypes <- fmap s2n . M.keys <$> getEnv effKinds
  let is = e ^. effectIntfs
      en = e ^. effectName
      f = \i -> do
        let intfn = prefix ++ "/" ++ i ^. intfName
            iargs = i ^. intfArgs
            iresult = _intfResultType i
            pos = i ^. intfLoc
            tvars = i ^.. intfBoundVars .traverse._1
            evars = i ^. intfBoundEffVars
            tb = bind (globalTypes ++ tvars) (bindEDef e)
            ftvars = (tb ^.. fv) :: [TVar]
            eb = bind (globalEffTypes ++ evars) (bindEDef e)
            fevars = (eb ^.. fv) :: [EffVar]
        -- check if has free type variables
        when (ftvars /= []) $
                throwError $
                  "eff interfaces's type variables should "
                    ++ "only exists in eff type arguments: "
                    ++ ppr ftvars
                    ++ ppr (_effectLoc e)
        when (fevars /= []) $
                throwError $
                  "eff interfaces's eff type variables should "
                    ++ "only exists in eff type arguments: "
                    ++ ppr fevars
                    ++ ppr (_effectLoc e)
        addEffIntfs en intfn
        -- check if inteface exists or not
        ot <- getEnv $ funcTypes . at intfn
        forMOf _Just ot $ \t ->
          throwError $
            "eff interface has conflict name: " ++ intfn ++ " vs " ++ ppr t ++ ppr pos
        -- get effect type
        let eff = _intfEffectType i
        effs <-
          mergeEffs eff $
            if null (e ^. effectArgs)
              then EffVar (s2n $ e ^. effectName) pos
              else
                EffApp
                  (EffVar (s2n $ e ^. effectName) pos)
                  (map (`TVar` pos) $ e ^.. effectArgs . traverse . _1)
                  pos
        --  add effect type to interface's effect list
        let bt = intfType i e effs
        setEnv (Just bt) $ funcTypes . at intfn
        return i {_intfName = intfn}
  mapMOf (effectIntfs . traverse) f e
  where
    intfType i e eff =
      let iargs = i ^. intfArgs
          iresult = _intfResultType i
          intfn = i ^. intfName
          bvars = i ^. intfBoundVars
          pos = i ^. intfLoc
          tvars = e ^. effectArgs
          evars = i ^. intfBoundEffVars
       in bindTypeEffVar evars $
            bindTypeVar tvars $
              bindTypeVar bvars $ TFunc iargs eff iresult pos

-- | Initialize all effect interfaces
initEffIntfDefs :: (Has EnvEff sig m) => Module -> m Module
initEffIntfDefs = mapMOf (topStmts . traverse . _EDef) initEffIntfDef

-- | Check an effect interface
checkEffIntfDef :: (Has EnvEff sig m) => EffectDef -> m EffectDef
checkEffIntfDef e = do
  globalTypes <- fmap s2n . M.keys <$> getEnv typeKinds
  let en = e ^. effectName
      f = \i -> do
        let intfn = i ^. intfName
        t <- getEnv $ funcTypes . at intfn
        forMOf _Nothing t $ \t ->
          throwError $
            "cannot find eff interface: " ++ intfn ++ ppr (_effectLoc e)
        k <- underScope $ inferTypeKind $ fromJust t
        checkTypeKind k
        return i
  mapMOf (effectIntfs . traverse) f e

-- | Check all effect interfaces
checkEffIntfDefs :: (Has EnvEff sig m) => Module -> m Module
checkEffIntfDefs = mapMOf (topStmts . traverse . _EDef) checkEffIntfDef

-- | Initializa function definition
initFuncDef :: (Has EnvEff sig m) => FuncDef -> m FuncDef
initFuncDef f = do
  prefix <- getEnv currentModuleName
  globalTypes <- fmap s2n . M.keys <$> getEnv typeKinds
  globalEffTypes <- fmap s2n . M.keys <$> getEnv effKinds
  let pos = f ^. funcLoc
      fn = prefix ++ "/" ++ f ^. funcName
      ft = funcDefType f
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
  k <- inferTypeKind ft
  checkTypeKind k
  oft <- getEnv $ funcTypes . at fn
  forMOf _Just oft $ \oft ->
    throwError $ "function redefine: " ++ fn ++ ppr pos
  setEnv (Just ft) $ funcTypes . at fn
  setEnv (Just f{_funcName = fn}) $ funcDefs . at fn
  return f {_funcName = fn}

-- | Initialize all function definitons
initFuncDefs :: (Has EnvEff sig m) => Module -> m Module
initFuncDefs = mapMOf (topStmts . traverse . _FDef) initFuncDef

-- | Initializa function definition
addFuncDef :: (Has EnvEff sig m) =>  FuncDef -> m FuncDef
addFuncDef f = do
  let fn = f ^. funcName
  setEnv (Just f) $ funcDefs . at fn
  return f

-- | Initialize all function definitons
addFuncDefs :: (Has EnvEff sig m) => Module -> m Module
addFuncDefs = mapMOf (topStmts . traverse . _FDef) addFuncDef

-- | Check all function definitons
checkFuncDefs :: (Has EnvEff sig m) => Module -> m Module
checkFuncDefs = mapMOf (topStmts . traverse . _FDef) checkFuncDef

-- | Init a function implementation
initImplFuncDef :: (Has EnvEff sig m) => Module -> ImplFuncDef -> m ImplFuncDef
initImplFuncDef = setFuncImpl

-- | Init function implementations
initImplFuncDefs :: (Has EnvEff sig m) => Module -> m Module
initImplFuncDefs m = mapMOf (topStmts . traverse . _ImplFDef) (initImplFuncDef m) m

-- | Check a function implementation
checkImplFuncDef :: (Has EnvEff sig m) => ImplFuncDef -> m ImplFuncDef
checkImplFuncDef i = underScope $ do
  setEnv M.empty typeBinds
  setEnv M.empty kindBinds
  setEnv M.empty effTypeBinds
  setEnv M.empty effKindBinds
  let f = i ^. implFunDef
  let ft = funcDefType f
  k <- inferTypeKind ft
  checkTypeKind k
  ImplFuncDef <$> checkFuncType f

-- | Check all function implementations
checkImplFuncDefs :: (Has EnvEff sig m) => Module -> m Module
checkImplFuncDefs = mapMOf (topStmts . traverse . _ImplFDef) checkImplFuncDef

-- | Check local states
checkeLocalStates :: (Has EnvEff sig m) => Module -> m Module
checkeLocalStates m = mapMOf (topStmts . traverse . _FDef . funcExpr . _Just) checkLocalState m 
  >>= mapMOf (topStmts . traverse . _ImplFDef . implFunDef . funcExpr . _Just) checkLocalState

renameLocalVarsInExpr :: (Has EnvEff sig m) => Expr -> m Expr
renameLocalVarsInExpr = transformM rename
  where
    rename l@ELet{..} = do
      (pbinds, bbinds) <- genVarBinds _eletPattern
      return l{_eletPattern=substs pbinds _eletPattern, _eletBody=substs bbinds _eletBody}
    rename c@ECase{..} = do
      cs <- mapM (\c -> do
                    (pbinds, bbinds) <- genVarBinds (_casePattern c)
                    return c{_casePattern=substs pbinds (_casePattern c),
                             _caseExpr=substs bbinds (_caseExpr c)})
                    _ecaseBody
      return c{_ecaseBody=cs}
    rename l@ELam{..} = do
      vs <- mapM (\v -> do
                    id <- fresh
                    return (v, v ++ "_$arg" ++ show id)) (_elamArgs ^..traverse._1)
      let binds = map (\(n, nn) -> (s2n n, EVar (s2n nn) _eloc)) vs
          args = [(v ^. _2, t ^. _2) | v <- vs | t <- _elamArgs]
      return l{_elamArgs = args, _elamExpr=substs binds _elamExpr}
    rename e = return e
    genVarBinds p = do
      let vs = L.nubBy aeq (p ^.. fv :: [PVar])
      nvs <- mapM (\v -> do
                    id <- fresh
                    return (name2String v, name2String v ++ "_$tmp" ++ show id)) vs
      let pbinds = map (\(n, nn) -> (s2n n, PVar (s2n nn) (_ploc p))) nvs
          bbinds = map (\(n, nn) -> (s2n n, EVar (s2n nn) (_ploc p))) nvs
      return (pbinds, bbinds)

renameLocalVars :: (Has EnvEff sig m) => Module -> m Module
renameLocalVars m =
  mapMOf (topStmts . traverse . _FDef . funcExpr . _Just) renameLocalVarsInExpr m >>=
    mapMOf (topStmts . traverse . _ImplFDef . implFunDef . funcExpr . _Just) renameLocalVarsInExpr

-- | Remove meta annotation
removeAnn :: Expr -> Expr
removeAnn e = transform remove e
  where
    remove (EAnnMeta e _ _ _) = e
    remove (EAnn e _ _) = e
    remove e = e

-- | Remove all meta annotations
removeAnns :: Module -> Module
removeAnns m =
  over (topStmts . traverse . _FDef . funcExpr . _Just) removeAnn $
    over (topStmts . traverse . _ImplFDef . implFunDef . funcExpr . _Just) removeAnn m

-- | Rename func implementation names
convertFuncImplToFuncs :: Module -> Module
convertFuncImplToFuncs m =
  let tops = (m ^.. topStmts . traverse)
      fs =
        map
          ( \f ->
              let fn = f ^. funcName
                  ft = funcDefType f
                  n = uniqueFuncImplName fn ft
               in FDef f {_funcName = n}
          )
          (m ^.. topStmts . traverse . _ImplFDef . implFunDef)
   in m {_topStmts = tops ++ fs}

-- | Add module path for all types
addPrefixForTypes :: (Has EnvEff sig m) => Module -> m Module
addPrefixForTypes m' = do
  let m = addTypeBindings m'
  let allGlobalVars = L.nub (m ^.. fv) :: [TVar]
      allGlobalEffVars = L.nub (m ^.. fv) :: [EffVar]
      prefixes =
        L.nub $
          "" :
          (m ^. moduleName ++ "/") :
          "core/prelude/" :
          map (\i -> i ^. importPath ++ "/") (m ^. imports)
      loc = m ^. moduleLoc
  ts <- getEnv typeKinds
  es <- getEnv effKinds
  bindTs <-
    foldM
      ( \s v -> do
          vn' <- getNamePath m (name2String v)
          found <-
            filterOutAliasImports m vn'
              <$> foldM
                ( \f p -> do
                    let vn = p ++ vn'
                    case ts ^. at vn of
                      Just _ -> return $ f ++ [vn]
                      Nothing -> return f
                )
                []
                prefixes
          if null found
            then return s
            else
              if L.length found == 1
                then return $ s ++ map (\n -> (v, TVar (s2n n) loc)) found
                else throwError $ "found more than one type for " ++ ppr v ++ ppr found
      )
      []
      allGlobalVars
  bindEffs <-
    foldM
      ( \s v -> do
          vn' <- getNamePath m (name2String v)
          found <-
            filterOutAliasImports m vn'
              <$> foldM
                ( \f p -> do
                    let vn = p ++ vn'
                    case es ^. at vn of
                      Just _ -> return $ f ++ [vn]
                      Nothing -> return f
                )
                []
                prefixes
          if null found
            then return s
            else
              if L.length found == 1
                then return $ s ++ map (\n -> (v, EffVar (s2n n) loc)) found
                else throwError $ "found more than one eff type for " ++ ppr v ++ ppr found
      )
      []
      allGlobalEffVars
  return $ removeTypeBindings $ substs bindEffs $ substs bindTs m

-- | Add module path for expersions
addPrefixForExprs :: (Has EnvEff sig m) => Module -> m Module
addPrefixForExprs m' = do
  let m = addVarBindings m'
  let allGlobalVars = L.nub (m ^.. fv) :: [EVar]
      prefixes =
        L.nub $
          "" :
          (m ^. moduleName ++ "/") :
          "core/prelude/" :
          map (\i -> i ^. importPath ++ "/") (m ^. imports)
      loc = m ^. moduleLoc
  fs <- getEnv funcTypes
  binds <-
    foldM
      ( \s v -> do
          vn' <- getNamePath m (name2String v)
          found <-
            filterOutAliasImports m vn'
              <$> foldM
                ( \f p -> do
                    let vn = p ++ vn'
                    case fs ^. at vn of
                      Just _ -> return $ f ++ [vn]
                      Nothing -> return f
                )
                []
                prefixes
          if null found
            then return s
            else
              if L.length found == 1
                then return $ s ++ map (\n -> (v, EVar (s2n n) loc)) found
                else throwError $ "found more than one variable for " ++ ppr v ++ ppr found
      )
      []
      allGlobalVars
  return $ removeVarBindings $ substs binds m

-- | Finally add specalized functions into module
addSpecializedFuncs :: (Has EnvEff sig m) => Module -> m Module
addSpecializedFuncs m = do
  fs <- getEnv specializedFuncs
  return m{_topStmts=_topStmts m ++ map FDef (M.elems fs)}

convertInterfaceDefs :: Module -> Module
convertInterfaceDefs = over (topStmts . traverse) convert
  where convert :: TopStmt -> TopStmt
        convert IDef{..} = 
          let i = _idef
              loc = _interfaceLoc i
              iname = _interfaceName i
              tn = _interfaceTVar i ^. _1
              tvar = TVar tn loc
              deps = map (\n -> TApp (TVar (s2n n) loc) [tvar] loc) (_interfaceDeps i)
              intfs = map (\f -> 
                            let bvs = _intfBoundVars f
                                bes = _intfBoundEffVars f
                             in bindTypeEffVar bes $ bindTypeVar bvs $ TFunc (_intfArgs f) (_intfEffectType f) (_intfResultType f) loc) (_interfaceFuncs i)
              c = TypeCon iname (deps ++ intfs) loc
              t = TypeDef{_typeName=iname,
                          _typeArgs=[_interfaceTVar i],
                          _typeCons=[c],
                          _typeLoc=_interfaceLoc i}
            in TDef{_tdef=t}
        convert s = s

-- | Initialize a module
initModule :: Module -> Env -> Int -> Either String (Env, (Int, Module))
initModule m env id =
  run . runError . runState env . runFresh id $
    do
      setEnv (m ^. moduleName) currentModuleName
      (renameLocalVars . convertInterfaceDefs) m
      >>= initTypeDefs
      >>= initEffTypeDefs
      >>= preInitTypeAliases
      >>= addPrefixForTypes
      >>= (return . convertFuncImplToFuncs)
      >>= initTypeAliases
      >>= initTypeConDefs
      >>= initEffIntfDefs
      >>= initFuncDefs
      >>= initImplFuncDefs
      >>= addPrefixForExprs
      >>= addFuncDefs

-- | Type checking a module
checkType :: Module -> Env -> Int -> Bool -> Either String (Env, (Int, Module))
checkType m env id rmAnns =
  run . runError . runState env . runFresh id $
    do
      setEnv (m ^. moduleName) currentModuleName
      return (removeAnns m)
      >>= checkTypeConDefs
      >>= checkEffIntfDefs
      >>= checkFuncDefs
      >>= checkImplFuncDefs
      >>= addSpecializedFuncs
      >>= checkeLocalStates
      >>= (\m -> return $ if rmAnns then removeAnns m else m)
