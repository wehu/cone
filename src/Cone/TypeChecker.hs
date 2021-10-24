{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Cone.TypeChecker (initModule, checkType) where

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
  let b = bind (globalTypes :: [TVar]) (bindTypeTDef t)
      fvars = L.nubBy aeq (b ^.. fv) :: [TVar]
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
          tvars = map (\(n, t) -> (n, t, [])) (t ^. typeArgs)
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
      b = bind (globalTypes :: [TVar]) (bindTypeTAlias t)
      fvars = L.nubBy aeq (b ^.. fv) :: [TVar]
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
            tvars = i ^.. intfBoundVars . traverse . _1
            evars = i ^. intfBoundEffVars
            tb = bind (globalTypes ++ tvars) (bindTypeEDef e)
            ftvars = L.nubBy aeq (tb ^.. fv) :: [TVar]
            eb = bind (globalEffTypes ++ evars) (bindTypeEDef e)
            fevars = L.nubBy aeq (eb ^.. fv) :: [EffVar]
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
          tvars = map (\(n, t) -> (n, t, [])) (e ^. effectArgs)
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
      bt = bind (globalTypes :: [TVar]) (bindTypeFDef f)
      be = bind (globalEffTypes :: [EffVar]) (bindTypeFDef f)
      ftvars = L.nubBy aeq (bt ^.. fv) :: [TVar]
      fevars = L.nubBy aeq (be ^.. fv) :: [EffVar]
  -- check if has free type variables
  when (ftvars /= []) $
    throwError $
      "function type variables should "
        ++ "only exists in function type arguments: "
        ++ ppr ftvars
        ++ ppr (_funcLoc f)
  when (fevars /= []) $
    throwError $
      "function eff type variables should "
        ++ "only exists in function eff type arguments: "
        ++ ppr fevars
        ++ ppr (_funcLoc f)
  k <- inferTypeKind ft
  checkTypeKind k
  oft <- getEnv $ funcTypes . at fn
  forMOf _Just oft $ \oft ->
    throwError $ "function redefine: " ++ fn ++ ppr pos
  setEnv (Just ft) $ funcTypes . at fn
  --fBody <- mapMOf _Just (addImplicitVars (_funcBoundVars f) (_funcArgs f)) (_funcExpr f)
  --fBody <- transformMOn _Just addImplicitVarsForLam fBody
  let f' = f {_funcName = fn {-, _funcExpr = fBody-}}
  setEnv (Just f') $ funcDefs . at fn
  return f'

--where addImplicitVars bvs args e = do
--        let pos = _eloc e
--        (r, _) <- foldM
--          ( \(s, i) (v, _, cs) -> do
--              foldM
--                ( \(s, i) c -> do
--                    let cn = name2String $ _tvar c
--                    intfs <- getEnv $ intfFuncs . at cn
--                    when (isn't _Just intfs) $
--                      throwError $ "cannot find interface " ++ cn ++ ppr pos
--                    let p = PApp (EVar (s2n cn) pos) [] (map (\n -> PVar (s2n $ n ++ "_$" ++ name2String v) pos) $ fromJust intfs) pos
--                    return (ELet p (EVar (s2n $ args !! i ^. _1) pos) s False pos, i + 1)
--                )
--                (s, i)
--                cs
--          )
--          (e, 0)
--          bvs
--        return r
--      addImplicitVarsForLam l@ELam{..} = do
--        b <- mapMOf _Just (addImplicitVars _elamBoundVars _elamArgs) _elamExpr
--        return l{_elamExpr = b}
--      addImplicitVarsForLam e = return e

-- | Initialize all function definitons
initFuncDefs :: (Has EnvEff sig m) => Module -> m Module
initFuncDefs = mapMOf (topStmts . traverse . _FDef) initFuncDef

-- | Initializa function definition
addFuncDef :: (Has EnvEff sig m) => FuncDef -> m FuncDef
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
  --setEnv M.empty typeBinds
  --setEnv M.empty kindBinds
  --setEnv M.empty effTypeBinds
  --setEnv M.empty effKindBinds
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
checkeLocalStates m =
  mapMOf (topStmts . traverse . _FDef . funcExpr . _Just) checkLocalState m
    >>= mapMOf (topStmts . traverse . _ImplFDef . implFunDef . funcExpr . _Just) checkLocalState

renameLocalVarsInExpr :: (Has EnvEff sig m) => Expr -> m Expr
renameLocalVarsInExpr = transformM rename
  where
    rename l@ELet {..} = do
      (pbinds, bbinds) <- genVarBinds _eletPattern
      return l {_eletPattern = substs pbinds _eletPattern, _eletBody = substs bbinds _eletBody}
    rename c@ECase {..} = do
      cs <-
        mapM
          ( \c -> do
              (pbinds, bbinds) <- genVarBinds (_casePattern c)
              return
                c
                  { _casePattern = substs pbinds (_casePattern c),
                    _caseExpr = substs bbinds (_caseExpr c)
                  }
          )
          _ecaseBody
      return c {_ecaseBody = cs}
    rename l@ELam {..} = do
      vs <-
        mapM
          ( \v -> do
              id <- fresh
              return (v, v ++ "_$arg" ++ show id)
          )
          (_elamArgs ^.. traverse . _1)
      let binds = map (\(n, nn) -> (s2n n, EVar (s2n nn) _eloc)) vs
          args = [(v ^. _2, t ^. _2) | v <- vs | t <- _elamArgs]
      return l {_elamArgs = args, _elamExpr = substs binds _elamExpr}
    rename e = return e
    genVarBinds p = do
      let vs = L.nubBy aeq (p ^.. fv :: [PVar])
      nvs <-
        mapM
          ( \v -> do
              id <- fresh
              return (name2String v, name2String v ++ "_$tmp" ++ show id)
          )
          vs
      let pbinds = map (\(n, nn) -> (s2n n, PVar (s2n nn) (_ploc p))) nvs
          bbinds = map (\(n, nn) -> (s2n n, EVar (s2n nn) (_ploc p))) nvs
      return (pbinds, bbinds)

renameLocalVars :: (Has EnvEff sig m) => Module -> m Module
renameLocalVars m =
  mapMOf (topStmts . traverse . _FDef . funcExpr . _Just) renameLocalVarsInExpr m
    >>= mapMOf (topStmts . traverse . _ImplFDef . implFunDef . funcExpr . _Just) renameLocalVarsInExpr

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
  return m {_topStmts = _topStmts m ++ map FDef (M.elems fs)}

convertInterfaceDefs :: (Has EnvEff sig m) => Module -> m Module
convertInterfaceDefs m = do
  prefix <- getEnv currentModuleName
  let is = m ^.. topStmts . traverse . _IDef
  intfs <- mapM (convert prefix) is
  return m {_topStmts = [s | s <- _topStmts m, isn't _IDef s] ++ join intfs}
  where
    convert prefix InterfaceDef {..} = do
      let i = _idef
          loc = _interfaceLoc
          iname = _interfaceName
          tn = _interfaceTVar ^. _1
          tvar = TVar tn loc
      -- deps = map (\n -> TApp n [tvar] loc) _interfaceDeps
      intfs <-
        mapM
          ( \f -> do
              fiArgs <-
                mapM
                  ( \t -> do
                      id <- fresh
                      let n = "__arg_$" ++ show id
                      return (n, t)
                  )
                  (_intfArgs f)
              let bvs = (_interfaceTVar ^. _1, _interfaceTVar ^. _2, []) : _intfBoundVars f
                  bes = _intfBoundEffVars f
                  args = join $ map (\(n, _, cs) -> [TApp c [TVar n loc] loc | c <- cs]) (_intfBoundVars f)
                  ft =
                    bindTypeEffVar bes $
                      bindTypeVar bvs $
                        TFunc (args ++ _intfArgs f) (_intfEffectType f) (_intfResultType f) (_intfLoc f)
                  fi =
                    FuncDef
                      { _funcName = _intfName f,
                        _funcBoundVars = (_interfaceTVar ^. _1, _interfaceTVar ^. _2, []) : bvs,
                        _funcBoundEffVars = bes,
                        _funcArgs = fiArgs,
                        _funcEffectType = _intfEffectType f,
                        _funcResultType = _intfResultType f,
                        _funcExpr = Nothing,
                        _funcLoc = _intfLoc f
                      }
               in return (ft, fi, _intfName f)
          )
          (L.sortBy (\a b -> _intfName a `compare` _intfName b) _interfaceFuncs)
      let c = TypeCon iname {-deps ++ -} (intfs ^.. traverse . _1) loc
          t =
            TypeDef
              { _typeName = iname,
                _typeArgs = [_interfaceTVar],
                _typeCons = [c],
                _typeLoc = _interfaceLoc
              }
          placeHolder =
            FuncDef
              { _funcName = iname ++ "_$dict",
                _funcBoundVars = [(_interfaceTVar ^. _1, _interfaceTVar ^. _2, [])],
                _funcBoundEffVars = [],
                _funcArgs = [],
                _funcEffectType = EffList [] loc,
                _funcResultType = TApp (TVar (s2n iname) loc) [tvar] loc,
                _funcExpr = Nothing,
                _funcLoc = loc
              }
          impls =
            L.foldl'
              ( \(s, i) (ft, _, fn) ->
                  (s ++ [(fn, ft, i, bind [tn] (tvar, ft))], i + 1)
              )
              ([], 0 :: Int)
              intfs
      setEnv (Just $ impls ^. _1) $ intfFuncs . at (prefix ++ "/" ++ iname)
      forM_ _interfaceFuncs $ \intf -> do
        let n = prefix ++ "/" ++ intf ^. intfName
        oldImpls <- getEnv $ intfImpls . at n . non []
        setEnv (Just oldImpls) $ intfImpls . at n
      oldCntrs <- getEnv $ intfCntrs . at (prefix ++ "/" ++ iname ++ "_$dict") . non []
      setEnv (Just oldCntrs) $ intfCntrs . at (prefix ++ "/" ++ iname ++ "_$dict")
      return $ TDef {_tdef = t} : FDef {_fdef = placeHolder} : map FDef (intfs ^.. traverse . _2)
    convert prefix BoundInterfaceDef {..} =
      let (_, b) = unsafeUnbind _boundInterfaceDef
       in convert prefix b

convertImplInterfaceDefs :: Module -> Module
convertImplInterfaceDefs m =
  let implIntfs = m ^.. topStmts . traverse . _ImplIDef
      intfs = map convert implIntfs
   in m {_topStmts = _topStmts m ++ intfs}
  where
    convert ImplInterfaceDef {..} =
      let loc = _implInferfaceLoc
          iname = _implInterfaceDefName
          t = _implInterfaceDefType
          bvs = _implInterfaceBoundVars
          intfs =
            map
              ( \f ->
                  ELam (_funcBoundVars f) (_funcBoundEffVars f) (_funcArgs f) (_funcEffectType f) (_funcResultType f) (_funcExpr f) loc
              )
              (L.sortBy (\a b -> _funcName a `compare` _funcName b) _implInterfaceDefFuncs)
          c = EApp False (EVar (s2n iname) loc) [t] intfs loc
          dict = uniqueFuncImplName (iname ++ "_$dict") t
       in FDef $ FuncDef dict bvs [] [] (EffList [] loc) (TApp (TVar (s2n iname) loc) [t] loc) (Just c) loc
    convert BoundImplInterfaceDef {..} =
      let (_, b) = unsafeUnbind _boundImplInterfaceDef
       in convert b

addImplicitArgs :: Module -> Module
addImplicitArgs m =
  over (topStmts . traverse . _FDef) convert $
    over (topStmts . traverse . _ImplFDef . implFunDef) convert m
  where
    convert f@FuncDef {..} =
      let loc = _funcLoc
          args = join $ map (\(n, _, cs) -> [("____implicit_$" ++ name2String n, TApp c [TVar n loc] loc) | c <- cs]) _funcBoundVars
          e = fmap (transform convertLam) _funcExpr
       in f {_funcArgs = args ++ _funcArgs, _funcExpr = e}
      where
        convertLam l@ELam {..} =
          let loc = _eloc
              args = join $ map (\(n, _, cs) -> [("____implicit_$" ++ name2String n, TApp c [TVar n loc] loc) | c <- cs]) _elamBoundVars
           in l {_elamArgs = args ++ _elamArgs}
        convertLam e = e
    convert BoundFuncDef {..} =
      let (_, b) = unsafeUnbind _boundFuncDef
       in convert b
    convert BoundEffFuncDef {..} =
      let (_, b) = unsafeUnbind _boundEffFuncDef
       in convert b

initIntfImpls :: (Has EnvEff sig m) => Module -> m Module
initIntfImpls m = transformMOn (topStmts . traverse . _ImplIDef) initIntfImpl m
  where
    initIntfImpl i@ImplInterfaceDef {..} = do
      prefix <- getEnv currentModuleName
      let iname = _implInterfaceDefName
          loc = _implInterfaceLoc i
          t = _implInterfaceDefType
      intf <- searchInterface m iname loc
      funcNames' <- getEnv $ intfFuncs . at intf
      when (isn't _Just funcNames') $
        throwError $ "cannot find interface " ++ ppr intf ++ ppr loc
      let implFuncNames = L.sort $ _implInterfaceDefFuncs ^.. traverse . funcName
          funcNames = fromJust funcNames' ^.. traverse . _1
      when (funcNames /= implFuncNames) $
        throwError $ "interface implementation function mismatch: " ++ ppr funcNames ++ " vs " ++ ppr implFuncNames
      let intfPrefix = join $ L.intersperse "/" $ init $ splitOn "/" intf
          intfT = TApp (TVar (s2n intf) loc) [t] loc
          impls =
            L.foldl'
              ( \(s, i) f ->
                 let ft = TFunc (_funcArgs f ^.. traverse . _2) (_funcEffectType f) (_funcResultType f) (_funcLoc f)
                  in ( ( intfPrefix ++ "/" ++ _funcName f,
                      ( prefix ++ "/" ++ uniqueFuncImplName (iname ++ "_$dict") t,
                        bindTypeEffVar (_funcBoundEffVars f) $
                          bindTypeVar (_implInterfaceBoundVars ++ _funcBoundVars f) ft,
                        i,
                        bind (_implInterfaceBoundVars ^.. traverse . _1) (intfT, ft)
                      )
                    ) :
                    s,
                    i + 1
                  )
              )
              ([], 0)
              _implInterfaceDefFuncs
          cntr =
            ( prefix ++ "/" ++ uniqueFuncImplName (iname ++ "_$dict") t,
              bindTypeEffVar [] $
                bindTypeVar _implInterfaceBoundVars intfT,
              0,
              bind (_implInterfaceBoundVars ^.. traverse . _1) (intfT, intfT)
            )
      forM_ (impls ^. _1) $ \(intf, impl) -> do
        oldImpls <- getEnv $ intfImpls . at intf . non []
        setEnv (Just $ impl : oldImpls) $ intfImpls . at intf
      oldCntrs <- getEnv $ intfCntrs . at (intf ++ "_$dict") . non []
      setEnv (Just $ cntr : oldCntrs) $ intfCntrs . at (intf ++ "_$dict")
      return i
    initIntfImpl i = return i

selectIntfs :: (Has EnvEff sig m) => Module -> m Module
selectIntfs = mapMOf (topStmts . traverse . _FDef) selectIntfForFunc

-- | Initialize a module
initModule :: Module -> Env -> Int -> Either String (Env, (Int, Module))
initModule m env id =
  run . runError . runState env . runFresh id $
    do
      setEnv (m ^. moduleName) currentModuleName
      convertInterfaceDefs m
      >>= initTypeDefs
      >>= initEffTypeDefs
      >>= preInitTypeAliases
      >>= addPrefixForTypes
      >>= (renameLocalVars . addImplicitArgs . convertImplInterfaceDefs . convertFuncImplToFuncs)
      >>= addPrefixForTypes
      >>= initTypeAliases
      >>= initTypeConDefs
      >>= initEffIntfDefs
      >>= initFuncDefs
      >>= initImplFuncDefs
      >>= addPrefixForExprs
      >>= addFuncDefs
      >>= initIntfImpls

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
      >>= selectIntfs
      >>= addSpecializedFuncs
      >>= checkeLocalStates
      >>= (\m -> return $ if rmAnns then removeAnns m else m)
