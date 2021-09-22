{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}

module Cone.TypeChecker (Env (..), types, funcs, effs, effIntfs, funcImpls, initialEnv, initModule, checkType) where

import Cone.Parser.AST
import Cone.TypeChecker.Env
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
  return t {_typeName = tn}
  where
    typeKindOf t =
      let loc = _typeLoc t
          args = t ^. typeArgs
          star = KStar loc
          num = KNum loc
          resK = case (t ^. typeName) of
            "neg" -> num
            "add" -> num
            "sub" -> num
            "mul" -> num
            "div" -> num
            "mod" -> num
            "max" -> num
            "min" -> num
            _ -> star
       in if args == [] -- if no arguments, it is just a simple enum
            then star
            else KFunc (args ^.. traverse . _2 . non star) resK loc

-- | Initialize all type definitions
initTypeDefs :: (Has EnvEff sig m) => Module -> m Module
initTypeDefs m = mapMOf (topStmts . traverse . _TDef) (initTypeDef $ m ^. moduleName) m

-- | Initialize a constructor in type definition
initTypeConDef :: (Has EnvEff sig m) => String -> TypeDef -> m TypeDef
initTypeConDef prefix t = do
  globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
  mapMOf
    (typeCons . traverse)
    ( \c -> do
        let cn = prefix ++ "/" ++ c ^. typeConName
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
            if tvars == []
              then TVar (s2n tn) pos
              else TApp (TVar (s2n tn) pos) (fmap (\t -> TVar (t ^. _1) pos) tvars) pos
          bt =
            bindTypeVar tvars $
              if targs == []
                then rt
                else TFunc targs (EffList [] pos) rt pos
       in bindTypeEffVar [] bt

-- | Initialize all type constructors
initTypeConDefs :: (Has EnvEff sig m) => Module -> m Module
initTypeConDefs m = mapMOf (topStmts . traverse . _TDef) (initTypeConDef $ m ^. moduleName) m

-- | Check the type constructor's type
checkTypeConDef :: (Has EnvEff sig m) => TypeDef -> m TypeDef
checkTypeConDef t =
  forMOf (typeCons . traverse) t $ \c -> do
    let cn = c ^. typeConName
    tt <- getEnv $ funcs . at cn
    forMOf _Nothing tt $ \_ ->
      throwError $
        "cannot find type constructor : " ++ cn ++ (ppr $ _typeLoc t)
    k <- underScope $ inferTypeKind $ fromJust tt
    checkTypeKind k
    return c

-- | Check all type constructor's types
checkTypeConDefs :: (Has EnvEff sig m) => Module -> m Module
checkTypeConDefs m = mapMOf (topStmts . traverse . _TDef) checkTypeConDef m

-- | Initializa effect type definition
initEffTypeDef :: (Has EnvEff sig m) => String -> EffectDef -> m EffectDef
initEffTypeDef prefix e = do
  let en = prefix ++ "/" ++ e ^. effectName
  oe <- getEnv $ effs . at en
  forMOf _Just oe $ \oe ->
    throwError $
      "redefine an effect: " ++ en ++ " vs " ++ ppr oe ++ (ppr $ _effectLoc e)
  setEnv (Just $ effKind e) $ effs . at en
  return e {_effectName = en}
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
initEffTypeDefs m = mapMOf (topStmts . traverse . _EDef) (initEffTypeDef $ m ^. moduleName) m

-- | Initialize effect inteface definitions
initEffIntfDef :: (Has EnvEff sig m) => String -> EffectDef -> m EffectDef
initEffIntfDef prefix e = do
  globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
  let is = e ^. effectIntfs
      en = e ^. effectName
      f = \i -> do
        let intfn = prefix ++ "/" ++ i ^. intfName
            iargs = i ^. intfArgs
            iresult = _intfResultType i
            pos = i ^. intfLoc
            bvars = (i ^.. intfBoundVars . traverse . _1)
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
                ++ ppr fvars
                ++ ppr pos
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
            if e ^. effectArgs == []
              then EffVar (s2n $ e ^. effectName) pos
              else
                EffApp
                  (EffVar (s2n $ e ^. effectName) pos)
                  (map (\v -> TVar v pos) $ e ^.. effectArgs . traverse . _1)
                  pos
        --  add effect type to interface's effect list
        let bt = intfType i e effs
        setEnv (Just bt) $ funcs . at intfn
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
initEffIntfDefs m = mapMOf (topStmts . traverse . _EDef) (initEffIntfDef $ m ^. moduleName) $ m

-- | Check an effect interface
checkEffIntfDef :: (Has EnvEff sig m) => EffectDef -> m EffectDef
checkEffIntfDef e = do
  globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
  let en = e ^. effectName
      f = \i -> do
        let intfn = i ^. intfName
        t <- getEnv $ funcs . at intfn
        forMOf _Nothing t $ \t ->
          throwError $
            "cannot find eff interface: " ++ intfn ++ ppr (_effectLoc e)
        k <- underScope $ inferTypeKind $ fromJust t
        checkTypeKind k
        return i
  mapMOf (effectIntfs . traverse) f e

-- | Check all effect interfaces
checkEffIntfDefs :: (Has EnvEff sig m) => Module -> m Module
checkEffIntfDefs m = mapMOf (topStmts . traverse . _EDef) checkEffIntfDef m

-- | Initializa function definition
initFuncDef :: (Has EnvEff sig m) => String -> FuncDef -> m FuncDef
initFuncDef prefix f = do
  let pos = f ^. funcLoc
      fn = prefix ++ "/" ++ f ^. funcName
      ft = funcDefType f
  k <- inferTypeKind ft
  checkTypeKind k
  oft <- getEnv $ funcs . at fn
  forMOf _Just oft $ \oft ->
    throwError $ "function redefine: " ++ fn ++ ppr pos
  setEnv (Just ft) $ funcs . at fn
  return f {_funcName = fn}

-- | Initialize all function definitons
initFuncDefs :: (Has EnvEff sig m) => Module -> m Module
initFuncDefs m = mapMOf (topStmts . traverse . _FDef) (initFuncDef $ m ^. moduleName) m

-- | Check a function type
checkFuncType :: (Has EnvEff sig m) => FuncDef -> m FuncDef
checkFuncType f = underScope $ do
  let pos = f ^. funcLoc
      star = KStar pos
      btvars = fmap (\t -> (name2String (t ^. _1), t ^. _2 . non star)) $ f ^. funcBoundVars
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
      effType <- inferExprEffType eWithType
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

-- | Check all function definitons
checkFuncDefs :: (Has EnvEff sig m) => Module -> m Module
checkFuncDefs m = mapMOf (topStmts . traverse . _FDef) checkFuncDef m

-- | Init a function implementation
initImplFuncDef :: (Has EnvEff sig m) => String -> ImplFuncDef -> m ImplFuncDef
initImplFuncDef prefix f = setFuncImpl prefix f

-- | Init function implementations
initImplFuncDefs :: (Has EnvEff sig m) => Module -> m Module
initImplFuncDefs m = mapMOf (topStmts . traverse . _ImplFDef) (initImplFuncDef $ m ^. moduleName) m

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
checkImplFuncDefs m = mapMOf (topStmts . traverse . _ImplFDef) checkImplFuncDef m

-- | Remove meta annotation
removeAnn :: Expr -> Expr
removeAnn e = transform remove e
  where
    remove (EAnnMeta e _ _) = e
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

-- | Add type bindings
addTypeBindings :: Module -> Module
addTypeBindings m =
  over (topStmts . traverse . _EDef) bindEDef $
    over (topStmts . traverse . _TDef) bindTDef $
      over (topStmts . traverse . _FDef) bindFDef $
        over (topStmts . traverse . _ImplFDef . implFunDef) bindFDef m
  where
    bindEDef edef =
      let boundVars = L.nub $ edef ^.. effectArgs . traverse
          edef' = over (effectIntfs . traverse) (bindEffIntf boundVars) edef
       in BoundEffectDef (bind (boundVars ^.. traverse . _1) edef') (_effectLoc edef)
    bindEffIntf bvs intf =
      let boundVars = L.nub $ bvs ++ intf ^. intfBoundVars
          boundEffVars = L.nub $ intf ^. intfBoundEffVars
          loc = intf ^. intfLoc
       in BoundEffFuncIntf (bind boundEffVars $ BoundFuncIntf (bind (boundVars ^.. traverse . _1) intf) loc) loc
    bindTDef tdef =
      let boundVars = L.nub $ tdef ^.. typeArgs . traverse . _1
       in BoundTypeDef (bind boundVars tdef) (_typeLoc tdef)
    bindFDef fdef =
      let boundVars = L.nub $ fdef ^. funcBoundVars
          boundEffVars = L.nub $ fdef ^. funcBoundEffVars
          loc = fdef ^. funcLoc
          expr = fmap (transform bindExpr) $ _funcExpr fdef
       in BoundEffFuncDef (bind boundEffVars $ BoundFuncDef (bind (boundVars ^.. traverse . _1) fdef {_funcExpr = expr}) loc) loc
    bindExpr l@ELam {..} =
      let boundVars = L.nub $ _elamBoundVars
          boundEffVars = L.nub $ _elamBoundEffVars
       in l
            { _elamExpr =
                fmap
                  ( \e ->
                      EBoundEffTypeVars (bind boundEffVars $ EBoundTypeVars (bind (boundVars ^.. traverse . _1) e) _eloc) _eloc
                  )
                  _elamExpr
            }
    bindExpr expr = expr

-- | Remove type bindings
removeTypeBindings :: Module -> Module
removeTypeBindings m =
  over (topStmts . traverse . _EDef) removeBindingsForEDef $
    over (topStmts . traverse . _TDef) removeBindingsForTDef $
      over (topStmts . traverse . _FDef) removeBindingsForFDef $
        over (topStmts . traverse . _ImplFDef . implFunDef) removeBindingsForFDef m
  where
    removeBindingsForEDef (BoundEffectDef b _) =
      let (_, e) = unsafeUnbind b
       in removeBindingsForEDef e
    removeBindingsForEDef e =
      over (effectIntfs . traverse) removeBindingsForIntf e
    removeBindingsForIntf (BoundFuncIntf b _) =
      let (_, i) = unsafeUnbind b
       in removeBindingsForIntf i
    removeBindingsForIntf (BoundEffFuncIntf b _) =
      let (_, i) = unsafeUnbind b
       in removeBindingsForIntf i
    removeBindingsForIntf intf = intf
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
      let expr = fmap removeBindingsForExpr $ _funcExpr fdef
       in fdef {_funcExpr = expr}
    removeBindingsForExpr (EBoundTypeVars b _) =
      let (_, e) = unsafeUnbind b
       in removeBindingsForExpr e
    removeBindingsForExpr (EBoundEffTypeVars b _) =
      let (_, e) = unsafeUnbind b
       in removeBindingsForExpr e
    removeBindingsForExpr l@ELam {..} =
      l {_elamExpr = fmap removeBindingsForExpr _elamExpr}
    removeBindingsForExpr e@ECase {..} =
      e
        { _ecaseExpr = removeBindingsForExpr _ecaseExpr,
          _ecaseBody = over traverse removeBindingsForCase _ecaseBody
        }
    removeBindingsForExpr w@EWhile {..} =
      w
        { _ewhileCond = removeBindingsForExpr _ewhileCond,
          _ewhileBody = removeBindingsForExpr _ewhileBody
        }
    removeBindingsForExpr a@EApp {..} =
      a
        { _eappFunc = removeBindingsForExpr _eappFunc,
          _eappArgs = over traverse removeBindingsForExpr _eappArgs
        }
    removeBindingsForExpr l@ELet {..} =
      l
        { _eletExpr = removeBindingsForExpr _eletExpr,
          _eletPattern = removeBindingsForPattern _eletPattern,
          _eletBody = removeBindingsForExpr _eletBody
        }
    removeBindingsForExpr h@EHandle {..} =
      h
        { _ehandleScope = removeBindingsForExpr _ehandleScope,
          _ehandleBindings = map removeBindingsForFDef _ehandleBindings
        }
    removeBindingsForExpr s@ESeq {..} =
      s {_eseq = map removeBindingsForExpr _eseq}
    removeBindingsForExpr e@EAnn {..} =
      e {_eannExpr = removeBindingsForExpr _eannExpr}
    removeBindingsForExpr e@EAnnMeta {..} =
      e {_eannMetaExpr = removeBindingsForExpr _eannMetaExpr}
    removeBindingsForExpr expr = expr
    removeBindingsForPattern p@PExpr {..} =
      p {_pExpr = removeBindingsForExpr _pExpr}
    removeBindingsForPattern p = p
    removeBindingsForCase c@Case {..} =
      c
        { _caseExpr = removeBindingsForExpr _caseExpr,
          _casePattern = removeBindingsForPattern _casePattern
        }

-- | Get real name if there is alias prefix
getNamePath :: (Has EnvEff sig m) => Module -> String -> m String
getNamePath m n = do
  let aliases =
        L.foldl'
          ( \s i ->
              case i ^. importAlias of
                Just alias -> s & at alias ?~ i ^. importPath
                Nothing -> s
          )
          M.empty
          $ m ^. imports
      n' = last $ splitOn "/" n
      ns = join $ L.intersperse "/" $ L.init $ splitOn "/" n
  case aliases ^. at ns of
    Just prefix -> return $ prefix ++ "/" ++ n'
    Nothing -> return n

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
          (map (\i -> i ^. importPath ++ "/") $ m ^. imports)
      loc = m ^. moduleLoc
  ts <- getEnv types
  es <- getEnv effs
  bindTs <-
    foldM
      ( \s v -> do
          vn' <- getNamePath m (name2String v)
          found <-
            foldM
              ( \f p -> do
                  let vn = p ++ vn'
                  case ts ^. at vn of
                    Just _ -> return $ f ++ [(v, TVar (s2n vn) loc)]
                    Nothing -> return f
              )
              []
              prefixes
          if found == []
            then return s
            else
              if L.length found == 1
                then return $ s ++ found
                else throwError $ "found more than one type for " ++ ppr v ++ ppr found
      )
      []
      allGlobalVars
  bindEffs <-
    foldM
      ( \s v -> do
          vn' <- getNamePath m (name2String v)
          found <-
            foldM
              ( \f p -> do
                  let vn = p ++ vn'
                  case es ^. at vn of
                    Just _ -> return $ f ++ [(v, EffVar (s2n vn) loc)]
                    Nothing -> return f
              )
              []
              prefixes
          if found == []
            then return s
            else
              if L.length found == 1
                then return $ s ++ found
                else throwError $ "found more than one eff type for " ++ ppr v ++ ppr found
      )
      []
      allGlobalEffVars
  return $ removeTypeBindings $ substs bindEffs $ substs bindTs m

-- | Add variable bindings
addVarBindings :: Module -> Module
addVarBindings m =
  over (topStmts . traverse . _FDef) bindFDef $
    over (topStmts . traverse . _ImplFDef . implFunDef) bindFDef m
  where
    bindFDef fdef =
      let boundVars = map s2n $ L.nub $ fdef ^.. funcArgs . traverse . _1
          loc = fdef ^. funcLoc
          expr = fmap (transform bindExpr) $ _funcExpr fdef
       in fdef {_funcExpr = fmap (\e -> EBoundVars (bind boundVars e) loc) expr}
    bindExpr l@ELam {..} =
      let boundVars = map s2n $ L.nub $ _elamArgs ^.. traverse . _1
          loc = _eloc
       in l {_elamExpr = fmap (\e -> EBoundVars (bind boundVars e) loc) _elamExpr}
    bindExpr l@ELet {..} =
      let vs = map (s2n . name2String) ((l ^.. fv) :: [PVar])
       in EBoundVars (bind vs l) _eloc
    bindExpr c@ECase {..} =
      let ps =
            map
              ( \p ->
                  let vs = map (s2n . name2String) ((p ^.. fv) :: [PVar])
                   in BoundCase (bind vs p) (_caseLoc p)
              )
              _ecaseBody
       in c {_ecaseBody = ps}
    bindExpr expr = expr

-- | Remove variable bindings
removeVarBindings :: Module -> Module
removeVarBindings m =
  over (topStmts . traverse . _FDef . funcExpr . _Just) removeBindingsForExpr $
    over (topStmts . traverse . _ImplFDef . implFunDef . funcExpr . _Just) removeBindingsForExpr m
  where
    removeBindingsForExpr (EBoundVars b _) =
      let (_, e) = unsafeUnbind b
       in removeBindingsForExpr e
    removeBindingsForExpr l@ELam {..} =
      l {_elamExpr = fmap removeBindingsForExpr _elamExpr}
    removeBindingsForExpr e@ECase {..} =
      e
        { _ecaseExpr = removeBindingsForExpr _ecaseExpr,
          _ecaseBody = over traverse removeBindingsForCase _ecaseBody
        }
    removeBindingsForExpr w@EWhile {..} =
      w
        { _ewhileCond = removeBindingsForExpr _ewhileCond,
          _ewhileBody = removeBindingsForExpr _ewhileBody
        }
    removeBindingsForExpr a@EApp {..} =
      a
        { _eappFunc = removeBindingsForExpr _eappFunc,
          _eappArgs = over traverse removeBindingsForExpr _eappArgs
        }
    removeBindingsForExpr l@ELet {..} =
      l
        { _eletExpr = removeBindingsForExpr _eletExpr,
          _eletPattern = removeBindingsForPattern _eletPattern,
          _eletBody = removeBindingsForExpr _eletBody
        }
    removeBindingsForExpr h@EHandle {..} =
      h
        { _ehandleScope = removeBindingsForExpr _ehandleScope,
          _ehandleBindings = over (traverse . funcExpr . _Just) removeBindingsForExpr _ehandleBindings
        }
    removeBindingsForExpr s@ESeq {..} =
      s {_eseq = map removeBindingsForExpr _eseq}
    removeBindingsForExpr e@EAnn {..} =
      e {_eannExpr = removeBindingsForExpr _eannExpr}
    removeBindingsForExpr e@EAnnMeta {..} =
      e {_eannMetaExpr = removeBindingsForExpr _eannMetaExpr}
    removeBindingsForExpr expr = expr
    removeBindingsForPattern p@PExpr {..} =
      p {_pExpr = removeBindingsForExpr _pExpr}
    removeBindingsForPattern p = p
    removeBindingsForCase BoundCase {..} =
      let (_, c) = unsafeUnbind _boundCase
       in removeBindingsForCase c
    removeBindingsForCase c@Case {..} =
      c
        { _caseExpr = removeBindingsForExpr _caseExpr,
          _casePattern = removeBindingsForPattern _casePattern
        }

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
          (map (\i -> i ^. importPath ++ "/") $ m ^. imports)
      loc = m ^. moduleLoc
  fs <- getEnv funcs
  binds <-
    foldM
      ( \s v -> do
          vn' <- getNamePath m (name2String v)
          found <-
            foldM
              ( \f p -> do
                  let vn = p ++ vn'
                  case fs ^. at vn of
                    Just _ -> return $ f ++ [(v, EVar (s2n vn) loc)]
                    Nothing -> return f
              )
              []
              prefixes
          if found == []
            then return s
            else
              if L.length found == 1
                then return $ s ++ found
                else throwError $ "found more than one variable for " ++ ppr v ++ ppr found
      )
      []
      allGlobalVars
  return $ removeVarBindings $ substs binds m

-- | Initialize a module
initModule :: Module -> Env -> Int -> Either String (Env, (Int, Module))
initModule m env id =
  run . runError . (runState env) . runFresh id $
    do
      (return $ convertFuncImplToFuncs m)
      >>= initTypeDefs
      >>= initEffTypeDefs
      >>= addPrefixForTypes
      >>= initTypeConDefs
      >>= initEffIntfDefs
      >>= initFuncDefs
      >>= initImplFuncDefs
      >>= addPrefixForExprs

-- | Type checking a module
checkType :: Module -> Env -> Int -> Either String (Env, (Int, Module))
checkType m env id =
  run . runError . (runState env) . runFresh id $
    do
      return m
      >>= checkTypeConDefs
      >>= checkEffIntfDefs
      >>= checkFuncDefs
      >>= checkImplFuncDefs
      >>= (return . removeAnns)
