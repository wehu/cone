{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}

module Cone.TypeChecker (Env (..), types, funcs, effs, initialEnv, initModule, checkType) where

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

initTypeDef :: (Has EnvEff sig m) => TypeDef -> m ()
initTypeDef t = do
  let tn = t ^. typeName
  ot <- getEnv $ types . at tn
  forMOf _Just ot $ \ot ->
    throwError $
      "redefine a type: " ++ tn ++ " vs " ++ ppr ot ++ (ppr $ _typeLoc t)
  let k = Just $ typeKindOf t
  setEnv k $ types . at tn
  where
    typeKindOf t =
      let loc = _typeLoc t
          args = t ^. typeArgs
          star = KStar loc
       in if args == []
            then star
            else KFunc (args ^.. traverse . _2 . non star) star loc

initTypeDefs :: (Has EnvEff sig m) => Module -> m ()
initTypeDefs m = mapM_ initTypeDef $ m ^.. topStmts . traverse . _TDef

initTypeConDef :: (Has EnvEff sig m) => TypeDef -> m ()
initTypeConDef t = do
  globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
  forM_ (t ^. typeCons) $ \c -> do
    let cn = c ^. typeConName
        cargs = c ^. typeConArgs
        pos = c ^. typeConLoc
        targs = (t ^.. typeArgs . traverse . _1) ++ globalTypes
        b = bind targs cargs
        fvars = (b ^.. fv) :: [TVar]
    if fvars /= []
      then
        throwError $
          "type constructor's type variables should "
            ++ "only exists in type arguments: "
            ++ ppr fvars
      else return ()
    ot <- getEnv $ funcs . at cn
    forMOf _Just ot $ \t ->
      throwError $
        "type construct has conflict name: " ++ cn ++ " vs " ++ ppr t ++ ppr pos
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
              else TApp (s2n tn) (fmap (\t -> TVar t pos) tvars) pos
          bt =
            bindType tvars $
              if targs == []
                then rt
                else TFunc targs (EffList [] pos) rt pos
       in bindTypeEffVar [] bt

initTypeConDefs :: (Has EnvEff sig m) => Module -> m ()
initTypeConDefs m = mapM_ initTypeConDef $ m ^.. topStmts . traverse . _TDef

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

checkTypeConDefs :: (Has EnvEff sig m) => Module -> m ()
checkTypeConDefs m = mapM_ checkTypeConDef $ m ^.. topStmts . traverse . _TDef

initEffTypeDef :: (Has EnvEff sig m) => EffectDef -> m ()
initEffTypeDef e = do
  let en = e ^. effectName
  oe <- getEnv $ effs . at en
  forMOf _Just oe $ \oe ->
    throwError $
      "redefine an effect: " ++ en ++ " vs " ++ ppr oe ++ (ppr $ _effectLoc e)
  setEnv (Just $ effKind e) $ effs . at en
  where
    effKind e =
      let loc = _effectLoc e
          args = e ^. effectArgs
          star = KStar loc
          estar = EKStar loc
       in if args == []
            then estar
            else EKFunc (args ^.. traverse . _2 . non star) estar loc

initEffTypeDefs :: (Has EnvEff sig m) => Module -> m ()
initEffTypeDefs m = mapM_ initEffTypeDef $ m ^.. topStmts . traverse . _EDef

initEffIntfDef :: (Has EnvEff sig m) => EffectDef -> m ()
initEffIntfDef e = do
  globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
  let is = e ^. effectIntfs
      en = e ^. effectName
      f = \i -> do
        let intfn = i ^. intfName
            iargs = i ^. intfArgs
            iresult = i ^. intfResultType
            pos = i ^. intfLoc
            bvars = (i ^. intfBoundVars)
            targs = (e ^.. effectArgs . traverse . _1) ++ globalTypes
            b = bind (targs ++ bvars) $ iresult : iargs
            fvars = (b ^.. fv) :: [TVar]
        addEffIntfs en intfn
        if fvars /= []
          then
            throwError $
              "eff interfaces's type variables should "
                ++ "only exists in eff type arguments: "
                ++ ppr fvars ++ ppr pos
          else return ()
        ot <- getEnv $ funcs . at intfn
        forMOf _Just ot $ \t ->
          throwError $
            "eff interface has conflict name: " ++ intfn ++ " vs " ++ ppr t ++ ppr pos
        let eff = i ^. intfEffectType
        effs <- 
          mergeEffs eff $
            if e ^. effectArgs  == []
            then EffVar (s2n $ e ^. effectName) pos
            else EffApp
                  (e ^. effectName)
                  (map (\v -> TVar v pos) $ e ^.. effectArgs . traverse . _1)
                  pos
        let bt = intfType i e effs
        setEnv (Just bt) $ funcs . at intfn
  mapM_ f is
  where
    intfType i e eff =
      let iargs = i ^. intfArgs
          iresult = i ^. intfResultType
          intfn = i ^. intfName
          bvars = i ^. intfBoundVars
          pos = i ^. intfLoc
          tvars = e ^.. effectArgs . traverse . _1
          evars = i ^. intfBoundEffVars
       in bindTypeEffVar evars $ bindType tvars $
              bindType bvars $ TFunc iargs eff iresult pos

initEffIntfDefs :: (Has EnvEff sig m) => Module -> m ()
initEffIntfDefs m = mapM_ initEffIntfDef $ m ^.. topStmts . traverse . _EDef

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

checkEffIntfDefs :: (Has EnvEff sig m) => Module -> m ()
checkEffIntfDefs m = mapM_ checkEffIntfDef $ m ^.. topStmts . traverse . _EDef

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

initFuncDefs :: (Has EnvEff sig m) => Module -> m ()
initFuncDefs m = mapM_ initFuncDef $ m ^.. topStmts . traverse . _FDef

checkFuncType :: (Has EnvEff sig m) => FuncDef -> m ()
checkFuncType f = underScope $ do
  let pos = f ^. funcLoc
      bvars = fmap (\t -> (name2String t, KStar pos)) $ f ^. funcBoundVars
      bevars = fmap (\t -> (name2String t, EKStar pos)) $ f ^. funcBoundEffVars
  forM_ bvars $ \(n, k) -> setEnv (Just k) $ types . at n
  forM_ bevars $ \(n, k) -> setEnv (Just k) $ effs . at n
  mapM_
    (\(n, t) -> setFuncType n t)
    (f ^. funcArgs)
  case f ^. funcExpr of
    Just e -> do
      eType <- inferExprType e
      resultType <- inferType $ f ^. funcResultType
      checkTypeMatch eType resultType
      effType <- inferExprEffType e
      let fEff = f ^. funcEffectType 
      checkEffTypeMatch effType fEff
    Nothing -> return ()

checkFuncDef :: (Has EnvEff sig m) => FuncDef -> m ()
checkFuncDef f = underScope $ do
  let pos = f ^. funcLoc
      ft = funcDefType f
  k <- inferTypeKind ft
  checkTypeKind k
  checkFuncType f

checkFuncDefs :: (Has EnvEff sig m) => Module -> m ()
checkFuncDefs m = mapM_ checkFuncDef $ m ^.. topStmts . traverse . _FDef

checkImplFuncDef :: (Has EnvEff sig m) => FuncDef -> m ()
checkImplFuncDef f = underScope $ do
  let pos = f ^. funcLoc
      fn = f ^. funcName
      ft = funcDefType f
  k <- inferTypeKind ft
  checkTypeKind k
  ift <- getEnv $ funcs . at fn
  forMOf _Nothing ift $ \_ ->
    throwError $ "cannot find general function definiton for impl: " ++ fn ++ ppr pos
  bindings <- collectVarBindings (fromJust ift) ft
  checkVarBindings bindings
  checkFuncType f

checkImplFuncDefs :: (Has EnvEff sig m) => Module -> m ()
checkImplFuncDefs m = mapM_ checkImplFuncDef $ m ^.. topStmts . traverse . _ImplFDef . implFunDef

initModule :: Module -> Env -> Int -> Either String (Env, (Int, Module))
initModule m env id = run . runError . (runState env) . runFresh id $ do
  initTypeDefs m
  initEffTypeDefs m
  initTypeConDefs m
  initEffIntfDefs m
  initFuncDefs m
  return m

checkType :: Module -> Env -> Int -> Either String (Env, (Int, Module))
checkType m env id = run . runError . (runState env) . runFresh id $ do
  checkTypeConDefs m
  checkEffIntfDefs m
  checkFuncDefs m
  checkImplFuncDefs m
  return m
