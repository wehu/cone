{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Cone.Passes.TypeInfer (infer) where

import Cone.Parser.AST
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
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe

type Eff s e = Fresh :+: State s :+: Error e

type TypeKinds = M.Map String Kind

type EffKinds = M.Map String EffKind

type EffIntfTypes = M.Map String Type

type ExprTypes = M.Map String Type

data Scope = Scope {_typeKinds :: TypeKinds, _effKinds :: EffKinds, _exprTypes :: ExprTypes}

makeLenses ''Scope

data Env = Env
  { _types :: TypeKinds,
    _funcs :: ExprTypes,
    _effs :: EffKinds,
    _effIntfs :: EffIntfTypes
  }
  deriving (Show)

makeLenses ''Env

initialEnv =
  Env
    { _types = M.empty,
      _funcs = M.empty,
      _effs = M.empty,
      _effIntfs = M.empty
    }

type EnvEff = Eff Env String

initTypeDef :: (Has EnvEff sig m) => Module -> m ()
initTypeDef m = do
  env <- get @Env
  tkinds <- ts env
  put $ set types tkinds env
  where
    tdefs = universeOn (topStmts . traverse . _TDef) m
    ts env = foldM insertTypeKind (env ^. types) tdefs
    insertTypeKind ts t =
      let tn = t ^. typeName
       in case M.lookup tn ts of
            Just ot ->
              throwError $
                "redefine a type: " ++ tn ++ " vs " ++ show ot
            Nothing -> return $ M.insert tn (typeKind t) ts
    typeKind t =
      let loc = _typeLoc t
          args = t ^. typeArgs
          star = KStar loc
       in if args == []
            then star
            else
              KFunc
                ( fmap
                    ( \(_, kk) -> case kk of
                        Nothing -> star
                        Just kkk -> kkk
                    )
                    args
                )
                star
                loc

initTypeConDef :: (Has EnvEff sig m) => Module -> m ()
initTypeConDef m = do
  env <- get @Env
  tconTypes <- tcons env
  put $ set funcs tconTypes env
  where
    tdefs = universeOn (topStmts . traverse . _TDef) m
    tcons env =
      let globalTypes = (fmap (\n -> s2n n) $ M.keys (env ^. types))
       in foldM (insertTconType globalTypes) (env ^. funcs) tdefs
    insertTconType globalTypes fs t =
      let cons = t ^. typeCons
          f = \fs c -> do
            let cn = c ^. typeConName
                cargs = c ^. typeConArgs
                pos = c ^. typeConLoc
                targs = (t ^.. typeArgs . traverse . _1) ++ globalTypes
                b = bind targs cargs
                fvars = (b ^.. fv) :: [TVar]
             in do
                  if fvars /= []
                    then
                      throwError $
                        "type constructor's type variables should "
                          ++ "only exists in type arguments: "
                          ++ show fvars
                    else return ()
                  case M.lookup cn fs of
                    Just t ->
                      throwError $
                        "type construct has conflict name: " ++ cn ++ " vs " ++ show t
                    Nothing -> do
                      let bt = (tconType c t)
                       in do
                            k <- inferTypeKind (Scope M.empty M.empty M.empty) bt
                            checkTypeKind k
                            return $ M.insert cn bt fs
       in foldM f fs cons
    tconType c t =
      let targs = c ^. typeConArgs
          tn = t ^. typeName
          pos = c ^. typeConLoc
          tvars = t ^.. typeArgs . traverse . _1
          rt = TApp (s2n tn) (fmap (\t -> TVar t pos) tvars) pos
          bt =
            bind tvars $
              if targs == []
                then rt
                else TFunc targs Nothing rt pos
       in BoundType bt

inferTypeKind :: (Has EnvEff sig m) => Scope -> Type -> m Kind
inferTypeKind scope a@TApp {..} = do
  ak <- inferTypeKind scope $ TVar _tappName _tloc
  case ak of
    KStar {} ->
      if _tappArgs == []
        then return ak
        else throwError $ "expected a func kind, but got " ++ show ak
    KFunc {..} ->
      if L.length _tappArgs /= L.length _kfuncArgs
        then throwError $ "kind arguments mismatch: " ++ show _tappArgs ++ " vs " ++ show _kfuncArgs
        else do
          mapM
            ( \(a, b) -> do
                t <- inferTypeKind scope a
                checkTypeKind t
                checkTypeKind b
                if aeq t b
                  then return ()
                  else throwError $ "kind mismatch: " ++ show t ++ " vs " ++ show b
            )
            [(a, b) | a <- _tappArgs | b <- _kfuncArgs]
          checkTypeKind _kfuncResult
          return _kfuncResult
inferTypeKind scope a@TAnn {..} = do
  k <- inferTypeKind scope _tannType
  checkTypeKind k
  if aeq k _tannKind
    then return k
    else throwError $ "kind mismatch: " ++ show k ++ " vs " ++ show _tannKind
inferTypeKind scope b@BoundType {..} =
  let (bvs, t) = unsafeUnbind $ _boundType
      newScope =
        L.foldl'
          ( \s e ->
              M.insert (name2String e) (KStar $ _tloc t) s
          )
          (scope ^. typeKinds)
          bvs
   in inferTypeKind scope {_typeKinds = newScope} t
inferTypeKind scope v@TVar {..} = do
  kinds <- _types <$> get @Env
  case M.lookup (name2String _tvar) (scope ^. typeKinds) of
    Just k -> return k
    Nothing -> case M.lookup (name2String _tvar) kinds of
      Just k -> return k
      Nothing -> throwError $ "cannot find type: " ++ show v
inferTypeKind scope f@TFunc {..} = do
  ks <- mapM (inferTypeKind scope) _tfuncArgs
  mapM_ checkTypeKind ks
  ek <- mapM (inferEffKind scope) _tfuncEff
  mapM_ checkEffKind ek
  rk <- inferTypeKind scope _tfuncResult
  checkTypeKind rk
  return $ KStar _tloc
inferTypeKind _ t = return $ KStar $ _tloc t

checkTypeKind :: (Has EnvEff sig m) => Kind -> m ()
checkTypeKind k = do
  case k of
    KStar {} -> return ()
    _ -> throwError $ "expected a star kind, but got " ++ show k

initEffTypeDef :: (Has EnvEff sig m) => Module -> m ()
initEffTypeDef m = do
  env <- get @Env
  ekinds <- eff env
  put $ set effs ekinds env
  where
    edefs = universeOn (topStmts . traverse . _EDef) m

    eff env = foldM insertEffKind (env ^. effs) edefs
    insertEffKind es e =
      let en = e ^. effectName
       in case M.lookup en es of
            Just oe ->
              throwError $
                "redefine an effect: " ++ en ++ " vs " ++ show oe
            Nothing -> return $ M.insert en (effKind e) es
    effKind e =
      let loc = _effectLoc e
          args = e ^. effectArgs
          star = KStar loc
          estar = EKStar loc
       in if args == []
            then estar
            else
              EKFunc
                ( fmap
                    ( \(_, kk) -> case kk of
                        Nothing -> star
                        Just kkk -> kkk
                    )
                    args
                )
                estar
                loc

inferEffKind :: (Has EnvEff sig m) => Scope -> EffectType -> m EffKind
inferEffKind scope a@EffApp {..} = do
  ak <- inferEffKind scope $ EffVar _effAppName _effLoc
  case ak of
    EKFunc {..} ->
      if L.length _effAppArgs /= L.length _ekfuncArgs
        then throwError $ "eff kind arguments mismatch: " ++ show _effAppArgs ++ " vs " ++ show _ekfuncArgs
        else do
          mapM
            ( \(a, b) -> do
                e <- inferTypeKind scope a
                checkTypeKind e
                checkTypeKind b
                if aeq e b
                  then return ()
                  else throwError $ "eff kind mismatch: " ++ show e ++ " vs " ++ show b
            )
            [(a, b) | a <- _effAppArgs | b <- _ekfuncArgs]
          checkEffKind _ekfuncResult
          return _ekfuncResult
    _ -> throwError $ "expected a func eff kind, but got " ++ show ak
inferEffKind scope a@EffAnn {..} = do
  k <- inferEffKind scope _effAnnType
  checkEffKind k
  if aeq k _effAnnKind
    then return k
    else throwError $ "eff kind mismatch: " ++ show k ++ " vs " ++ show _effAnnKind
inferEffKind scope b@BoundEffType {..} =
  let (bvs, t) = unsafeUnbind $ _boundEffType
      newScope =
        L.foldl'
          ( \s e ->
              M.insert (name2String e) (EKStar $ _effLoc t) s
          )
          (scope ^. effKinds)
          bvs
   in inferEffKind scope {_effKinds = newScope} t
inferEffKind scope v@EffVar {..} = do
  kinds <- _effs <$> get @Env
  case M.lookup (name2String _effVarName) (scope ^. effKinds) of
    Just k -> return k
    Nothing -> case M.lookup (name2String _effVarName) kinds of
      Just k -> return k
      Nothing -> throwError $ "cannot find type: " ++ show v
inferEffKind scope l@EffList {..} = do
  ls <- mapM (inferEffKind scope) _effList
  mapM_ checkEffKind ls
  return $ EKList ls _effLoc
inferEffKind scope EffTotal {..} = return $ EKStar _effLoc

checkEffKind :: (Has EnvEff sig m) => EffKind -> m ()
checkEffKind k = do
  case k of
    EKStar {} -> return ()
    EKList {..} -> mapM_ checkEffKind _ekList
    _ -> throwError $ "expected a star eff kind, but got " ++ show k

initEffIntfDef :: (Has EnvEff sig m) => Module -> m ()
initEffIntfDef m = do
  env <- get @Env
  eintfs <- effIntfTypes env
  put $ set effIntfs eintfs env
  where
    edefs = universeOn (topStmts . traverse . _EDef) m
    effIntfTypes env =
      let globalTypes = (fmap (\n -> s2n n) $ M.keys (env ^. types))
       in foldM (insertEffIntfType globalTypes) (env ^. effIntfs) edefs
    insertEffIntfType globalTypes intfs e =
      let is = e ^. effectIntfs
          en = e ^. effectName
          f = \is i -> do
            let intfn = i ^. intfName
                iargs = i ^. intfArgs
                iresult = i ^. intfResultType
                pos = i ^. intfLoc
                bvars = (i ^. intfBoundVars)
                targs = (e ^.. effectArgs . traverse . _1) ++ globalTypes
                b = bind (targs ++ bvars) $ iresult : iargs
                fvars = (b ^.. fv) :: [TVar]
             in do
                  if fvars /= []
                    then
                      throwError $
                        "eff interfaces's type variables should "
                          ++ "only exists in eff type arguments: "
                          ++ show fvars
                    else return ()
                  case M.lookup intfn is of
                    Just t ->
                      throwError $
                        "eff interface has conflict name: " ++ intfn ++ " vs " ++ show t
                    Nothing -> do
                      let bt = (intfType i e)
                       in do
                            k <- inferTypeKind (Scope M.empty M.empty M.empty) bt
                            checkTypeKind k
                            return $ M.insert intfn bt is
       in foldM f intfs is
    intfType i e =
      let iargs = i ^. intfArgs
          iresult = i ^. intfResultType
          intfn = i ^. intfName
          bvars = i ^. intfBoundVars
          pos = i ^. intfLoc
          tvars = e ^.. effectArgs . traverse . _1
       in BoundType $
            bind tvars $
              BoundType $
                bind bvars $ TFunc iargs Nothing iresult pos

magicVarName :: Int -> TVar
magicVarName i = s2n $ "__" ++ show i

initFuncDef :: (Has EnvEff sig m) => Module -> m ()
initFuncDef m = do
  env <- get @Env
  fs <- funcTypes env
  put $ set funcs fs env
  where
    fdefs = universeOn (topStmts . traverse . _FDef) m
    funcTypes env =
      foldM
        ( \fs f ->
            let pos = f ^. funcLoc
                fn = f ^. funcName
                bvars = fmap (\t -> (name2String t, KStar pos)) $ f ^. funcBoundVars
                scope = Scope (M.fromList bvars) M.empty (env ^. funcs)
             in do
                  argTypes <-
                    ( mapM
                        ( \(_, a) ->
                            case a of
                              Just t -> do
                                inferTypeKind scope t
                                return t
                              Nothing -> do
                                v <- fresh
                                return $ TVar (magicVarName v) pos
                        )
                        (f ^. funcArgs)
                      )
                  effType <-
                    ( case (f ^. funcEffectType) of
                        Just t -> do
                          inferEffKind scope t
                          return t
                        Nothing -> return $ EffTotal pos
                      )
                  resultType <-
                    ( case (f ^. funcResultType) of
                        Just t -> do
                          inferTypeKind scope t
                          return t
                        Nothing -> do
                          v <- fresh
                          return $ TVar (magicVarName v) pos
                      )
                  let ft =
                        BoundType $
                          bind (f ^. funcBoundVars) $
                            TFunc argTypes (Just effType) resultType pos
                   in case M.lookup fn fs of
                        Just _ -> throwError $ "function redefine: " ++ fn
                        Nothing -> return $ M.insert fn ft fs
        )
        (env ^. funcs)
        fdefs

inferFuncDef :: (Has EnvEff sig m) => Module -> m ()
inferFuncDef m =
  let fdefs = universeOn (topStmts . traverse . _FDef) m
   in mapM_
        ( \f -> do
            env <- get @Env
            let pos = f ^. funcLoc
                fn = f ^. funcName
                fs = env ^. funcs
                bvars = fmap (\t -> (name2String t, KStar pos)) $ f ^. funcBoundVars
                scope = Scope (M.fromList bvars) M.empty fs
             in do
                  ftype <- unboundType $ fromJust $ M.lookup fn fs
                  ft <- case ftype of
                    ft@TFunc {} -> return ft
                    _ -> throwError $ "expected function type, but got: " ++ show ftype
                  let argTypes = _tfuncArgs ft
                  let resultType = _tfuncResult ft
                  let effType = _tfuncEff ft
                  newScope <-
                    ( foldM
                        ( \s ((n, _), t) ->
                            let ts = M.insert n t $ s ^. exprTypes
                             in return $ scope {_exprTypes = ts}
                        )
                        scope
                        [(n, t) | t <- argTypes | n <- (f ^. funcArgs)]
                      )
                  eType <- inferExprType newScope $ fromJust $ f ^. funcExpr
                  if aeq (closeType eType) (closeType resultType)
                    then return ()
                    else
                      throwError $
                        "function result type mismatch: "
                          ++ show eType
                          ++ " vs "
                          ++ show resultType
        )
        fdefs

inferExprType :: (Has EnvEff sig m) => Scope -> Expr -> m Type
inferExprType scope e@EVar {..} =
  case M.lookup _evarName (scope ^. exprTypes) of
    Just t -> return t
    Nothing -> throwError $ "cannot find expr var: " ++ _evarName
inferExprType scope a@EApp {..} = do
  app <- inferExprType scope _eappFunc
  argTypes <- mapM (inferExprType scope) _eappArgs
  appType <- (unboundType $ app)
  let appArgTypes = appType ^. tfuncArgs
   in if aeq (fmap closeType appArgTypes) (fmap closeType argTypes)
        then case appType of
          TFunc {..} -> return _tfuncResult
          _ -> throwError $ "expect a function type: " ++ show appType
        else
          throwError $
            "application type checking failed: "
              ++ show appArgTypes
              ++ " vs "
              ++ show argTypes
inferExprType scope _ = throwError $ "xxx"

closeType :: Type -> Bind [TVar] Type
closeType t =
  let fvars = t ^.. fv
   in bind fvars t

unboundType :: (Has EnvEff sig m) => Type -> m Type
unboundType b@BoundType {..} =
  let (ps, t) = unsafeUnbind _boundType
      pos = _tloc t
   in do
        foldM
          ( \t p -> do
              np <- magicVarName <$> fresh
              unboundType $ subst p (TVar np pos) t
          )
          t
          ps
unboundType t = return t

-- EVar{_evarName :: NamePath, _eloc :: Location}
--           | ELam{_elamBoundVars :: [TVar], _elamArgs :: [(String, Maybe Type)], _elamEffType :: Maybe EffectType,
--                  _elamResultType :: Maybe Type, _elamExpr :: Maybe Expr,
--                  _eloc :: Location}
--           | ECase{_ecaseExpr :: Expr, _ecaseBody :: [Case], _eloc :: Location}
--           | EApp{_eappFunc :: Expr, _eappArgs :: [Expr], _eloc :: Location}
--           | ELet{_eletVars :: [(String, Expr)], _eletBody :: Expr,
--                  _eloc :: Location}
--           | EHandle{_ehandleExpr :: Expr, _ehandleBindings :: [FuncDef],
--                     _eloc :: Location}
--           -- | ESeq{_eseq :: [Expr], _eloc :: Location}
--           | EAnn{_eannExpr :: Expr, _eannType :: Type, _eloc :: Location}

infer :: Module -> Either String (Env, (Int, Module))
infer m = run . runError . (runState initialEnv) . runFresh 0 $ do
  initTypeDef m
  initEffTypeDef m
  initTypeConDef m
  initEffIntfDef m
  initFuncDef m
  inferFuncDef m
  return m
