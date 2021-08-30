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
import Debug.Trace
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
  tkinds <- typeKinds env
  put $ set types tkinds env
  where
    typeDefs = universeOn (topStmts . traverse . _TDef) m
    typeKinds env = foldM insertTypeKind (env ^. types) typeDefs
    insertTypeKind ts t =
      let tn = t ^. typeName
       in case M.lookup tn ts of
            Just ot ->
              throwError $
                "redefine a type: " ++ tn ++ " vs " ++ ppr ot
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
                          ++ ppr fvars
                    else return ()
                  case M.lookup cn fs of
                    Just t ->
                      throwError $
                        "type construct has conflict name: " ++ cn ++ " vs " ++ ppr t
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
        else throwError $ "expected a func kind, but got " ++ ppr ak
    KFunc {..} ->
      if L.length _tappArgs /= L.length _kfuncArgs
        then throwError $ "kind arguments mismatch: " ++ ppr _tappArgs ++ " vs " ++ ppr _kfuncArgs
        else do
          mapM
            ( \(a, b) -> do
                t <- inferTypeKind scope a
                checkTypeKind t
                checkTypeKind b
                if aeq t b
                  then return ()
                  else throwError $ "kind mismatch: " ++ ppr t ++ " vs " ++ ppr b
            )
            [(a, b) | a <- _tappArgs | b <- _kfuncArgs]
          checkTypeKind _kfuncResult
          return _kfuncResult
inferTypeKind scope a@TAnn {..} = do
  k <- inferTypeKind scope _tannType
  checkTypeKind k
  if aeq k _tannKind
    then return k
    else throwError $ "kind mismatch: " ++ ppr k ++ " vs " ++ ppr _tannKind
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
      Nothing -> throwError $ "cannot find type: " ++ ppr v
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
    _ -> throwError $ "expected a star kind, but got " ++ ppr k

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
                "redefine an effect: " ++ en ++ " vs " ++ ppr oe
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
        then throwError $ "eff kind arguments mismatch: " ++ ppr _effAppArgs ++ " vs " ++ ppr _ekfuncArgs
        else do
          mapM
            ( \(a, b) -> do
                e <- inferTypeKind scope a
                checkTypeKind e
                checkTypeKind b
                if aeq e b
                  then return ()
                  else throwError $ "eff kind mismatch: " ++ ppr e ++ " vs " ++ ppr b
            )
            [(a, b) | a <- _effAppArgs | b <- _ekfuncArgs]
          checkEffKind _ekfuncResult
          return _ekfuncResult
    _ -> throwError $ "expected a func eff kind, but got " ++ ppr ak
inferEffKind scope a@EffAnn {..} = do
  k <- inferEffKind scope _effAnnType
  checkEffKind k
  if aeq k _effAnnKind
    then return k
    else throwError $ "eff kind mismatch: " ++ ppr k ++ " vs " ++ ppr _effAnnKind
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
      Nothing -> throwError $ "cannot find type: " ++ ppr v
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
    _ -> throwError $ "expected a star eff kind, but got " ++ ppr k

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
                          ++ ppr fvars
                    else return ()
                  case M.lookup intfn is of
                    Just t ->
                      throwError $
                        "eff interface has conflict name: " ++ intfn ++ " vs " ++ ppr t
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

freeVarName :: Int -> TVar
freeVarName i = makeName "$" $ toInteger i

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
                                return $ TVar (freeVarName v) pos
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
                          return $ TVar (freeVarName v) pos
                      )
                  let ft =
                        BoundType $
                          bind (f ^. funcBoundVars) $
                            TFunc argTypes (Just effType) resultType pos
                   in do
                        inferTypeKind scope ft
                        case M.lookup fn fs of
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
                (bts, ftype) = unbindTypeSample $ fromJust $ M.lookup fn fs
             in do
                  ft <- case ftype of
                    ft@TFunc {} -> return ft
                    _ -> throwError $ "expected function type, but got: " ++ ppr ftype
                  let argTypes = _tfuncArgs ft
                  let resultType = _tfuncResult ft
                  let effType = _tfuncEff ft
                  if L.length argTypes /= L.length (f ^. funcArgs)
                    then throwError $ "type mismatch: " ++ ppr argTypes ++ " vs " ++ ppr (f ^. funcArgs)
                    else return ()
                  newScope <-
                    ( foldM
                        ( \s ((n, _), t) ->
                            let ts = M.insert n t $ s ^. exprTypes
                             in return $ s {_exprTypes = ts}
                        )
                        scope
                        [(n, t) | t <- argTypes | n <- (f ^. funcArgs)]
                      )
                  newScope' <-
                    ( foldM
                        ( \s t ->
                            let ks = M.insert (name2String t) (KStar pos) $ s ^. typeKinds
                             in return $ s {_typeKinds = ks}
                        )
                        newScope
                        bts
                      )
                  case f ^. funcExpr of
                    Just e -> do
                      eType <- inferExprType newScope' e
                      if aeq eType resultType
                        then return ()
                        else
                          throwError $
                            "function result type mismatch: "
                              ++ ppr eType
                              ++ " vs "
                              ++ ppr resultType
                    Nothing -> return ()
        )
        fdefs

inferExprType :: (Has EnvEff sig m) => Scope -> Expr -> m Type
inferExprType scope e@EVar {..} =
  case M.lookup _evarName (scope ^. exprTypes) of
    Just t -> return t
    Nothing -> throwError $ "cannot find expr var: " ++ _evarName
inferExprType scope a@EApp {..} = do
  appFuncType <- inferExprType scope _eappFunc >>= unbindType
  argTypes <- mapM (inferExprType scope) _eappArgs
  inferAppResultType appFuncType argTypes
inferExprType scope l@ELam {..} = do
  newScope <-
    ( foldM
        ( \s t ->
            let ks = M.insert (name2String t) (KStar _eloc) $ s ^. typeKinds
             in return $ s {_typeKinds = ks}
        )
        scope
        _elamBoundVars
      )
  args <-
    mapM
      ( \(_, t') -> case t' of
          Just t -> do
            inferTypeKind newScope t
            return t
          Nothing -> do
            v <- fresh
            return $ TVar (freeVarName v) _eloc
      )
      _elamArgs
  eff <- case _elamEffType of
    Just e -> do
      inferEffKind newScope e
      return e
    Nothing -> return $ EffTotal _eloc
  newScope' <-
    foldM
      ( \s (n, t) ->
          let ts = M.insert n t $ s ^. exprTypes
           in return $ s {_exprTypes = ts}
      )
      newScope
      [(n, t) | (n, _) <- _elamArgs | t <- args]

  case _elamExpr of
    Just e -> return ()
    Nothing -> throwError $ "expected an expression for lambda"
  eType <- inferExprType newScope' $ fromJust _elamExpr
  result <- case _elamResultType of
    Just t -> do
      inferTypeKind newScope t
      if aeq eType t
        then return t
        else throwError $ "lambda result type mismatch: " ++ ppr t ++ " vs " ++ ppr eType
    Nothing -> return eType
  return $ BoundType $ bind _elamBoundVars $ TFunc args (Just eff) result _eloc
inferExprType scope a@EAnn {..} = do
  t <- inferExprType scope _eannExpr
  inferTypeKind scope _eannType
  if aeq t _eannType
    then return _eannType
    else throwError $ "type mismatch: " ++ ppr t ++ " vs " ++ ppr _eannType
inferExprType scope ELit {..} = do
  inferTypeKind scope _litType
  return _litType
inferExprType scope e = throwError $ "unsupported expression: " ++ ppr e

collectVarBinding :: (Has EnvEff sig m) => Type -> Type -> m [(TVar, Type)]
collectVarBinding a@TPrim {} b@TPrim {} = do
  if aeq a b
    then return []
    else throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b
collectVarBinding a@TVar {..} t =
  let fvars = t ^.. fv
   in if L.foldl' (\r e -> aeq e _tvar || r) False fvars
        then throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr t
        else return [(_tvar, t)]
collectVarBinding a@TFunc {} b@TFunc {} =
  if L.length (_tfuncArgs a) /= L.length (_tfuncArgs b)
    then throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b
    else
      (++)
        <$> ( foldM
                (\s (a, b) -> (++) <$> (return s) <*> collectVarBinding a b)
                []
                [(aarg, barg) | aarg <- a ^. tfuncArgs | barg <- b ^. tfuncArgs]
            )
        <*> collectVarBinding (_tfuncResult a) (_tfuncResult b)
collectVarBinding a@TApp {} b@TApp {} =
  -- not support higher kind so far
  if L.length (_tappArgs a) == L.length (_tappArgs b)
    && aeq (_tappName a) (_tappName b)
    then
      foldM
        ( \s (a, b) -> do
            (++) <$> (return s) <*> collectVarBinding a b
        )
        []
        [(aarg, barg) | aarg <- (a ^. tappArgs) | barg <- (b ^. tappArgs)]
    else throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b
collectVarBinding a@TAnn {} b@TAnn {} =
  collectVarBinding (_tannType a) (_tannType b)
collectVarBinding a@BoundType {} b@BoundType {} =
  let (ats, _) = unsafeUnbind $ _boundType a
      (bts, _) = unsafeUnbind $ _boundType b
   in do
        if L.length ats /= L.length bts
          then throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b
          else return ()
        at <- unbindType a
        bt <- unbindType b
        collectVarBinding at bt
collectVarBinding a b = throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b

inferAppResultType :: (Has EnvEff sig m) => Type -> [Type] -> m Type
inferAppResultType f@TFunc {} args = do
  let fArgTypes = _tfuncArgs f
   in do
        if L.length fArgTypes /= L.length args
          then throwError $ "function type argument number mismatch: " ++ ppr fArgTypes ++ " vs " ++ ppr args
          else return ()
        bindings <-
          foldM
            (\s (a, b) -> (++) <$> (return s) <*> collectVarBinding a b)
            []
            [(a, b) | a <- fArgTypes | b <- args]
        foldM
          ( \b (n, t) -> do
              case M.lookup n b of
                Nothing -> return $ M.insert n t b
                Just ot ->
                  if aeq t ot
                    then return b
                    else throwError $ "type var binding conflict: " ++ ppr t ++ " vs " ++ ppr ot
          )
          M.empty
          bindings
        return $ substs bindings $ _tfuncResult f
inferAppResultType t _ = throwError $ "expected a function type, but got " ++ ppr t

closeType :: Type -> Bind [TVar] Type
closeType t =
  let fvars = t ^.. fv
   in bind fvars t

unbindType :: (Has EnvEff sig m) => Type -> m Type
unbindType b@BoundType {..} =
  let (ps, t) = unsafeUnbind _boundType
      pos = _tloc t
   in do
        foldM
          ( \t p -> do
              np <- freeVarName <$> fresh
              return $ subst p (TVar np pos) t
          )
          t
          ps
unbindType t = return t

unbindTypeSample :: Type -> ([TVar], Type)
unbindTypeSample b@BoundType {..} = unsafeUnbind _boundType
unbindTypeSample t = ([], t)

--           | ECase{_ecaseExpr :: Expr, _ecaseBody :: [Case], _eloc :: Location}
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
