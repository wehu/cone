{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
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

getEnv :: (Has EnvEff sig m) => Getter Env a -> m a
getEnv l = do
  env <- get @Env
  return $ view l env

setEnv :: (Has EnvEff sig m) => b -> Setter Env Env a b -> m ()
setEnv v l = do
  env <- get @Env
  put $ set l v env

underScope :: (Has EnvEff sig m) => m a -> m a
underScope f = do
  env <- get @Env
  res <- f
  put env
  return res

initTypeDef :: (Has EnvEff sig m) => Module -> m ()
initTypeDef m = initTypeKinds
  where
    typeDefs = m ^.. topStmts . traverse . _TDef
    initTypeKinds = mapM_ insertTypeKind typeDefs
    insertTypeKind t = do
      let tn = t ^. typeName
      ot <- getEnv $ types . at tn
      forMOf _Just ot $ \ot ->
        throwError $
          "redefine a type: " ++ tn ++ " vs " ++ ppr ot
      let k = Just $ typeKindOf t
      setEnv k $ types . at tn
    typeKindOf t =
      let loc = _typeLoc t
          args = t ^. typeArgs
          star = KStar loc
       in if args == []
            then star
            else KFunc (args ^.. traverse . _2 . non star) star loc

initTypeConDef :: (Has EnvEff sig m) => Module -> m ()
initTypeConDef m = initTconTypes
  where
    tdefs = m ^.. topStmts . traverse . _TDef
    initTconTypes = do
      globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
      mapM_ (insertTconType globalTypes) tdefs
    insertTconType globalTypes t =
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
            "type construct has conflict name: " ++ cn ++ " vs " ++ ppr t
        let bt = tconType c t
        setEnv (Just bt) $ funcs . at cn
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

checkTypeConDef :: (Has EnvEff sig m) => Module -> m ()
checkTypeConDef m = checkTconTypes
  where
    tdefs = m ^.. topStmts . traverse . _TDef
    checkTconTypes = do
      globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
      mapM_ (checkTconType globalTypes) tdefs
    checkTconType globalTypes t =
      forM_ (t ^. typeCons) $ \c -> do
        let cn = c ^. typeConName
        t <- getEnv $ funcs . at cn
        forMOf _Nothing t $ \t ->
          throwError $
            "cannot find type constructor : " ++ cn
        k <- underScope $ inferTypeKind $ fromJust t
        checkTypeKind k

inferTypeKind :: (Has EnvEff sig m) => Type -> m Kind
inferTypeKind a@TApp {..} = do
  ak <- inferTypeKind $ TVar _tappName _tloc
  case ak of
    KStar {} ->
      if _tappArgs == []
        then return ak
        else throwError $ "expected a func kind, but got " ++ ppr ak
    KFunc {..} ->
      if L.length _tappArgs /= L.length _kfuncArgs
        then throwError $ "kind arguments mismatch: " ++ ppr _tappArgs ++ " vs " ++ ppr _kfuncArgs
        else do
          forM_
            [(a, b) | a <- _tappArgs | b <- _kfuncArgs]
            $ \(a, b) -> do
              t <- inferTypeKind a
              checkTypeKind t
              checkTypeKind b
              if aeq t b
                then return ()
                else throwError $ "kind mismatch: " ++ ppr t ++ " vs " ++ ppr b
          checkTypeKind _kfuncResult
          return _kfuncResult
inferTypeKind a@TAnn {..} = do
  k <- inferTypeKind _tannType
  checkTypeKind k
  if aeq k _tannKind
    then return k
    else throwError $ "kind mismatch: " ++ ppr k ++ " vs " ++ ppr _tannKind
inferTypeKind b@BoundType {..} = underScope $ do
  let (bvs, t) = unsafeUnbind $ _boundType
      star = KStar $ _tloc t
  mapM_ (\v -> setEnv (Just star) $ types . at (name2String v)) bvs
  inferTypeKind t
inferTypeKind v@TVar {..} = do
  let tvn = name2String _tvar
  k <- getEnv $ types . at tvn
  forMOf _Nothing k $ \k ->
    throwError $ "cannot find type: " ++ ppr v
  return $ fromJust k
inferTypeKind f@TFunc {..} = do
  ks <- mapM inferTypeKind _tfuncArgs
  mapM_ checkTypeKind ks
  ek <- mapM inferEffKind _tfuncEff
  mapM_ checkEffKind ek
  rk <- inferTypeKind _tfuncResult
  checkTypeKind rk
  return $ KStar _tloc
inferTypeKind t = return $ KStar $ _tloc t

checkTypeKind :: (Has EnvEff sig m) => Kind -> m ()
checkTypeKind k = do
  case k of
    KStar {} -> return ()
    _ -> throwError $ "expected a star kind, but got " ++ ppr k

initEffTypeDef :: (Has EnvEff sig m) => Module -> m ()
initEffTypeDef m = initEffKinds
  where
    edefs = m ^.. topStmts . traverse . _EDef
    initEffKinds = mapM_ insertEffKind edefs
    insertEffKind e = do
      let en = e ^. effectName
      oe <- getEnv $ effs . at en
      forMOf _Just oe $ \oe ->
        throwError $
          "redefine an effect: " ++ en ++ " vs " ++ ppr oe
      setEnv (Just $ effKind e) $ effs . at en
    effKind e =
      let loc = _effectLoc e
          args = e ^. effectArgs
          star = KStar loc
          estar = EKStar loc
       in if args == []
            then estar
            else EKFunc (args ^.. traverse . _2 . non star) estar loc

inferEffKind :: (Has EnvEff sig m) => EffectType -> m EffKind
inferEffKind a@EffApp {..} = do
  ak <- inferEffKind $ EffVar _effAppName _effLoc
  case ak of
    EKFunc {..} ->
      if L.length _effAppArgs /= L.length _ekfuncArgs
        then throwError $ "eff kind arguments mismatch: " ++ ppr _effAppArgs ++ " vs " ++ ppr _ekfuncArgs
        else do
          forM_
            [(a, b) | a <- _effAppArgs | b <- _ekfuncArgs]
            $ \(a, b) -> do
              e <- inferTypeKind a
              checkTypeKind e
              checkTypeKind b
              if aeq e b
                then return ()
                else throwError $ "eff kind mismatch: " ++ ppr e ++ " vs " ++ ppr b
          checkEffKind _ekfuncResult
          return _ekfuncResult
    _ -> throwError $ "expected a func eff kind, but got " ++ ppr ak
inferEffKind a@EffAnn {..} = do
  k <- inferEffKind _effAnnType
  checkEffKind k
  if aeq k _effAnnKind
    then return k
    else throwError $ "eff kind mismatch: " ++ ppr k ++ " vs " ++ ppr _effAnnKind
inferEffKind b@BoundEffType {..} = underScope $ do
  let (bvs, t) = unsafeUnbind $ _boundEffType
      star = EKStar $ _effLoc t
  forM_ bvs $ \v -> setEnv (Just star) $ effs . at (name2String v)
  inferEffKind t
inferEffKind v@EffVar {..} = do
  let evn = name2String _effVarName
  k <- getEnv $ effs . at evn
  forMOf _Nothing k $ \k ->
    throwError $ "cannot find type: " ++ ppr v
  return $ fromJust k
inferEffKind l@EffList {..} = do
  ls <- mapM inferEffKind _effList
  mapM_ checkEffKind ls
  return $ EKList ls _effLoc
inferEffKind EffTotal {..} = return $ EKStar _effLoc

checkEffKind :: (Has EnvEff sig m) => EffKind -> m ()
checkEffKind k = do
  case k of
    EKStar {} -> return ()
    EKList {..} -> mapM_ checkEffKind _ekList
    _ -> throwError $ "expected a star eff kind, but got " ++ ppr k

initEffIntfDef :: (Has EnvEff sig m) => Module -> m ()
initEffIntfDef m = initEffIntfTypes
  where
    edefs = m ^.. topStmts . traverse . _EDef
    initEffIntfTypes = do
      globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
      forM_ edefs $ insertEffIntfType globalTypes
    insertEffIntfType globalTypes e = do
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
            if fvars /= []
              then
                throwError $
                  "eff interfaces's type variables should "
                    ++ "only exists in eff type arguments: "
                    ++ ppr fvars
              else return ()
            ot <- getEnv $ effIntfs . at intfn
            forMOf _Just ot $ \t ->
              throwError $
                "eff interface has conflict name: " ++ intfn ++ " vs " ++ ppr t
            let bt = intfType i e
            setEnv (Just bt) $ effIntfs . at intfn
      mapM_ f is
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

checkEffIntfDef :: (Has EnvEff sig m) => Module -> m ()
checkEffIntfDef m = checkEffIntfTypes
  where
    edefs = m ^.. topStmts . traverse . _EDef
    checkEffIntfTypes = do
      globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
      forM_ edefs $ checkEffIntfType globalTypes
    checkEffIntfType globalTypes e = do
      let is = e ^. effectIntfs
          en = e ^. effectName
          f = \i -> do
            let intfn = i ^. intfName
            t <- getEnv $ effIntfs . at intfn
            forMOf _Nothing t $ \t ->
              throwError $
                "cannot find eff interface: " ++ intfn
            k <- underScope $ inferTypeKind $ fromJust t
            checkTypeKind k
      mapM_ f is

freeVarName :: Int -> TVar
freeVarName i = makeName "$" $ toInteger i

initFuncDef :: (Has EnvEff sig m) => Module -> m ()
initFuncDef m = initFuncTypes
  where
    fdefs = m ^.. topStmts . traverse . _FDef
    initFuncTypes =
      mapM_
        ( \f -> do
            let pos = f ^. funcLoc
                fn = f ^. funcName
                bvars = fmap (\t -> (name2String t, KStar pos)) $ f ^. funcBoundVars
                initLocalScope = forM_ bvars $ \(n, k) -> setEnv (Just k) $ types . at n
            argTypes <-
              ( forM
                  (f ^. funcArgs ^.. traverse . _2)
                  $ \t -> underScope $ do
                        initLocalScope
                        k <- inferTypeKind t
                        checkTypeKind k
                        return t
                )
            effType <- underScope $ do
                     let t = f ^. funcEffectType . (non $ EffTotal pos)
                     initLocalScope
                     k <- inferEffKind t
                     checkEffKind k
                     return t
            resultType <- underScope $ do
                    let t = f ^.funcResultType
                    initLocalScope
                    k <- inferTypeKind t
                    checkTypeKind k
                    return t
            let ft =
                  BoundType $
                    bind (f ^. funcBoundVars) $
                      TFunc argTypes (Just effType) resultType pos
            underScope $ do
              initLocalScope
              k <- inferTypeKind ft
              checkTypeKind k
            oft <- getEnv $ funcs . at fn
            forMOf _Just oft $ \oft ->
              throwError $ "function redefine: " ++ fn
            setEnv (Just ft) $ funcs . at fn
        )
        fdefs

inferFuncDef :: (Has EnvEff sig m) => Module -> m ()
inferFuncDef m =
  let fdefs = m ^.. topStmts . traverse . _FDef
   in mapM_
        ( \f -> underScope $ do
            let pos = f ^. funcLoc
                fn = f ^. funcName
                bvars = fmap (\t -> (name2String t, KStar pos)) $ f ^. funcBoundVars
            forM_ bvars $ \(n, k) -> setEnv (Just k) $ types . at n
            (bts, ftype) <- (\f -> unbindTypeSample $ fromJust f) <$> (getEnv $ funcs . at fn)
            ft <- case ftype of
              ft@TFunc {} -> return ft
              _ -> throwError $ "expected function type, but got: " ++ ppr ftype
            let argTypes = _tfuncArgs ft
            let resultType = _tfuncResult ft
            let effType = _tfuncEff ft
            if L.length argTypes /= L.length (f ^. funcArgs)
              then throwError $ "type mismatch: " ++ ppr argTypes ++ " vs " ++ ppr (f ^. funcArgs)
              else return ()
            mapM_
              (\((n, _), t) -> setEnv (Just t) $ funcs . at n)
              [(n, t) | t <- argTypes | n <- (f ^. funcArgs)]
            forM_ bts $ \t -> setEnv (Just $ KStar pos) $ types . at (name2String t)
            case f ^. funcExpr of
              Just e -> do
                eType <- inferExprType e
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

inferExprType :: (Has EnvEff sig m) => Expr -> m Type
inferExprType EVar {..} = do
  v <- getEnv $ funcs . at _evarName
  forMOf _Nothing v $ \v ->
    throwError $ "cannot find expr var: " ++ _evarName
  return $ fromJust v
inferExprType a@EApp {..} = do
  appFuncType <- inferExprType _eappFunc >>= unbindType
  argTypes <- mapM inferExprType _eappArgs
  inferAppResultType appFuncType argTypes
inferExprType l@ELam {..} = underScope $ do
  mapM_ (\t -> setEnv (Just $ KStar _eloc) $ types . at (name2String t)) _elamBoundVars
  args <-
    mapM
      ( \(_, t) -> do
            k <- inferTypeKind t
            checkTypeKind k
            return t
      )
      _elamArgs
  eff <- case _elamEffType of
    Just e -> do
      inferEffKind e
      return e
    Nothing -> return $ EffTotal _eloc
  mapM_
    (\(n, t) -> setEnv (Just t) $ funcs . at n)
    [(n, t) | (n, _) <- _elamArgs | t <- args]
  case _elamExpr of
    Just e -> return ()
    Nothing -> throwError $ "expected an expression for lambda"
  eType <- inferExprType $ fromJust _elamExpr
  k <- inferTypeKind _elamResultType
  checkTypeKind k
  if aeq eType _elamResultType
    then return ()
    else throwError $ "lambda result type mismatch: " ++ ppr _elamResultType ++ " vs " ++ ppr eType
  return $ BoundType $ bind _elamBoundVars $ TFunc args (Just eff) eType _eloc
inferExprType a@EAnn {..} = do
  t <- inferExprType _eannExpr
  k <- inferTypeKind _eannType
  checkTypeKind k
  if aeq t _eannType
    then return _eannType
    else throwError $ "type mismatch: " ++ ppr t ++ " vs " ++ ppr _eannType
inferExprType ELit {..} = do
  k <- inferTypeKind _litType
  checkTypeKind k
  return _litType
inferExprType e = throwError $ "unsupported expression: " ++ ppr e

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
                (\s e -> (++) <$> (return s) <*> e)
                []
                [collectVarBinding aarg barg | aarg <- a ^. tfuncArgs | barg <- b ^. tfuncArgs]
            )
        <*> collectVarBinding (_tfuncResult a) (_tfuncResult b)
collectVarBinding a@TApp {} b@TApp {} =
  -- not support higher kind so far
  if L.length (_tappArgs a) == L.length (_tappArgs b)
    && aeq (_tappName a) (_tappName b)
    then
      foldM
        (\s e -> (++) <$> (return s) <*> e)
        []
        [collectVarBinding aarg barg | aarg <- (a ^. tappArgs) | barg <- (b ^. tappArgs)]
    else throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b
collectVarBinding a@TAnn {} b@TAnn {} =
  collectVarBinding (_tannType a) (_tannType b)
collectVarBinding a@BoundType {} b@BoundType {} = do
  let (ats, _) = unsafeUnbind $ _boundType a
      (bts, _) = unsafeUnbind $ _boundType b
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
  if L.length fArgTypes /= L.length args
    then throwError $ "function type argument number mismatch: " ++ ppr fArgTypes ++ " vs " ++ ppr args
    else return ()
  bindings <-
    foldM
      (\s e -> (++) <$> return s <*> e)
      []
      [collectVarBinding a b | a <- fArgTypes | b <- args]
  foldM
    ( \b (n, t) -> do
        case b ^. at n of
          Nothing -> return $ at n ?~ t $ b
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
unbindType b@BoundType {..} = do
  let (ps, t) = unsafeUnbind _boundType
      pos = _tloc t
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
  checkTypeConDef m
  checkEffIntfDef m
  inferFuncDef m
  return m
