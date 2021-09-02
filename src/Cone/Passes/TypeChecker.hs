{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Cone.Passes.TypeChecker (Env (..), types, funcs, effs, effIntfs, initialEnv, initModule, checkType) where

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

initTypeDef :: (Has EnvEff sig m) => TypeDef -> m ()
initTypeDef t = do
  let tn = t ^. typeName
  ot <- getEnv $ types . at tn
  forMOf _Just ot $ \ot ->
    throwError $
      "redefine a type: " ++ tn ++ " vs " ++ ppr ot
  let k = Just $ typeKindOf t
  setEnv k $ types . at tn
  where typeKindOf t =
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
        "type construct has conflict name: " ++ cn ++ " vs " ++ ppr t
    let bt = tconType c t
    setEnv (Just bt) $ funcs . at cn
  where tconType c t =
          let targs = c ^. typeConArgs
              tn = t ^. typeName
              pos = c ^. typeConLoc
              tvars = t ^.. typeArgs . traverse . _1
              rt =
                if tvars == []
                  then TVar (s2n tn) pos
                  else TApp (s2n tn) (fmap (\t -> TVar t pos) tvars) pos
              bt =
                bind tvars $
                  if targs == []
                    then rt
                    else TFunc targs Nothing rt pos
           in BoundType bt

initTypeConDefs :: (Has EnvEff sig m) => Module -> m ()
initTypeConDefs m = mapM_ initTypeConDef $ m ^.. topStmts . traverse . _TDef

checkTypeConDef :: (Has EnvEff sig m) => TypeDef -> m ()
checkTypeConDef t = do
  globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
  forM_ (t ^. typeCons) $ \c -> do
    let cn = c ^. typeConName
    t <- getEnv $ funcs . at cn
    forMOf _Nothing t $ \t ->
      throwError $
        "cannot find type constructor : " ++ cn
    k <- underScope $ inferTypeKind $ fromJust t
    checkTypeKind k

checkTypeConDefs :: (Has EnvEff sig m) => Module -> m ()
checkTypeConDefs m = mapM_ checkTypeConDef $ m ^.. topStmts . traverse . _TDef

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

initEffTypeDef :: (Has EnvEff sig m) => EffectDef -> m ()
initEffTypeDef e = do
  let en = e ^. effectName
  oe <- getEnv $ effs . at en
  forMOf _Just oe $ \oe ->
    throwError $
      "redefine an effect: " ++ en ++ " vs " ++ ppr oe
  setEnv (Just $ effKind e) $ effs . at en
  where effKind e =
          let loc = _effectLoc e
              args = e ^. effectArgs
              star = KStar loc
              estar = EKStar loc
           in if args == []
                then estar
                else EKFunc (args ^.. traverse . _2 . non star) estar loc

initEffTypeDefs :: (Has EnvEff sig m) => Module -> m ()
initEffTypeDefs m = mapM_ initEffTypeDef $ m ^.. topStmts . traverse . _EDef

inferEffKind :: (Has EnvEff sig m) => EffectType -> m EffKind
inferEffKind a@EffApp {..} = do
  ak <- inferEffKind $ EffVar (s2n _effAppName) _effLoc
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
  where intfType i e =
          let iargs = i ^. intfArgs
              iresult = i ^. intfResultType
              intfn = i ^. intfName
              bvars = i ^. intfBoundVars
              pos = i ^. intfLoc
              eff = case i ^. intfEffectType of
                      Just e -> e
                      Nothing -> EffTotal pos
              tvars = e ^.. effectArgs . traverse . _1
           in BoundType $
                bind tvars $
                  BoundType $
                    bind bvars $ TFunc iargs (Just eff) iresult pos

initEffIntfDefs :: (Has EnvEff sig m) => Module -> m ()
initEffIntfDefs m = mapM_ initEffIntfDef $ m ^.. topStmts . traverse . _EDef

checkEffIntfDef :: (Has EnvEff sig m) => EffectDef -> m ()
checkEffIntfDef e = do
  globalTypes <- (\ts -> fmap (\n -> s2n n) $ M.keys ts) <$> getEnv types
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

checkEffIntfDefs :: (Has EnvEff sig m) => Module -> m ()
checkEffIntfDefs m = mapM_ checkEffIntfDef $ m ^.. topStmts . traverse . _EDef

freeVarName :: Int -> TVar
freeVarName i = makeName "$" $ toInteger i

initFuncDef :: (Has EnvEff sig m) => FuncDef -> m ()
initFuncDef f = do
  let pos = f ^. funcLoc
      fn = f ^. funcName
      bvars = fmap (\t -> (name2String t, KStar pos)) $ f ^. funcBoundVars
      argTypes = f ^. funcArgs ^.. traverse . _2
      effType = f ^. funcEffectType . (non $ EffTotal pos)
      resultType = f ^. funcResultType
      ft =
        BoundType $
          bind (f ^. funcBoundVars) $
            TFunc argTypes (Just effType) resultType pos
  k <- inferTypeKind ft
  checkTypeKind k
  oft <- getEnv $ funcs . at fn
  forMOf _Just oft $ \oft ->
    throwError $ "function redefine: " ++ fn
  setEnv (Just ft) $ funcs . at fn

initFuncDefs :: (Has EnvEff sig m) => Module -> m ()
initFuncDefs m = mapM_ initFuncDef $ m ^.. topStmts . traverse . _FDef

checkFuncDef :: (Has EnvEff sig m) => FuncDef -> m ()
checkFuncDef f = underScope $ do
  let pos = f ^. funcLoc
      fn = f ^. funcName
      bvars = fmap (\t -> (name2String t, KStar pos)) $ f ^. funcBoundVars
  forM_ bvars $ \(n, k) -> setEnv (Just k) $ types . at n
  mapM_
    (\(n, t) -> setEnv (Just t) $ funcs . at n)
    (f ^. funcArgs)
  case f ^. funcExpr of
    Just e -> do
      eType <- inferExprType e
      if aeq eType (f ^. funcResultType) 
        then return ()
        else
          throwError $
            "function result type mismatch: "
              ++ ppr eType
              ++ " vs "
              ++ ppr (f ^. funcResultType)
    Nothing -> return ()

checkFuncDefs :: (Has EnvEff sig m) => Module -> m ()
checkFuncDefs m = mapM_ checkFuncDef $ m ^.. topStmts . traverse . _FDef

checkImplFuncDef :: (Has EnvEff sig m) => FuncDef -> m ()
checkImplFuncDef f = underScope $ do
  let pos = f ^. funcLoc
      fn = f ^. funcName
      bvars = fmap (\t -> (name2String t, KStar pos)) $ f ^. funcBoundVars
      argTypes = f ^. funcArgs ^.. traverse . _2
      effType = f ^. funcEffectType . (non $ EffTotal pos)
      resultType = f ^. funcResultType
      ft =
        BoundType $
          bind (f ^. funcBoundVars) $
            TFunc argTypes (Just effType) resultType pos
  k <- inferTypeKind ft
  checkTypeKind k
  ift <- getEnv $ funcs . at fn
  forMOf _Nothing ift $ \_ ->
    throwError $ "cannot find general function definiton for impl: " ++ fn
  bindings <- collectVarBinding (fromJust ift) ft
  checkVarBinding bindings
  forM_ bvars $ \(n, k) -> setEnv (Just k) $ types . at n
  mapM_
    (\(n, t) -> setEnv (Just t) $ funcs . at n)
    (f ^. funcArgs)
  case f ^. funcExpr of
    Just e -> do
      eType <- inferExprType e
      if aeq eType (f ^. funcResultType) 
        then return ()
        else
          throwError $
            "function result type mismatch: "
              ++ ppr eType
              ++ " vs "
              ++ ppr (f ^. funcResultType)
    Nothing -> return ()

checkImplFuncDefs :: (Has EnvEff sig m) => Module -> m ()
checkImplFuncDefs m = mapM_ checkImplFuncDef $ m ^.. topStmts . traverse . _ImplFDef . implFunDef

inferExprType :: (Has EnvEff sig m) => Expr -> m Type
inferExprType EVar {..} = do
  v <- getEnv $ funcs . at _evarName
  forMOf _Nothing v $ \v ->
    throwError $ "cannot find expr var: " ++ _evarName
  return $ fromJust v
inferExprType a@EApp {..} = do
  appFuncType <- inferExprType _eappFunc >>= unbindType
  argTypes <- mapM inferExprType _eappArgs
  argKinds <- mapM inferTypeKind argTypes
  mapM_ checkTypeKind argKinds
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
inferExprType ESeq {..} = do
  ts <- mapM inferExprType _eseq
  return $ last ts
inferExprType ELet {..} =
  bindPatternVarsType _eletPattern _eletExpr
inferExprType ECase {..} = do
  ct <- inferExprType _ecaseExpr
  ts <- forM _ecaseBody $ \c -> underScope $ do
    bindPatternVarsType (c ^. casePattern) _ecaseExpr
    pt <- inferPatternType $ c ^. casePattern
    et <- inferExprType $ c ^. caseExpr
    return (pt, et)
  let t : rest = ts
  forM_ (rest ^.. traverse . _2) $ \e ->
    if aeq ct (t ^. _1)
      then return ()
      else throwError $ "type mismatch: " ++ ppr (t ^. _1) ++ " vs " ++ ppr e
  forM_ (ts ^.. traverse . _1) $ \e ->
    if aeq ct e
      then return ()
      else throwError $ "type mismatch: " ++ ppr ct ++ " vs " ++ ppr e
  return $ (last ts) ^. _2
inferExprType EWhile {..} = do
  t <- inferExprType _ewhileCond
  if aeq t (TPrim Pred _eloc)
    then return t
    else throwError $ "while expected a bool as condition, but got " ++ ppr t
  underScope $ do
    t <- inferExprType _ewhileBody
    k <- inferTypeKind t
    checkTypeKind k
  return $ TPrim Unit _eloc
inferExprType EHandle {..} = do
  ek <- inferEffKind _ehandleEff
  checkEffKind ek
  bodyType <- inferExprType _ehandleScope
  btk <- inferTypeKind bodyType
  checkTypeKind btk
  underScope $ forM_ _ehandleBindings checkFuncDef
  return bodyType

inferPatternType :: (Has EnvEff sig m) => Pattern -> m Type
inferPatternType PVar {..} = inferExprType $ EVar _pvar _ploc
inferPatternType PApp {..} = do
  args <- mapM inferPatternType _pappArgs
  appFuncType <- inferExprType (EVar _pappName _ploc) >>= unbindType
  inferAppResultType appFuncType args
inferPatternType PExpr {..} = inferExprType _pExpr

bindPatternVarsType :: (Has EnvEff sig m) => Pattern -> Expr -> m Type
bindPatternVarsType p e = do
  eType <- inferExprType e
  typeBindings <- extractPatternType p eType
  foldM
    ( \bs (v, t) -> do
        let n = name2String v
        case bs ^. at n of
          Just _ -> throwError $ "pattern rebind a variable: " ++ n
          Nothing -> do
            setEnv (Just t) $ funcs . at n
            return $ bs & at n ?~ True
    )
    M.empty
    typeBindings
  return eType

extractPatternType :: (Has EnvEff sig m) => Pattern -> Type -> m [(TVar, Type)]
extractPatternType PVar {..} t = return [(s2n _pvar, t)]
extractPatternType PExpr {..} t = return []
extractPatternType a@PApp {..} t = underScope $ do
  appFuncType <- inferExprType (EVar _pappName _ploc) >>= unbindType
  let cntr =
        ( \arg ->
            let newTVar = do
                  fvn <- fresh
                  let vn = name2String $ freeVarName fvn
                      t = TVar (s2n vn) _ploc
                  setEnv (Just t) $ funcs . at vn
                  return t
             in case arg of
                  TVar {..} -> do
                    gt <- getEnv $ types . at (name2String _tvar)
                    case gt of
                      Just _ -> return arg
                      Nothing -> newTVar
                  tp@TApp {..} -> do
                    as <- mapM cntr _tappArgs
                    return $ tp {_tappArgs = as}
                  _ -> newTVar
        )
  argTypes <- mapM cntr (appFuncType ^. tfuncArgs)
  appT <- inferAppResultType appFuncType argTypes
  bindings <- collectVarBinding appT t
  foldM
    ( \s e ->
        (++) <$> return s <*> e
    )
    []
    [extractPatternType arg argt | arg <- _pappArgs | argt <- substs bindings argTypes]

collectVarBinding :: (Has EnvEff sig m) => Type -> Type -> m [(TVar, Type)]
collectVarBinding a@TPrim {} b@TPrim {} = do
  if aeq a b
    then return []
    else throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b
collectVarBinding a@TVar {..} t = do
  tk <- getEnv $ types . at (name2String _tvar)
  case tk of
    Just _ -> do
      ut <- unbindType t
      if aeq a ut
        then return []
        else throwError $ "try to rebind type: " ++ ppr a ++ " to " ++ show t
    Nothing ->
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
  at <- unbindType a
  bt <- unbindType b
  collectVarBinding at bt
collectVarBinding a b = throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b

checkVarBinding :: (Has EnvEff sig m) => [(TVar, Type)] -> m ()
checkVarBinding bindings = do
  foldM_
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
  checkVarBinding bindings
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

--           | EHandle{_ehandleExpr :: Expr, _ehandleBindings :: [FuncDef],
--                     _eloc :: Location}

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
