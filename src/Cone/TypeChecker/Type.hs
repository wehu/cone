{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}

module Cone.TypeChecker.Type where

import Cone.Parser.AST
import Cone.TypeChecker.Env
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Lens
import Control.Lens.Plated
import Control.Monad
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe
import Unbound.Generics.LocallyNameless.Bind

inferTypeKind :: (Has EnvEff sig m) => Type -> m Kind
inferTypeKind a@TApp {..} = do
  ak <- inferTypeKind $ TVar _tappName _tloc
  case ak of
    KStar {} ->
      if _tappArgs == []
        then return ak
        else throwError $ "expected a func kind, but got " ++ ppr ak ++ ppr _tloc
    KFunc {..} ->
      if L.length _tappArgs /= L.length _kfuncArgs
        then throwError $ "kind arguments mismatch: " ++ ppr _tappArgs ++ " vs " ++ ppr _kfuncArgs ++ ppr a ++ ppr _tloc
        else do
          forM_
            [(a, b) | a <- _tappArgs | b <- _kfuncArgs]
            $ \(a, b) -> do
              t <- inferTypeKind a
              checkTypeKind t
              checkTypeKind b
              checkKindMatch t b
          checkTypeKind _kfuncResult
          return _kfuncResult
inferTypeKind a@TAnn {..} = do
  k <- inferTypeKind _tannType
  checkTypeKind k
  checkKindMatch k _tannKind
  return _tannKind
inferTypeKind b@BoundType {..} = underScope $ do
  let (bvs, t) = unsafeUnbind $ _boundType
      star = KStar $ _tloc
  mapM_ (\v -> setEnv (Just star) $ types . at (name2String v)) bvs
  inferTypeKind t
inferTypeKind b@BoundEffVarType {..} = underScope $ do
  let (bvs, t) = unsafeUnbind $ _boundEffVarType
      star = EKStar $ _tloc
  mapM_ (\v -> setEnv (Just star) $ effs . at (name2String v)) bvs
  inferTypeKind t
inferTypeKind v@TVar {..} = do
  let tvn = name2String _tvar
  k <- getEnv $ types . at tvn
  forMOf _Nothing k $ \k ->
    throwError $ "cannot find type: " ++ ppr v ++ ppr _tloc
  return $ fromJust k
inferTypeKind f@TFunc {..} = do
  ks <- mapM inferTypeKind _tfuncArgs
  mapM_ checkTypeKind ks
  ek <- inferEffKind _tfuncEff
  checkEffKind ek
  rk <- inferTypeKind _tfuncResult
  checkTypeKind rk
  return $ KStar _tloc
inferTypeKind n@TNum {..} = return $ KStar _tloc
inferTypeKind t = return $ KStar $ _tloc t

evalType :: Type -> [Type] -> (Int -> Int -> Int) -> Type
evalType t args f =
  if all (not . isn't _TNum) args
    then
      let arg : rest = fmap _tnum args
       in TNum (L.foldl' (\a b -> f <$> a <*> b) arg rest) (_tloc t)
    else t

inferType :: (Has EnvEff sig m) => Type -> m Type
inferType a@TApp {..} = do
  args <- mapM inferType _tappArgs
  let t = a {_tappArgs = args}
  case name2String _tappName of
    "____add" -> return $ evalType t args (+)
    "____sub" -> return $ evalType t args (-)
    "____mul" -> return $ evalType t args (*)
    "____div" -> return $ evalType t args div
    "____mod" -> return $ evalType t args mod
    "max" -> return $ evalType t args max
    "min" -> return $ evalType t args min
    _ -> return t
inferType a@TAnn {..} = do
  t <- inferType _tannType
  return a {_tannType = t}
inferType b@BoundType {..} = do
  let (B bts t) = _boundType
  t <- inferType t
  return $ bindType bts t
inferType b@BoundEffVarType {..} = do
  let (B ets t) = _boundEffVarType
  t <- inferType t
  return $ bindTypeEffVar ets t
inferType f@TFunc {..} = do
  args <- mapM inferType _tfuncArgs
  eff <- inferEffectType _tfuncEff
  res <- inferType _tfuncResult
  return f {_tfuncArgs = args, _tfuncEff = eff, _tfuncResult = res}
inferType t = return t

checkTypeKind :: (Has EnvEff sig m) => Kind -> m ()
checkTypeKind k = do
  case k of
    KStar {} -> return ()
    _ -> throwError $ "expected a star kind, but got " ++ ppr k ++ ppr (_kloc k)

inferEffKind :: (Has EnvEff sig m) => EffectType -> m EffKind
inferEffKind v@EffVar{..} = do
  k <- getEnv $ effs . at (name2String _effVar)
  case k of
    Just k -> return k
    Nothing -> throwError $ "cannot find eff variable: " ++ ppr v ++ ppr _effLoc
inferEffKind a@EffApp {..} = do
  k <- getEnv $ effs . at _effAppName
  forMOf _Nothing k $ \k ->
    throwError $ "cannot find type: " ++ ppr a ++ ppr _effLoc
  let ak = fromJust k
  case ak of
    EKFunc {..} ->
      if L.length _effAppArgs /= L.length _ekfuncArgs
        then throwError $ "eff kind arguments mismatch: " ++ ppr _effAppArgs ++ " vs " ++ ppr _ekfuncArgs ++ ppr _effLoc
        else do
          forM_
            [(a, b) | a <- _effAppArgs | b <- _ekfuncArgs]
            $ \(a, b) -> do
              e <- inferTypeKind a
              checkTypeKind e
              checkTypeKind b
              checkKindMatch e b
          checkEffKind _ekfuncResult
          return _ekfuncResult
    _ -> throwError $ "expected a func eff kind, but got " ++ ppr ak ++ ppr _effLoc
inferEffKind l@EffList {..} = do
  ls <- mapM inferEffKind _effList
  mapM_ checkEffKind ls
  return $ EKList ls _effLoc

inferEffectType :: (Has EnvEff sig m) => EffectType -> m EffectType
inferEffectType v@EffVar {} = return v
inferEffectType a@EffApp {..} = do
  args <- mapM inferType _effAppArgs
  return a {_effAppArgs = args}
inferEffectType l@EffList {..} = do
  ls <- mapM inferEffectType _effList
  return l {_effList = ls}

checkEffKind :: (Has EnvEff sig m) => EffKind -> m ()
checkEffKind k = do
  case k of
    EKStar {} -> return ()
    EKList {..} -> mapM_ checkEffKind _ekList
    _ -> throwError $ "expected a star eff kind, but got " ++ ppr k ++ ppr (_ekloc k)

checkTypeMatch :: (Has EnvEff sig m) => Type -> Type -> m ()
checkTypeMatch a b = do
  if aeq a b
    then return ()
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)

checkKindMatch :: (Has EnvEff sig m) => Kind -> Kind -> m ()
checkKindMatch a b = do
  if aeq a b
    then return ()
    else throwError $ "type kind mismatch: " ++ ppr a ++ ppr (_kloc a) ++ " vs " ++ ppr b ++ ppr (_kloc b)

checkEffTypeMatch :: (Has EnvEff sig m) => EffectType -> EffectType -> m ()
checkEffTypeMatch a b = do
  al <- toEffList a
  bl <- toEffList b
  if aeq (al ^. effList) (bl ^. effList)
     && aeq (al ^. effVar) (bl ^. effVar)
    then return ()
    else throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)

checkEffKindMatch :: (Has EnvEff sig m) => EffKind -> EffKind -> m ()
checkEffKindMatch a b = do
  if aeq a b
    then return ()
    else throwError $ "eff type kind mismatch: " ++ ppr a ++ ppr (_ekloc a) ++ " vs " ++ ppr b ++ ppr (_ekloc b)

toEffList' :: EffectType -> EffectType
toEffList' a@EffApp {..} = EffList [a] _effLoc
toEffList' v@EffVar {..} = EffList [v] _effLoc
toEffList' l@EffList {} = 
  let ls = join $ map (_effList . toEffList') (_effList l)
   in EffList ls (_effLoc l)

toEffList :: (Has EnvEff sig m) => EffectType -> m EffectType
toEffList eff = do
  es <- getEnv effs
  let effs = toEffList' eff
      (el, vl) = L.partition (\e -> isn't _EffVar e ||
                                    (isn't _Nothing $ M.lookup (name2String $ _effVar e) es))
                               (_effList effs)
      al = (L.sortBy acompare el) ++ (L.sortBy acompare vl)
  return effs{_effList=al}

mergeEffs :: (Has EnvEff sig m) => EffectType -> EffectType -> m EffectType
mergeEffs a@EffList {} b@EffList {} = do
  let al = a ^. effList
      bl = b ^. effList
      pos = _effLoc a
      l = L.unionBy aeq al bl
  return $ EffList l pos
mergeEffs a b = do
  al <- toEffList a
  bl <- toEffList b
  mergeEffs al bl

removeEff :: (Has EnvEff sig m) => EffectType -> EffectType -> m EffectType
removeEff f@EffList {} e@EffList {} = do
  let fl = f ^. effList
      el = e ^. effList
      pos = _effLoc f
  l <-
    foldM
      ( \l e -> return $ 
          l L.\\ (map (l !!) (L.findIndices (\a -> acompare e a /= LT) l))
      )
      fl
      el
  return $ EffList l pos
removeEff f e = do
  fl <- toEffList f
  el <- toEffList e
  removeEff fl el

applyTypeArgs :: (Has EnvEff sig m) => Type -> [Type] -> m Type
applyTypeArgs t args = do
  let (bts, ets, tt) = unbindTypeSimple t
  if L.length bts < L.length args then 
    throwError $ "function type variable number mismatch: " 
    ++ ppr bts ++ " vs" ++ ppr args ++ ": " ++ ppr t ++ ppr (_tloc t)
  else do
    let argsLen = L.length args
        binds = [(n, t) | n <- L.take argsLen bts | t <- args]
    return $ bindTypeEffVar ets $ bindType (L.drop argsLen bts) $ substs binds tt

inferAppResultType :: (Has EnvEff sig m) => Type -> [Type] -> [Type] -> m Type
inferAppResultType f@TFunc {} bargs args = do
  let fArgTypes = _tfuncArgs f
  if L.length fArgTypes /= L.length args
    then throwError $ "function type argument number mismatch: " ++ ppr fArgTypes ++ " vs " ++ ppr args ++ ppr (_tloc f)
    else return ()
  bindings <-
    foldM
      (\s e -> (++) <$> return s <*> e)
      []
      [collectVarBindings a b | a <- fArgTypes | b <- args]
  checkVarBindings bindings
  return $ substs bindings $ _tfuncResult f
inferAppResultType t _ [] = return t
inferAppResultType t _ _ = throwError $ "expected a function type, but got " ++ ppr t ++ ppr (_tloc t)

inferAppResultEffType :: (Has EnvEff sig m) => Type -> [Type] -> [Type] -> m EffectType
inferAppResultEffType f@TFunc {} targs args = do
  let fArgTypes = _tfuncArgs f
  if L.length fArgTypes /= L.length args
    then throwError $ "function type argument number mismatch: " ++ ppr fArgTypes ++ " vs " ++ ppr args ++ ppr (_tloc f)
    else return ()
  bindings <-
    foldM
      (\s e -> (++) <$> return s <*> e)
      []
      [collectVarBindings a b | a <- fArgTypes | b <- args]
  checkVarBindings bindings
  resEff <- toEffList $ _tfuncEff f
  funcEff <- toEffList $ _tfuncEff f
  let eff = substs bindings resEff
  effBindings <- collectEffVarBindings funcEff resEff
  checkEffVarBindings effBindings
  toEffList $ substs effBindings eff
inferAppResultEffType t _ [] = return $ EffList [] (_tloc t)
inferAppResultEffType t _ _ = throwError $ "expected a function type, but got " ++ ppr t ++ ppr (_tloc t)

collectVarBindings :: (Has EnvEff sig m) => Type -> Type -> m [(TVar, Type)]
collectVarBindings a@TPrim {} b@TPrim {} = do
  checkTypeMatch a b
  return []
collectVarBindings a@TVar {..} t = do
  tk <- getEnv $ types . at (name2String _tvar)
  case tk of
    Just _ -> do
      ut <- unbindType t
      if aeq a ut
        then return []
        else throwError $ "try to rebind type variable: " ++ ppr a ++ " to " ++ ppr t ++ ppr _tloc
    Nothing -> 
      let fvars = t ^.. fv
       in if not (aeq a t) && L.foldl' (\r e -> aeq e _tvar || r) False fvars
           then throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr t ++ ppr _tloc
           else return [(_tvar, t)]
collectVarBindings a@TFunc {} b@TFunc {} =
  if L.length (_tfuncArgs a) /= L.length (_tfuncArgs b)
    then throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
    else do
      al <- toEffList $ _tfuncEff a
      bl <- toEffList $ _tfuncEff b
      (++) <$>
       ((++)
        <$> ( foldM
                (\s e -> (++) <$> (return s) <*> e)
                []
                [collectVarBindings aarg barg | aarg <- a ^. tfuncArgs | barg <- b ^. tfuncArgs]
            )
        <*> collectVarBindings (_tfuncResult a) (_tfuncResult b))
        <*> collectVarBindingsInEff al bl
collectVarBindings a@TApp {} b@TApp {} =
  -- not support higher kind so far
  if L.length (_tappArgs a) == L.length (_tappArgs b)
    && aeq (_tappName a) (_tappName b)
    then
      foldM
        (\s e -> (++) <$> (return s) <*> e)
        []
        [collectVarBindings aarg barg | aarg <- (a ^. tappArgs) | barg <- (b ^. tappArgs)]
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectVarBindings a@TAnn {} b@TAnn {} =
  collectVarBindings (_tannType a) (_tannType b)
collectVarBindings a@BoundType {} b@BoundType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectVarBindings at bt
collectVarBindings a@BoundEffVarType {} b@BoundEffVarType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectVarBindings at bt
collectVarBindings a@BoundType {} b@BoundEffVarType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectVarBindings at bt
collectVarBindings a@BoundEffVarType {} b@BoundType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectVarBindings at bt
collectVarBindings a@TNum {} b@TNum {} =
  if (_tnum a) == (_tnum b)
    then return []
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectVarBindings a b = throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)

isEffVar :: (Has EnvEff sig m) => EffectType -> m Bool
isEffVar e@EffVar{..} = do
  found <- getEnv $ effs . at (name2String _effVar)
  case found of
    Just _ -> return False
    Nothing -> return True
isEffVar _ = return False

collectVarBindingsInEff :: (Has EnvEff sig m) => EffectType -> EffectType -> m [(TVar, Type)]
collectVarBindingsInEff s@EffVar{} _ = return []
collectVarBindingsInEff a@EffApp{} b@EffApp{} =
  if L.length (a ^. effAppArgs) /= L.length (b ^. effAppArgs) ||
     a ^. effAppName /= b ^. effAppName
  then throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b) 
  else foldM (\s e -> (++) <$> return s <*> e)
      []
      [collectVarBindings aarg barg | aarg <- (a ^. effAppArgs) | barg <- (b ^. effAppArgs)]
collectVarBindingsInEff a@EffList{} b@EffList{} = do
  let al = a ^. effList
  let bl = b ^. effList
  if L.length al > L.length bl
  then throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b) 
  else do
    if L.length al < L.length bl
    then do
           is <- isEffVar $ last al
           if not is
           then throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
           else return ()
    else return () 
    foldM (\s e -> (++) <$> return s <*> e)
      []
      [collectVarBindingsInEff aarg barg | aarg <- al | barg <- take (L.length al) bl]
collectVarBindingsInEff a b = throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)

collectEffVarBindings :: (Has EnvEff sig m) => EffectType -> EffectType -> m [(EffVar, EffectType)]
collectEffVarBindings EffVar{..} e = do
  is <- isEffVar e
  if is then return [(_effVar, e)]
  else return []
collectEffVarBindings a@EffApp{} b@EffApp{} = do
  if L.length (a ^. effAppArgs) /= L.length (b ^. effAppArgs) ||
     a ^. effAppName /= b ^. effAppName
  then throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b) 
  else do
    bindings <- foldM (\s e -> (++) <$> return s <*> e)
      []
      [collectVarBindings aarg barg | aarg <- (a ^. effAppArgs) | barg <- (b ^. effAppArgs)]
    checkVarBindings bindings
  return []
collectEffVarBindings a@EffList{} b@EffList{} = do
  let al = a ^. effList
  let bl = b ^. effList
  if L.length al > L.length bl
  then throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b) 
  else do
    if L.length al < L.length bl 
    then do
           is <- isEffVar $ last al
           if L.length al == 0 || not is
           then throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
           else return ()
    else return () 
    bindings <- foldM (\s e -> (++) <$> return s <*> e)
      []
      [collectEffVarBindings aarg barg | aarg <- al | barg <- take (L.length al) bl]
    if L.length al < L.length bl
    then return $ bindings ++ [(_effVar (last al), EffList (drop ((L.length al) - 1) bl) (_effLoc b))]
    else return bindings
collectEffVarBindings a b = throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)

checkVarBindings :: (Has EnvEff sig m) => [(TVar, Type)] -> m ()
checkVarBindings bindings = do
  foldM_
    ( \b (n, t) -> do
        case b ^. at n of
          Nothing -> return $ at n ?~ t $ b
          Just ot ->
            if aeq t ot
              then return b
              else throwError $ "type var binding conflict: " ++ ppr t ++ ppr (_tloc t) ++ " vs " ++ ppr ot ++ ppr (_tloc ot)
    )
    M.empty
    bindings

checkEffVarBindings :: (Has EnvEff sig m) => [(EffVar, EffectType)] -> m ()
checkEffVarBindings bindings = do
  foldM_
    ( \b (n, t) -> do
        case b ^. at n of
          Nothing -> return $ at n ?~ t $ b
          Just ot ->
            if aeq t ot
              then return b
              else throwError $ "eff type var binding conflict: " ++ ppr t ++ ppr (_effLoc t) ++ " vs " ++ ppr ot ++ ppr (_effLoc ot)
    )
    M.empty
    bindings

funcDefType :: FuncDef -> Type
funcDefType f =
  let pos = f ^. funcLoc
      argTypes = f ^. funcArgs ^.. traverse . _2
      effType = f ^. funcEffectType
      resultType = f ^. funcResultType
      bvs = f ^. funcBoundVars
      ft =
        bindType bvs $
            TFunc argTypes effType resultType pos
      bes = f ^. funcBoundEffVars
      bft = bindTypeEffVar bes ft
   in bft

extractTensorShape :: (Has EnvEff sig m) => Type -> m [Type]
extractTensorShape t@TApp{..} = do
  if name2String _tappName /= "____pair"
  then throwError $ "expected a pair type, but got " ++ ppr t ++ ppr _tloc
  else if L.length _tappArgs /= 2
    then throwError $ "expected 2 arguments, but got " ++ ppr t ++ ppr _tloc
    else do let a:b:[] = _tappArgs
            case a of
              TNum{..} -> case b of
                           TNum{..} -> return [a, b]
                           _ -> ((:) a) <$> extractTensorShape b
              _ -> throwError $ "expected a tnum type, but got " ++ ppr t ++ ppr _tloc 
extractTensorShape t = throwError $ "expected a pair type, but got " ++ ppr t ++ ppr (_tloc t)

extractTensorInfo :: (Has EnvEff sig m) => Type -> m (Type, [Type])
extractTensorInfo t@TApp{..} =
  if name2String _tappName /= "tensor" 
  then throwError $ "expected a tensor type, but got " ++ ppr t ++ ppr _tloc
  else if L.length _tappArgs /= 2
    then throwError $ "expected 2 arguments, but got " ++ ppr t ++ ppr _tloc
    else let et:shape:[] = _tappArgs
          in do s <- extractTensorShape shape
                return (et, s)
extractTensorInfo t = throwError $ "expected a tensor type, but got " ++ ppr t ++ ppr (_tloc t)

toTensorShape :: (Has EnvEff sig m) => [Type] -> m Type
toTensorShape t@(d0:d1:[]) = do
  if isn't _TNum d0 || isn't _TNum d1
  then throwError $ "expected tnum, but got " ++ ppr d0 ++ ppr (_tloc d0) ++ " or " ++ ppr d1 ++ ppr (_tloc d1)
  else return $ TApp (s2n "____pair") [d0, d1] (_tloc d0)
toTensorShape t@(d0:ds) = do
  ds' <- toTensorShape ds
  if isn't _TNum d0
  then throwError $ "expected tnum, but got " ++ ppr d0 ++ ppr (_tloc d0)
  else return $ TApp (s2n "____pair") [d0, ds'] (_tloc d0) 
toTensorShape ds = throwError $ "unsupported dims " ++ ppr ds

toTensorType :: (Has EnvEff sig m) => Type -> [Type] -> m Type
toTensorType t shape = do
  shape' <- toTensorShape shape
  return $ TApp (s2n "tensor") [t, shape'] (_tloc t)