{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cone.TypeChecker.Type where

import Cone.Parser.AST
import Cone.TypeChecker.Env
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Lens
import Control.Lens.Plated
import Control.Monad
import qualified Data.ByteString.Lazy.UTF8 as BLU
import Data.Digest.Pure.MD5
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace
import GHC.Stack
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe

-- | Infer type's kind
inferTypeKind :: (Has EnvEff sig m) => Type -> m Kind
inferTypeKind a@TApp {..} = do
  ak <- inferTypeKind _tappName
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
              checkKindMatch t b
          return _kfuncResult
inferTypeKind a@TAnn {..} = do
  k <- inferTypeKind _tannType
  checkKindMatch k _tannKind
  return _tannKind
inferTypeKind b@BoundType {..} = underScope $ do
  let (bvs, t) = unsafeUnbind $ _boundType
      star = KStar $ _tloc
  mapM_ (\(v, k) -> setEnv (Just $ k ^. non star) $ types . at (name2String v)) bvs
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
inferTypeKind n@TNum {..} = return $ KNum _tloc
inferTypeKind l@TList {..} = do
  es' <- mapM inferTypeKind _tlist
  let e : es = es'
  forM_ es $ \k ->
    checkKindMatch e k
  return $ KList e _tloc
inferTypeKind t = return $ KStar $ _tloc t

-- | Eval a type if there is number calc
evalType1 :: Type -> [Type] -> (Int -> Int) -> Type
evalType1 t args f =
  if all (not . isn't _TNum) args
    then
      let arg : rest = fmap _tnum args
       in TNum (fmap f arg) (_tloc t)
    else t

evalType2 :: Type -> [Type] -> (Int -> Int -> Int) -> Type
evalType2 t args f =
  if all (not . isn't _TNum) args
    then
      let arg : rest = fmap _tnum args
       in TNum (L.foldl' (\a b -> f <$> a <*> b) arg rest) (_tloc t)
    else t

-- | Simplize the type
inferType :: (Has EnvEff sig m) => Type -> m Type
inferType a@TApp {..} = do
  args <- mapM inferType _tappArgs
  let t = a {_tappArgs = args}
  case name2String (_tvar _tappName) of
    "core/prelude/neg" -> return $ evalType1 t args (\e -> (-e))
    "core/prelude/add" -> return $ evalType2 t args (+)
    "core/prelude/sub" -> return $ evalType2 t args (-)
    "core/prelude/mul" -> return $ evalType2 t args (*)
    "core/prelude/div" -> return $ evalType2 t args div
    "core/prelude/mod" -> return $ evalType2 t args mod
    "core/prelude/max" -> return $ evalType2 t args max
    "core/prelude/min" -> return $ evalType2 t args min
    _ -> return t
inferType a@TAnn {..} = do
  t <- inferType _tannType
  return a {_tannType = t}
inferType b@BoundType {..} = do
  let (bts, t) = unsafeUnbind _boundType
  t <- inferType t
  return $ bindType bts t
inferType b@BoundEffVarType {..} = do
  let (ets, t) = unsafeUnbind _boundEffVarType
  t <- inferType t
  return $ bindTypeEffVar ets t
inferType f@TFunc {..} = do
  args <- mapM inferType _tfuncArgs
  eff <- inferEffectType _tfuncEff
  res <- inferType _tfuncResult
  return f {_tfuncArgs = args, _tfuncEff = eff, _tfuncResult = res}
inferType l@TList {..} = do
  es <- mapM inferType _tlist
  return l {_tlist = es}
inferType t = return t

-- | Check a type kind
checkTypeKind :: (Has EnvEff sig m) => Kind -> m ()
checkTypeKind k = do
  case k of
    KStar {} -> return ()
    _ -> throwError $ "expected a star kind, but got " ++ ppr k ++ ppr (_kloc k)

-- | Infer an effect type kind
inferEffKind :: (Has EnvEff sig m) => EffectType -> m EffKind
inferEffKind v@EffVar {..} = do
  k <- getEnv $ effs . at (name2String _effVar)
  case k of
    Just k -> return k
    Nothing -> throwError $ "cannot find eff variable: " ++ ppr v ++ ppr _effLoc
inferEffKind a@EffApp {..} = do
  k <- getEnv $ effs . at (name2String $ _effVar _effAppName)
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

-- | Infer effect type
inferEffectType :: (Has EnvEff sig m) => EffectType -> m EffectType
inferEffectType v@EffVar {} = return v
inferEffectType a@EffApp {..} = do
  args <- mapM inferType _effAppArgs
  return a {_effAppArgs = args}
inferEffectType l@EffList {..} = do
  ls <- mapM inferEffectType _effList
  return l {_effList = ls}

-- | Check effect kind
checkEffKind :: (Has EnvEff sig m) => EffKind -> m ()
checkEffKind k = do
  case k of
    EKStar {} -> return ()
    EKList {..} -> mapM_ checkEffKind _ekList
    _ -> throwError $ "expected a star eff kind, but got " ++ ppr k ++ ppr (_ekloc k)

-- | Check if type match or not
checkTypeMatch :: (Has EnvEff sig m) => Type -> Type -> m ()
checkTypeMatch a b = do
  a' <- inferType a
  b' <- inferType b
  if aeq a' b'
    then return ()
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)

-- | Check if type kind match or not
checkKindMatch :: (Has EnvEff sig m) => Kind -> Kind -> m ()
checkKindMatch a b = do
  if aeq a b
    then return ()
    else throwError $ "type kind mismatch: " ++ ppr a ++ ppr (_kloc a) ++ " vs " ++ ppr b ++ ppr (_kloc b)

-- | Check effect type match or not
checkEffTypeMatch :: (Has EnvEff sig m) => EffectType -> EffectType -> m ()
checkEffTypeMatch a b = do
  al <- toEffList a
  bl <- toEffList b
  if aeq (al ^. effList) (bl ^. effList)
    && aeq (al ^. effVar) (bl ^. effVar)
    then return ()
    else throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)

-- | Check if effect type kind match or not
checkEffKindMatch :: (Has EnvEff sig m) => EffKind -> EffKind -> m ()
checkEffKindMatch a b = do
  if aeq a b
    then return ()
    else throwError $ "eff type kind mismatch: " ++ ppr a ++ ppr (_ekloc a) ++ " vs " ++ ppr b ++ ppr (_ekloc b)

-- | Convert an effect type to effect list type
toEffList' :: EffectType -> EffectType
toEffList' a@EffApp {..} = EffList [a] _effLoc
toEffList' v@EffVar {..} = EffList [v] _effLoc
toEffList' l@EffList {} =
  let ls = join $ map (_effList . toEffList') (_effList l)
   in EffList ls (_effLoc l)

-- | Convert an effect type to effect list type
toEffList :: (Has EnvEff sig m) => EffectType -> m EffectType
toEffList eff = do
  es <- getEnv effs
  let effs = toEffList' eff
      -- first part is application effect type and second part is effect variable list
      (el, vl) =
        L.partition
          ( \e ->
              isn't _EffVar e
                || (isn't _Nothing $ M.lookup (name2String $ _effVar e) es)
          )
          (_effList effs)
      al = (L.sortBy acompare el) ++ (L.sortBy acompare vl)
  return effs {_effList = al}

-- | Merge two effect types
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

-- | Remove effect types
removeEff :: (Has EnvEff sig m) => EffectType -> EffectType -> m EffectType
removeEff f@EffList {} e@EffList {} = do
  -- es <- getEnv effs
  let -- (fl, fvl) = L.partition (\e -> isn't _EffVar e ||
      --                               (isn't _Nothing $ M.lookup (name2String $ _effVar e) es))
      --                          (f ^. effList)
      -- (el, evl) = L.partition (\e -> isn't _EffVar e ||
      --                               (isn't _Nothing $ M.lookup (name2String $ _effVar e) es))
      --                          (e ^. effList)
      fl = f ^. effList
      el = e ^. effList
      pos = _effLoc f
  l <-
    foldM
      ( \l e ->
          return $
            -- l L.\\ (map (l !!) (L.findIndices (\a -> acompare e a /= LT) l))
            l L.\\ (map (l !!) (L.findIndices (aeq e) l))
      )
      fl
      el
  -- vl <-
  --   foldM
  --     ( \l e -> return $
  --         l L.\\ (map (l !!) (L.findIndices (aeq e) l))
  --     )
  --     fvl
  --     evl
  return $ EffList (l {-L.sortBy acompare l ++ L.sortBy acompare vl -}) pos
removeEff f e = do
  fl <- toEffList f
  el <- toEffList e
  removeEff fl el

-- | Apply type arguments to application type
applyTypeArgs :: (Has EnvEff sig m) => Type -> [Type] -> m Type
applyTypeArgs t args = do
  let (bts, ets, tt) = unbindTypeSimple t
  if L.length bts < L.length args
    then
      throwError $
        "function type variable number mismatch: "
          ++ ppr bts
          ++ " vs"
          ++ ppr args
          ++ ": "
          ++ ppr t
          ++ ppr (_tloc t)
    else do
      let argsLen = L.length args
          binds = [(n ^. _1, t) | n <- L.take argsLen bts | t <- args]
          ts = [(n ^. _2 . non (KStar (_tloc t)), t) | n <- L.take argsLen bts | t <- args]
      forM_ ts $ \(k, t) -> do
        tk <- inferTypeKind t
        checkKindMatch k tk
      return $ bindTypeEffVar ets $ bindType (L.drop argsLen bts) $ substs binds tt

-- | Infer a result type of application type
inferAppResultType :: (Has EnvEff sig m) => Type -> [Type] -> [Type] -> m (Type, Type)
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
  let ft = substs bindings f
  return (_tfuncResult ft, ft)
inferAppResultType t _ [] = return (t, t)
inferAppResultType t _ _ = throwError $ "expected a function type, but got " ++ ppr t ++ ppr (_tloc t)

-- | Infer the result effect type of application type
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
  effBindings <-
    (++)
      <$> ( foldM
              (\s e -> (++) <$> return s <*> e)
              []
              [collectEffVarBindingsInType a b | a <- fArgTypes | b <- args]
          )
      <*> collectEffVarBindings funcEff resEff
  checkEffVarBindings effBindings
  toEffList $ substs effBindings eff
inferAppResultEffType t _ [] = return $ EffList [] (_tloc t)
inferAppResultEffType t _ _ = throwError $ "expected a function type, but got " ++ ppr t ++ ppr (_tloc t)

-- | Collect all variable bindings
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
      (++)
        <$> ( (++)
                <$> ( foldM
                        (\s e -> (++) <$> (return s) <*> e)
                        []
                        [collectVarBindings aarg barg | aarg <- a ^. tfuncArgs | barg <- b ^. tfuncArgs]
                    )
                <*> collectVarBindings (_tfuncResult a) (_tfuncResult b)
            )
        <*> collectVarBindingsInEff al bl
collectVarBindings a@TList {} b@TList {} =
  if L.length (_tlist a) == L.length (_tlist b)
    then
      foldM
        (\s e -> (++) <$> (return s) <*> e)
        []
        [collectVarBindings ae be | ae <- (a ^. tlist) | be <- (b ^. tlist)]
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
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

-- | Return if an effect variable is local variable or not
isEffVar :: (Has EnvEff sig m) => EffectType -> m Bool
isEffVar e@EffVar {..} = do
  -- if a variable can be found in eff records, it is not a type variable
  found <- getEnv $ effs . at (name2String _effVar)
  case found of
    Just _ -> return False
    Nothing -> return True
isEffVar _ = return False

-- | Check all variable bindings in effect type
collectVarBindingsInEff :: (Has EnvEff sig m) => EffectType -> EffectType -> m [(TVar, Type)]
collectVarBindingsInEff s@EffVar {} _ = return []
collectVarBindingsInEff a@EffApp {} b@EffApp {} =
  if L.length (a ^. effAppArgs) /= L.length (b ^. effAppArgs)
    || not (aeq (_effAppName a) (_effAppName b))
    then throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
    else
      foldM
        (\s e -> (++) <$> return s <*> e)
        []
        [collectVarBindings aarg barg | aarg <- (a ^. effAppArgs) | barg <- (b ^. effAppArgs)]
collectVarBindingsInEff a@EffList {} b@EffList {} = do
  let al = a ^. effList
  let bl = b ^. effList
  let error = throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
  if L.length al > L.length bl
    then
      if L.length al == (L.length bl) + 1
        then do
          is <- isEffVar $ last al
          if is
            then return ()
            else error
        else error
    else return ()
  if L.length al < L.length bl
    then do
      if al == []
        then error
        else do
          is <- isEffVar $ last al
          if not is
            then error
            else return ()
    else return ()
  foldM
    (\s e -> (++) <$> return s <*> e)
    []
    [collectVarBindingsInEff aarg barg | aarg <- al | barg <- bl]
collectVarBindingsInEff a b = throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)

-- | Check all effect variables
collectEffVarBindings :: (Has EnvEff sig m) => EffectType -> EffectType -> m [(EffVar, EffectType)]
collectEffVarBindings ev@EffVar {..} e = do
  is <- isEffVar ev
  if is
    then return [(_effVar, e)]
    else return []
collectEffVarBindings a@EffApp {} b@EffApp {} = do
  if L.length (a ^. effAppArgs) /= L.length (b ^. effAppArgs)
    || not (aeq (_effAppName a) (_effAppName b))
    then throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
    else do
      bindings <-
        foldM
          (\s e -> (++) <$> return s <*> e)
          []
          [collectVarBindings aarg barg | aarg <- (a ^. effAppArgs) | barg <- (b ^. effAppArgs)]
      checkVarBindings bindings
  return []
collectEffVarBindings a@EffList {} b@EffList {} = do
  let al = a ^. effList
  let bl = b ^. effList
  let error = throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
  if L.length al > L.length bl
    then
      if L.length al == (L.length bl) + 1
        then do
          is <- isEffVar $ last al
          if is
            then return ()
            else error
        else error
    else return ()
  if L.length al < L.length bl
    then
      if al == []
        then error
        else do
          is <- isEffVar $ last al
          if not is
            then error
            else return ()
    else return ()
  if L.length al < L.length bl
    then do
      bindings <-
        foldM
          (\s e -> (++) <$> return s <*> e)
          []
          [collectEffVarBindings aarg barg | aarg <- init al | barg <- bl]
      return $ bindings ++ [(_effVar (last al), EffList (drop ((L.length al) - 1) bl) (_effLoc b))]
    else do
      bindings <-
        foldM
          (\s e -> (++) <$> return s <*> e)
          []
          [collectEffVarBindings aarg barg | aarg <- al | barg <- bl]
      if L.length al == (L.length bl) + 1
        then return $ bindings ++ [(_effVar (last al), EffList [] (_effLoc b))]
        else return bindings
collectEffVarBindings a b = throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)

collectEffVarBindingsInType :: (Has EnvEff sig m) => Type -> Type -> m [(EffVar, EffectType)]
collectEffVarBindingsInType a@TPrim {} b@TPrim {} = do
  checkTypeMatch a b
  return []
collectEffVarBindingsInType a@TVar {..} t = do
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
            else return []
collectEffVarBindingsInType a@TFunc {} b@TFunc {} =
  if L.length (_tfuncArgs a) /= L.length (_tfuncArgs b)
    then throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
    else do
      al <- toEffList $ _tfuncEff a
      bl <- toEffList $ _tfuncEff b
      (++)
        <$> ( (++)
                <$> ( foldM
                        (\s e -> (++) <$> (return s) <*> e)
                        []
                        [collectEffVarBindingsInType aarg barg | aarg <- a ^. tfuncArgs | barg <- b ^. tfuncArgs]
                    )
                <*> collectEffVarBindingsInType (_tfuncResult a) (_tfuncResult b)
            )
        <*> collectEffVarBindings al bl
collectEffVarBindingsInType a@TList {} b@TList {} =
  if L.length (_tlist a) == L.length (_tlist b)
    then
      foldM
        (\s e -> (++) <$> (return s) <*> e)
        []
        [collectEffVarBindingsInType ae be | ae <- (a ^. tlist) | be <- (b ^. tlist)]
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectEffVarBindingsInType a@TApp {} b@TApp {} =
  -- not support higher kind so far
  if L.length (_tappArgs a) == L.length (_tappArgs b)
    && aeq (_tappName a) (_tappName b)
    then
      foldM
        (\s e -> (++) <$> (return s) <*> e)
        []
        [collectEffVarBindingsInType aarg barg | aarg <- (a ^. tappArgs) | barg <- (b ^. tappArgs)]
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectEffVarBindingsInType a@TAnn {} b@TAnn {} =
  collectEffVarBindingsInType (_tannType a) (_tannType b)
collectEffVarBindingsInType a@BoundType {} b@BoundType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectEffVarBindingsInType at bt
collectEffVarBindingsInType a@BoundEffVarType {} b@BoundEffVarType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectEffVarBindingsInType at bt
collectEffVarBindingsInType a@BoundType {} b@BoundEffVarType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectEffVarBindingsInType at bt
collectEffVarBindingsInType a@BoundEffVarType {} b@BoundType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectEffVarBindingsInType at bt
collectEffVarBindingsInType a@TNum {} b@TNum {} =
  if (_tnum a) == (_tnum b)
    then return []
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectEffVarBindingsInType a b = throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)

checkVarBindings :: (Has EnvEff sig m) => [(TVar, Type)] -> m ()
checkVarBindings bindings = do
  foldM_
    ( \b (n, t) -> do
        if aeq (TVar n $ _tloc t) t
          then return b
          else case b ^. at n of
            Nothing -> return $ at n ?~ t $ b
            Just ot ->
              if aeq t ot
                then return b
                else throwError $ "type var binding conflict: " ++ ppr t ++ ppr (_tloc t) ++ " vs " ++ ppr ot ++ ppr (_tloc ot)
    )
    M.empty
    bindings

-- | Check all effect variable bindings
checkEffVarBindings :: (Has EnvEff sig m) => [(EffVar, EffectType)] -> m ()
checkEffVarBindings bindings = do
  foldM_
    ( \b (n, t) -> do
        if aeq (EffVar n $ _effLoc t) t
          then return b
          else case b ^. at n of
            Nothing -> return $ at n ?~ t $ b
            Just ot ->
              if aeq t ot
                then return b
                else throwError $ "eff type var binding conflict: " ++ ppr t ++ ppr (_effLoc t) ++ " vs " ++ ppr ot ++ ppr (_effLoc ot)
    )
    M.empty
    bindings

-- | Get a function type from a function defintion
funcDefType :: FuncDef -> Type
funcDefType f =
  let pos = f ^. funcLoc
      argTypes = f ^. funcArgs ^.. traverse . _2
      effType = _funcEffectType f
      resultType = _funcResultType f
      bvs = _funcBoundVars f
      ft =
        bindType bvs $
          TFunc argTypes effType resultType pos
      bes = f ^. funcBoundEffVars
      bft = bindTypeEffVar bes ft
   in bft

-- | Extract a tensor type's shape
extractTensorShape :: (Has EnvEff sig m) => Type -> m [Int]
extractTensorShape t@TList {..} =
  foldM
    ( \s e -> do
        case e of
          TNum d _ -> case d of
            Just d -> return $ s ++ [d]
            Nothing -> throwError $ "expected a static shape, but got " ++ ppr e ++ ppr (e ^. tloc)
          _ -> throwError $ "expected a number type, but got " ++ ppr e ++ ppr (e ^. tloc)
    )
    []
    _tlist
extractTensorShape t = throwError $ "expected a pair type, but got " ++ ppr t ++ ppr (_tloc t)

-- | Extract a tensor type's information
extractTensorInfo :: (Has EnvEff sig m) => Type -> m (Type, [Int])
extractTensorInfo t@TApp {..} =
  if name2String (_tvar _tappName) /= "core/prelude/tensor"
    then throwError $ "expected a tensor type, but got " ++ ppr t ++ ppr _tloc
    else
      if L.length _tappArgs /= 2
        then throwError $ "expected 2 arguments, but got " ++ ppr t ++ ppr _tloc
        else
          let et : shape : [] = _tappArgs
           in do
                s <- extractTensorShape shape
                return (et, s)
extractTensorInfo t = throwError $ "expected a tensor type, but got " ++ ppr t ++ ppr (_tloc t)

-- | Construct a number list type based on pair types
toTensorShape :: (Has EnvEff sig m) => Location -> [Int] -> m Type
toTensorShape loc l = return $ TList [TNum (Just e) loc | e <- l] loc

-- | Construct a tensor type based on number list type
toTensorType :: (Has EnvEff sig m) => Type -> [Int] -> m Type
toTensorType t shape = do
  shape' <- toTensorShape (_tloc t) shape
  return $ TApp (TVar (s2n "core/prelude/tensor") (_tloc t)) [t, shape'] (_tloc t)

-- | Test if a type is a subtype of another type
isSubType :: (Has EnvEff sig m) => Type -> Type -> m Bool
isSubType s t = do
  catchError
    ( if aeq s t
        then return False
        else do
          binds <- collectVarBindings t s
          checkVarBindings binds
          return True
    )
    (\(e :: String) -> return False)

-- | Func implementation selector
funcImplSelector :: Type -> String
-- TODO md5 is not good, better just replace the special chars
funcImplSelector t = show $ md5 $ BLU.fromString $ ppr t

uniqueFuncImplName :: String -> Type -> String
uniqueFuncImplName fn t = fn ++ (funcImplSelector t)

-- | Set a function implementation
setFuncImpl :: (Has EnvEff sig m) => String -> ImplFuncDef -> m ImplFuncDef
setFuncImpl prefix impl = do
  let funcD = impl ^. implFunDef
      fn = prefix ++ "/" ++ funcD ^. funcName
      loc = funcD ^. funcLoc
      t =
        bindTypeEffVar (funcD ^. funcBoundEffVars) $
          bindType (funcD ^. funcBoundVars) $
            TFunc (funcD ^.. funcArgs . traverse . _2) (_funcEffectType funcD) (_funcResultType funcD) loc
  ft <- getEnv $ funcs . at fn
  case ft of
    Nothing -> throwError $ "cannot find general function definition: " ++ fn ++ ppr loc
    Just ft -> do
      isSubT <- isSubType t ft
      if isSubT
        then return ()
        else
          throwError $
            "implementation type is not subtype of general type: "
              ++ ppr t
              ++ ppr loc
              ++ " vs "
              ++ ppr ft
              ++ ppr (_tloc ft)
      impls <- getEnv $ funcImpls
      let sel = uniqueFuncImplName fn t
          i = EVar (s2n sel) loc
          oldImpl = impls ^. at sel
      forMOf _Just oldImpl $ \it -> do
        throwError $ "implementation conflict: " ++ ppr it ++ " vs " ++ ppr t ++ ppr (_tloc t)
      setEnv (Just i) $ funcImpls . at sel
  return impl {_implFunDef = funcD {_funcName = fn}}
