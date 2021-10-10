{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cone.TypeChecker.Type where

import Cone.Parser.AST
import Cone.Env
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Lens
import Control.Lens.Plated
import Control.Monad
import qualified Data.ByteString.Lazy.UTF8 as BLU
import Data.Digest.Pure.MD5
import qualified Data.List as L
import Data.List.Split
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace
import GHC.Stack
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)
import Unbound.Generics.LocallyNameless.Unsafe

getKindOfTVar :: (Has EnvEff sig m) => String -> Kind -> m Kind
getKindOfTVar n defaultK = do
  k <- getEnv $ types . at n
  case k of
    Just k -> return k
    Nothing -> do
      k <- getEnv $ kindBinds . at n . non defaultK
      checkKindMatch k defaultK
      setEnv (Just k) $ kindBinds . at n
      return k

isConcreteType :: Type -> Bool
isConcreteType t =
  let vs = t ^.. fv :: [TVar]
      es = t ^.. fv :: [EffVar]
   in all (elem '/' . name2String) vs &&
      all (elem '/' . name2String) es

-- | Infer type's kind
inferTypeKind :: (Has EnvEff sig m) => Type -> m Kind
inferTypeKind a@TApp {..} = do
  let go = do
        ak <- do
          let tvn = name2String $ _tvar _tappName
              kstar = KStar _tloc
              kf =
                if null _tappArgs
                  then kstar
                  else KFunc [kstar | _ <- _tappArgs] kstar _tloc
          getKindOfTVar tvn kf
        case ak of
          KStar {} ->
            if null _tappArgs
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
          _ -> throwError $ "expected a func kind or star kind, but got " ++ ppr ak ++ ppr _tloc
  let tvn = name2String $ _tvar _tappName
  alias <- getEnv $ typeAliases . at tvn
  case alias of
    Just alias -> do
      let kstar = KStar _tloc
      forM_
        [(a, b) | a <- alias ^.. typeAliasArgs . traverse . _2 . non kstar | b <- _tappArgs]
        $ \(a, b) -> do
          t <- inferTypeKind b
          checkKindMatch t a
      let t = substs [(n, tv) | n <- alias ^.. typeAliasArgs . traverse . _1 | tv <- _tappArgs] (_typeAliasType alias)
      inferTypeKind t
    Nothing -> go
inferTypeKind a@TAnn {..} = do
  k <-
    if not $ isn't _TVar _tannType
      then do
        let tvn = name2String $ _tvar _tannType
        getKindOfTVar tvn _tannKind
      else inferTypeKind _tannType
  checkKindMatch k _tannKind
  return _tannKind
inferTypeKind b@BoundType {..} = underScope $ do
  let (bvs, t) = unsafeUnbind _boundType
      star = KStar _tloc
  mapM_ (\(v, k) -> setEnv (Just $ k ^. non star) $ types . at (name2String v)) bvs
  inferTypeKind t
inferTypeKind b@BoundEffVarType {..} = underScope $ do
  let (bvs, t) = unsafeUnbind _boundEffVarType
      star = EKStar _tloc
  mapM_ (\v -> setEnv (Just star) $ effs . at (name2String v)) bvs
  inferTypeKind t
inferTypeKind v@TVar {..} = do
  let go = do
        let tvn = name2String _tvar
            kstar = KStar _tloc
        getKindOfTVar tvn kstar
  alias <- getEnv $ typeAliases . at (name2String _tvar)
  case alias of
    Just alias ->
      if null (alias ^. typeAliasArgs)
        then inferTypeKind $ _typeAliasType alias
        else go
    Nothing -> go
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
  if not (any (isn't _TNum) args)
    then
      let arg : rest = fmap _tnum args
       in TNum (fmap f arg) (_tloc t)
    else t

evalType2 :: Type -> [Type] -> (Int -> Int -> Int) -> Type
evalType2 t args f =
  if not (any (isn't _TNum) args)
    then
      let arg : rest = fmap _tnum args
       in TNum (L.foldl' (\a b -> f <$> a <*> b) arg rest) (_tloc t)
    else t

-- | Simplize the type
inferType :: (Has EnvEff sig m) => Type -> m Type
inferType a@TApp {..} = do
  args <- mapM inferType _tappArgs
  let t = a {_tappArgs = args}
      name = name2String (_tvar _tappName)
  alias <- getEnv $ typeAliases . at name
  case alias of
    Just alias -> do
      let t' = substs [(n, tv) | n <- alias ^.. typeAliasArgs . traverse . _1 | tv <- _tappArgs] (_typeAliasType alias)
      inferType t'
    Nothing -> do
      case name of
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
  return $ bindTypeVar bts t
inferType b@BoundEffVarType {..} = do
  let (ets, t) = unsafeUnbind _boundEffVarType
  t <- inferType t
  return $ bindTypeEffVar ets t
inferType f@TFunc {..} = do
  args <- mapM inferType _tfuncArgs
  eff <- inferEffType _tfuncEff
  res <- inferType _tfuncResult
  return f {_tfuncArgs = args, _tfuncEff = eff, _tfuncResult = res}
inferType l@TList {..} = do
  es <- mapM inferType _tlist
  return l {_tlist = es}
inferType v@TVar {..} = do
  let go = do
        t <- getEnv $ typeBinds . at (name2String _tvar)
        case t of
          Just t -> inferType t
          Nothing -> return v
  alias <- getEnv $ typeAliases . at (name2String _tvar)
  case alias of
    Just alias ->
      if null (alias ^. typeAliasArgs)
        then inferType $ _typeAliasType alias
        else go
    Nothing -> go
inferType t = return t

-- | Check a type kind
checkTypeKind :: (Has EnvEff sig m) => Kind -> m ()
checkTypeKind k = do
  case k of
    KStar {} -> return ()
    _ -> throwError $ "expected a star kind, but got " ++ ppr k ++ ppr (_kloc k)

inferEffType :: (Has EnvEff sig m) => EffectType -> m EffectType
inferEffType v@EffVar {..} = do
  t <- getEnv $ effTypeBinds . at (name2String _effVar)
  case t of
    Just t -> inferEffType t
    Nothing -> return v
inferEffType a@EffApp {..} = do
  app <- inferEffType _effAppName
  args <- mapM inferType _effAppArgs
  return a {_effAppName = app, _effAppArgs = args}
inferEffType l@EffList {..} = do
  ls <- mapM inferEffType _effList
  return l {_effList = ls}

getEffKindOfEffVar :: (Has EnvEff sig m) => String -> EffKind -> m EffKind
getEffKindOfEffVar n defaultK = do
  k <- getEnv $ effs . at n
  case k of
    Just k -> return k
    Nothing -> do
      k <- getEnv $ effKindBinds . at n . non defaultK
      checkEffKindMatch k defaultK
      setEnv (Just k) $ effKindBinds . at n
      return k

-- | Infer an effect type kind
inferEffKind :: (Has EnvEff sig m) => EffectType -> m EffKind
inferEffKind v@EffVar {..} = do
  let kstar = EKStar _effLoc
  getEffKindOfEffVar (name2String _effVar) kstar
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
              --checkTypeKind e
              --checkTypeKind b
              checkKindMatch e b
          checkEffKind _ekfuncResult
          return _ekfuncResult
    _ -> throwError $ "expected a func eff kind, but got " ++ ppr ak ++ ppr _effLoc
inferEffKind l@EffList {..} = do
  ls <- mapM inferEffKind _effList
  mapM_ checkEffKind ls
  return $ EKList ls _effLoc

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
                || isn't _Nothing (M.lookup (name2String $ _effVar e) es)
          )
          (_effList effs)
  al <- mapM inferEffType $ L.sortBy acompare el ++ L.sortBy acompare vl
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
            l L.\\ map (l !!) (L.findIndices (aeq e) l)
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
  return $ EffList l pos
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
      return $ bindTypeEffVar ets $ bindTypeVar (L.drop argsLen bts) $ substs binds tt

-- | Infer a result type of application type
inferAppResultType :: (Has EnvEff sig m) => Type -> [Type] -> [Type] -> m (Type, Type)
inferAppResultType f@TFunc {} bargs args = do
  let fArgTypes = _tfuncArgs f
  when (L.length fArgTypes /= L.length args) $ throwError $ "function type argument number mismatch: " ++ ppr fArgTypes ++ ppr (fArgTypes ^.. traverse . tloc) ++ " vs " ++ ppr args ++ ppr (args ^.. traverse . tloc)
  bindings <-
    foldM
      (\s e -> (++) s <$> e)
      []
      [collectVarBindings True a b | a <- fArgTypes | b <- args]
      >>= checkVarBindings
  let ft = substs bindings f
  return (_tfuncResult ft, ft)
inferAppResultType t _ [] = return (t, t)
inferAppResultType t _ _ = throwError $ "expected a function type, but got " ++ ppr t ++ ppr (_tloc t)

-- | Infer the result effect type of application type
inferAppResultEffType :: (Has EnvEff sig m) => Type -> [Type] -> [Type] -> m EffectType
inferAppResultEffType f@TFunc {} targs args = do
  let fArgTypes = _tfuncArgs f
  when (L.length fArgTypes /= L.length args) $ throwError $ "function type argument number mismatch: " ++ ppr fArgTypes ++ ppr (fArgTypes ^.. traverse . tloc) ++ " vs " ++ ppr args ++ ppr (args ^.. traverse . tloc)
  bindings <-
    foldM
      (\s e -> (++) s <$> e)
      []
      [collectVarBindings True a b | a <- fArgTypes | b <- args]
      >>= checkVarBindings
  resEff <- toEffList $ _tfuncEff f
  funcEff <- toEffList $ _tfuncEff f
  let eff = substs bindings resEff
  effBindings <-
    ( (++)
        <$> foldM
          (\s e -> (++) s <$> e)
          []
          [collectEffVarBindingsInType True a b | a <- fArgTypes | b <- args]
        <*> collectEffVarBindings True funcEff resEff
      )
      >>= checkEffVarBindings
  toEffList $ substs effBindings eff
inferAppResultEffType t _ [] = return $ EffList [] (_tloc t)
inferAppResultEffType t _ _ = throwError $ "expected a function type, but got " ++ ppr t ++ ppr (_tloc t)

-- | Collect all variable bindings
collectVarBindings :: (Has EnvEff sig m) => Bool -> Type -> Type -> m [(TVar, Type)]
collectVarBindings bi a@TPrim {} b@TPrim {} = do
  checkTypeMatch a b
  return []
collectVarBindings bi a@TVar {..} t = do
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
collectVarBindings bi t a@TVar {..} = do
  if bi
    then collectVarBindings bi a t
    else throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr t ++ ppr _tloc
collectVarBindings bi a@TFunc {} b@TFunc {} =
  if L.length (_tfuncArgs a) /= L.length (_tfuncArgs b)
    then throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
    else do
      al <- toEffList $ _tfuncEff a
      bl <- toEffList $ _tfuncEff b
      (++)
        <$> ( (++)
                <$> foldM
                  (\s e -> (++) s <$> e)
                  []
                  [collectVarBindings bi aarg barg | aarg <- a ^. tfuncArgs | barg <- b ^. tfuncArgs]
                <*> collectVarBindings bi (_tfuncResult a) (_tfuncResult b)
            )
        <*> collectVarBindingsInEff bi al bl
collectVarBindings bi a@TList {} b@TList {} =
  if L.length (_tlist a) == L.length (_tlist b)
    then
      foldM
        (\s e -> (++) s <$> e)
        []
        [collectVarBindings bi ae be | ae <- a ^. tlist | be <- b ^. tlist]
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectVarBindings bi a@TApp {} b@TApp {} =
  if L.length (_tappArgs a) == L.length (_tappArgs b)
    then do
      f <- collectVarBindings bi (_tappName a) (_tappName b)
      args <-
        foldM
          (\s e -> (++) s <$> e)
          []
          [collectVarBindings bi aarg barg | aarg <- a ^. tappArgs | barg <- b ^. tappArgs]
      return $ f ++ args
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectVarBindings bi a@TAnn {} b@TAnn {} =
  collectVarBindings bi (_tannType a) (_tannType b)
collectVarBindings bi a@BoundType {} b@BoundType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectVarBindings bi at bt
collectVarBindings bi a@BoundEffVarType {} b@BoundEffVarType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectVarBindings bi at bt
collectVarBindings bi a@BoundType {} b@BoundEffVarType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectVarBindings bi at bt
collectVarBindings bi a@BoundEffVarType {} b@BoundType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectVarBindings bi at bt
collectVarBindings bi a@TNum {} b@TNum {} =
  if _tnum a == _tnum b
    then return []
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectVarBindings bi a b = throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)

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
collectVarBindingsInEff :: (Has EnvEff sig m) => Bool -> EffectType -> EffectType -> m [(TVar, Type)]
collectVarBindingsInEff bi s@EffVar {} _ = return []
collectVarBindingsInEff bi a b@EffVar {} = do
  if bi
    then collectVarBindingsInEff bi b a
    else throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
collectVarBindingsInEff bi a@EffApp {} b@EffApp {} =
  if L.length (a ^. effAppArgs) /= L.length (b ^. effAppArgs)
    || not (aeq (_effAppName a) (_effAppName b))
    then throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
    else
      foldM
        (\s e -> (++) s <$> e)
        []
        [collectVarBindings bi aarg barg | aarg <- a ^. effAppArgs | barg <- b ^. effAppArgs]
collectVarBindingsInEff bi a@EffList {} b@EffList {} = do
  let al = a ^. effList
  let bl = b ^. effList
  let error = throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
  when (L.length al > L.length bl) $
    if L.length al == L.length bl + 1
      then do
        is <- isEffVar $ last al
        unless is error
      else error
  when (L.length al < L.length bl) $ do
    if null al
      then error
      else do
        is <- isEffVar $ last al
        unless is error
  foldM
    (\s e -> (++) s <$> e)
    []
    [collectVarBindingsInEff bi aarg barg | aarg <- al | barg <- bl]
collectVarBindingsInEff bi a b = throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)

-- | Check all effect variables
collectEffVarBindings :: (Has EnvEff sig m) => Bool -> EffectType -> EffectType -> m [(EffVar, EffectType)]
collectEffVarBindings bi ev@EffVar {..} e = do
  is <- isEffVar ev
  if is
    then return [(_effVar, e)]
    else return []
collectEffVarBindings bi a b@EffVar {} = do
  if bi
    then collectEffVarBindings bi b a
    else throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
collectEffVarBindings bi a@EffApp {} b@EffApp {} = do
  if L.length (a ^. effAppArgs) /= L.length (b ^. effAppArgs)
    || not (aeq (_effAppName a) (_effAppName b))
    then throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
    else do
      foldM
        (\s e -> (++) s <$> e)
        []
        [collectVarBindings bi aarg barg | aarg <- a ^. effAppArgs | barg <- b ^. effAppArgs]
        >>= checkVarBindings
  return []
collectEffVarBindings bi a@EffList {} b@EffList {} = do
  let al = a ^. effList
  let bl = b ^. effList
  let error = throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)
  when (L.length al > L.length bl) $
    if L.length al == L.length bl + 1
      then do
        is <- isEffVar $ last al
        unless is error
      else error
  when (L.length al < L.length bl) $
    if null al
      then error
      else do
        is <- isEffVar $ last al
        unless is error
  if L.length al < L.length bl
    then do
      bindings <-
        foldM
          (\s e -> (++) s <$> e)
          []
          [collectEffVarBindings bi aarg barg | aarg <- init al | barg <- bl]
      return $ bindings ++ [(_effVar (last al), EffList (drop (L.length al - 1) bl) (_effLoc b))]
    else do
      bindings <-
        foldM
          (\s e -> (++) s <$> e)
          []
          [collectEffVarBindings bi aarg barg | aarg <- al | barg <- bl]
      if L.length al == L.length bl + 1
        then return $ bindings ++ [(_effVar (last al), EffList [] (_effLoc b))]
        else return bindings
collectEffVarBindings bi a b = throwError $ "eff type mismatch: " ++ ppr a ++ ppr (_effLoc a) ++ " vs " ++ ppr b ++ ppr (_effLoc b)

collectEffVarBindingsInType :: (Has EnvEff sig m) => Bool -> Type -> Type -> m [(EffVar, EffectType)]
collectEffVarBindingsInType bi a@TPrim {} b@TPrim {} = do
  checkTypeMatch a b
  return []
collectEffVarBindingsInType bi a@TVar {..} t = do
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
collectEffVarBindingsInType bi a b@TVar {} = do
  if bi
    then collectEffVarBindingsInType bi b a
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectEffVarBindingsInType bi a@TFunc {} b@TFunc {} =
  if L.length (_tfuncArgs a) /= L.length (_tfuncArgs b)
    then throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
    else do
      al <- toEffList $ _tfuncEff a
      bl <- toEffList $ _tfuncEff b
      (++)
        <$> ( (++)
                <$> foldM
                  (\s e -> (++) s <$> e)
                  []
                  [collectEffVarBindingsInType bi aarg barg | aarg <- a ^. tfuncArgs | barg <- b ^. tfuncArgs]
                <*> collectEffVarBindingsInType bi (_tfuncResult a) (_tfuncResult b)
            )
        <*> collectEffVarBindings bi al bl
collectEffVarBindingsInType bi a@TList {} b@TList {} =
  if L.length (_tlist a) == L.length (_tlist b)
    then
      foldM
        (\s e -> (++) s <$> e)
        []
        [collectEffVarBindingsInType bi ae be | ae <- a ^. tlist | be <- b ^. tlist]
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectEffVarBindingsInType bi a@TApp {} b@TApp {} =
  if L.length (_tappArgs a) == L.length (_tappArgs b)
    then do
      f <- collectEffVarBindingsInType bi (_tappName a) (_tappName b)
      args <-
        foldM
          (\s e -> (++) s <$> e)
          []
          [collectEffVarBindingsInType bi aarg barg | aarg <- a ^. tappArgs | barg <- b ^. tappArgs]
      return $ f ++ args
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectEffVarBindingsInType bi a@TAnn {} b@TAnn {} =
  collectEffVarBindingsInType bi (_tannType a) (_tannType b)
collectEffVarBindingsInType bi a@BoundType {} b@BoundType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectEffVarBindingsInType bi at bt
collectEffVarBindingsInType bi a@BoundEffVarType {} b@BoundEffVarType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectEffVarBindingsInType bi at bt
collectEffVarBindingsInType bi a@BoundType {} b@BoundEffVarType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectEffVarBindingsInType bi at bt
collectEffVarBindingsInType bi a@BoundEffVarType {} b@BoundType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectEffVarBindingsInType bi at bt
collectEffVarBindingsInType bi a@TNum {} b@TNum {} =
  if _tnum a == _tnum b
    then return []
    else throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)
collectEffVarBindingsInType bi a b = throwError $ "type mismatch: " ++ ppr a ++ ppr (_tloc a) ++ " vs " ++ ppr b ++ ppr (_tloc b)

getSpecialTypes :: (Has EnvEff sig m) => [Type] -> m [Type]
getSpecialTypes (t : ts) =
  foldM
    ( \s t -> do
        foldM
          ( \r e -> do
              is <- isEqOrSubType e t
              if is
                then return $ r ++ [e]
                else do
                  is <- isEqOrSubType t e
                  if is
                    then return $ r ++ [t]
                    else return $ r ++ [e, t]
          )
          []
          s
    )
    [t]
    ts
getSpecialTypes [] = return []

groupTypes :: (Has EnvEff sig m) => [[Type]] -> m [[Type]]
groupTypes rels = do
  let newRels = L.nubBy aeq [L.unionBy aeq a b| a <- rels, b <- rels, not $ null (L.intersectBy aeq a b)]
  if aeq newRels rels then return newRels
  else groupTypes newRels

checkVarBindings :: (Has EnvEff sig m) => [(TVar, Type)] -> m [(TVar, Type)]
checkVarBindings bindings = do
  groups <- groupTypes $ map (\(v, t) -> [TVar v $ _tloc t, t]) bindings
  bs <- forM groups $ \g -> do
    (vars, nonVars) <-
      foldM
        ( \(vars, nonVars) e -> do
            if isn't _TVar e
              then return (vars, nonVars ++ [e])
              else do
                k <- getEnv $ types . at (name2String $ _tvar e)
                case k of
                  Just _ -> return (vars, nonVars ++ [e])
                  Nothing -> return (vars ++ [e], nonVars)
        )
        ([], [])
        g
    nonVars <- getSpecialTypes nonVars
    if L.length nonVars > 1
      then throwError $ "var bind conflicts: " ++ ppr vars ++ " to " ++ ppr [(v, loc) | v <- nonVars | loc <- nonVars ^.. traverse . tloc]
      else return [(_tvar v, t) | v <- vars, t <- nonVars]
  let allBinds = join bs
  forM_ allBinds $ \(v, t) -> do
    setEnv (Just t) $ typeBinds . at (name2String v)
  return allBinds

getSpecialEffTypes :: (Has EnvEff sig m) => [EffectType] -> m [EffectType]
getSpecialEffTypes (t : ts) =
  foldM
    ( \s t -> do
        foldM
          ( \r e -> do
              is <- isEqOrSubEffType e t
              if is
                then return $ r ++ [e]
                else do
                  is <- isEqOrSubEffType t e
                  if is
                    then return $ r ++ [t]
                    else return $ r ++ [e, t]
          )
          []
          s
    )
    [t]
    ts
getSpecialEffTypes [] = return []

groupEffTypes :: (Has EnvEff sig m) => [[EffectType]] -> m [[EffectType]]
groupEffTypes rels = do
  let newRels = L.nubBy aeq [L.unionBy aeq a b| a <- rels, b <- rels, not $ null (L.intersectBy aeq a b)]
  if aeq newRels rels then return newRels
  else groupEffTypes newRels

checkEffVarBindings :: (Has EnvEff sig m) => [(EffVar, EffectType)] -> m [(EffVar, EffectType)]
checkEffVarBindings bindings = do
  groups <- groupEffTypes $ map (\(v, t) -> [EffVar v $ _effLoc t, t]) bindings
  bs <- forM groups $ \g -> do
    (vars, nonVars) <-
      foldM
        ( \(vars, nonVars) e -> do
            if isn't _EffVar e
              then return (vars, nonVars ++ [e])
              else do
                k <- getEnv $ effs . at (name2String $ _effVar e)
                case k of
                  Just _ -> return (vars, nonVars ++ [e])
                  Nothing -> return (vars ++ [e], nonVars)
        )
        ([], [])
        g
    nonVars <- getSpecialEffTypes nonVars
    if L.length nonVars > 1
      then throwError $ "eff var bind conflicts: " ++ ppr vars ++ " to " ++ ppr [(v, loc) | v <- nonVars | loc <- nonVars ^.. traverse . effLoc]
      else return [(_effVar v, t) | v <- vars, t <- nonVars]
  let allBinds = join bs
  forM_ allBinds $ \(v, t) -> do
    setEnv (Just t) $ effTypeBinds . at (name2String v)
  return allBinds

-- | Get a function type from a function defintion
funcDefType :: FuncDef -> Type
funcDefType f =
  let pos = f ^. funcLoc
      argTypes = f ^. funcArgs ^.. traverse . _2
      effType = _funcEffectType f
      resultType = _funcResultType f
      bvs = _funcBoundVars f
      ft =
        bindTypeVar bvs $
          TFunc argTypes effType resultType pos
      bes = f ^. funcBoundEffVars
      bft = bindTypeEffVar bes ft
   in bft

-- | Test if a type is a subtype of another type
isSubType :: (Has EnvEff sig m) => Type -> Type -> m Bool
isSubType s t = do
  catchError
    ( if aeq s t
        then return False
        else do
          collectVarBindings False t s >>= checkVarBindings
          return True
    )
    (\(e :: String) -> return False)

-- | Test if a type is a subtype of another type
isEqOrSubType :: (Has EnvEff sig m) => Type -> Type -> m Bool
isEqOrSubType s t = do
  catchError
    ( do
        collectVarBindings False t s >>= checkVarBindings
        return True
    )
    (\(e :: String) -> return False)

-- | Test if a type is a subtype of another type
isSubEffType :: (Has EnvEff sig m) => EffectType -> EffectType -> m Bool
isSubEffType s t = do
  catchError
    ( if aeq s t
        then return False
        else do
          collectEffVarBindings False t s >>= checkEffVarBindings
          return True
    )
    (\(e :: String) -> return False)

-- | Test if a type is a subtype of another type
isEqOrSubEffType :: (Has EnvEff sig m) => EffectType -> EffectType -> m Bool
isEqOrSubEffType s t = do
  catchError
    ( do
        collectEffVarBindings False t s >>= checkEffVarBindings
        return True
    )
    (\(e :: String) -> return False)

-- | Set a function type into env
setFuncType :: (Has EnvEff sig m) => String -> Type -> m ()
setFuncType n t = do
  setEnv (Just t) $ funcs . at n
  l <- getEnv localState
  -- clear the local state
  setEnv (M.delete n l) localState

-- | Get a function type into env
getFuncType :: (Has EnvEff sig m) => Location -> String -> m Type
getFuncType pos n = do
  -- try to find in local state first
  v <- getEnv $ localState . at n
  case v of
    Just v -> inferType v
    Nothing -> do
      -- try to find in local scope
      v <- getEnv $ funcs . at n
      case v of
        Just v -> inferType v
        Nothing -> throwError $ "cannot find variable: " ++ n ++ ppr pos

-- | Get real name if there is alias prefix
getNamePath :: (Has EnvEff sig m) => Module -> String -> m String
getNamePath m n = do
  aliases <-
    foldM
      ( \s i ->
          case i ^. importAlias of
            Just alias -> do
              let old = s ^. at alias
              case old of
                Just old -> throwError $ "import alias conflict: import " ++ ppr old ++ " as " ++ ppr alias ++ " vs " ++ ppr i ++ ppr (_importLoc i)
                Nothing -> return $ s & at alias ?~ i ^. importPath
            Nothing -> return s
      )
      M.empty
      $ m ^. imports
  let n' = last $ splitOn "/" n
      ns = join $ L.intersperse "/" $ L.init $ splitOn "/" n
  case aliases ^. at ns of
    Just prefix -> return $ prefix ++ "/" ++ n'
    Nothing -> return n

filterOutAliasImports :: Module -> String -> [String] -> [String]
filterOutAliasImports m n ns =
  let aliasImports =
        L.nub $
          L.foldl'
            ( \s i ->
                case i ^. importAlias of
                  Just alias -> s ++ [(i ^. importPath) ++ "/" ++ n]
                  Nothing -> s
            )
            []
            $ m ^. imports
   in L.nub ns L.\\ aliasImports

-- | Func implementation selector
funcImplSelector :: Type -> String
-- TODO md5 is not good, better just replace the special chars
funcImplSelector t = show $ md5 $ BLU.fromString $ ppr t

uniqueFuncImplName :: String -> Type -> String
uniqueFuncImplName fn t = fn ++ funcImplSelector t

searchFunc :: (Has EnvEff sig m) => Module -> String -> Location -> m String
searchFunc m fn loc = do
  let prefixes =
        L.nub $
          "" :
          (m ^. moduleName ++ "/") :
          "core/prelude/" :
          map (\i -> i ^. importPath ++ "/") (m ^. imports)
  n <- getNamePath m fn
  fs <- getEnv funcs
  found <-
    filterOutAliasImports m n
      <$> foldM
        ( \f p -> do
            let ffn = p ++ n
            case fs ^. at ffn of
              Just _ -> return $ f ++ [ffn]
              Nothing -> return f
        )
        []
        prefixes
  if null found
    then throwError $ "no function definition found for : " ++ fn ++ ppr loc
    else
      if L.length found == 1
        then return $ head found
        else throwError $ "found more than one function for " ++ fn ++ ppr found ++ ppr loc

-- | Set a function implementation
setFuncImpl :: (Has EnvEff sig m) => String -> Module -> ImplFuncDef -> m ImplFuncDef
setFuncImpl prefix m impl = do
  let funcD = impl ^. implFunDef
      fn = prefix ++ "/" ++ funcD ^. funcName
      loc = funcD ^. funcLoc
      t =
        bindTypeEffVar (funcD ^. funcBoundEffVars) $
          bindTypeVar (funcD ^. funcBoundVars) $
            TFunc (funcD ^.. funcArgs . traverse . _2) (_funcEffectType funcD) (_funcResultType funcD) loc
  intfn <- searchFunc m (funcD ^. funcName) loc
  ft <- fromJust <$> getEnv (funcs . at intfn)
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
  let sel = uniqueFuncImplName fn t
      i = EVar (s2n sel) loc
  addFuncImpl intfn i t
  return impl {_implFunDef = funcD {_funcName = fn}}

bindEDef :: EffectDef -> EffectDef
bindEDef edef =
  let boundVars = L.nub $ edef ^.. effectArgs . traverse
      edef' = over (effectIntfs . traverse) (bindEffIntf boundVars) edef
   in BoundEffectDef (bind (boundVars ^.. traverse . _1) edef') (_effectLoc edef)

bindEffIntf :: [(TVar, Maybe Kind)] -> FuncIntf -> FuncIntf
bindEffIntf bvs intf =
  let boundVars = L.nub $ bvs ++ intf ^. intfBoundVars
      boundEffVars = L.nub $ intf ^. intfBoundEffVars
      loc = intf ^. intfLoc
   in BoundEffFuncIntf (bind boundEffVars $ BoundFuncIntf (bind (boundVars ^.. traverse . _1) intf) loc) loc

bindTDef :: TypeDef -> TypeDef
bindTDef tdef =
  let boundVars = L.nub $ tdef ^.. typeArgs . traverse . _1
   in BoundTypeDef (bind boundVars tdef) (_typeLoc tdef)

bindTAlias :: TypeAlias -> TypeAlias
bindTAlias talias =
  let boundVars = L.nub $ talias ^.. typeAliasArgs . traverse . _1
   in BoundTypeAlias (bind boundVars talias) (_typeAliasLoc talias)

bindFDef :: FuncDef -> FuncDef
bindFDef fdef =
  let boundVars = L.nub $ fdef ^. funcBoundVars
      boundEffVars = L.nub $ fdef ^. funcBoundEffVars
      loc = fdef ^. funcLoc
      expr = transform bindExpr <$> _funcExpr fdef
   in BoundEffFuncDef (bind boundEffVars $ BoundFuncDef (bind (boundVars ^.. traverse . _1) fdef {_funcExpr = expr}) loc) loc

bindExpr :: Expr -> Expr
bindExpr l@ELam {..} =
  let boundVars = L.nub _elamBoundVars
      boundEffVars = L.nub _elamBoundEffVars
   in  EBoundEffTypeVars (bind boundEffVars $ EBoundTypeVars (bind (boundVars ^.. traverse . _1) l) _eloc) _eloc
bindExpr expr = expr

