{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Cone.TypeChecker.Type where

import Cone.Parser.AST
import Cone.TypeChecker.Env
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
        then throwError $ "kind arguments mismatch: " ++ ppr _tappArgs ++ " vs " ++ ppr _kfuncArgs ++ ppr a
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
    _ -> return t
inferType a@TAnn {..} = do
  t <- inferType _tannType
  return a {_tannType = t}
inferType b@BoundType {..} = do
  let (bts, t) = unbindTypeSample b
  t <- inferType t
  return b {_boundType = bind bts t}
inferType f@TFunc {..} = do
  args <- mapM inferType _tfuncArgs
  eff <- mapM inferEffectType _tfuncEff
  res <- inferType _tfuncResult
  return f {_tfuncArgs = args, _tfuncEff = eff, _tfuncResult = res}
inferType t = return t

checkTypeKind :: (Has EnvEff sig m) => Kind -> m ()
checkTypeKind k = do
  case k of
    KStar {} -> return ()
    _ -> throwError $ "expected a star kind, but got " ++ ppr k

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
              checkKindMatch e b
          checkEffKind _ekfuncResult
          return _ekfuncResult
    _ -> throwError $ "expected a func eff kind, but got " ++ ppr ak
inferEffKind a@EffAnn {..} = do
  k <- inferEffKind _effAnnType
  checkEffKind k
  checkEffKindMatch k _effAnnKind
  return _effAnnKind
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

inferEffectType :: (Has EnvEff sig m) => EffectType -> m EffectType
inferEffectType a@EffApp {..} = do
  args <- mapM inferType _effAppArgs
  return a {_effAppArgs = args}
inferEffectType a@EffAnn {..} = do
  e <- inferEffectType _effAnnType
  return a {_effAnnType = e}
inferEffectType b@BoundEffType {..} = do
  let (bts, t) = unbindEffTypeSample b
  t <- inferEffectType t
  return b {_boundEffType = bind bts t}
inferEffectType l@EffList {..} = do
  ls <- mapM inferEffectType _effList
  return l {_effList = ls}
inferEffectType e = return e

checkEffKind :: (Has EnvEff sig m) => EffKind -> m ()
checkEffKind k = do
  case k of
    EKStar {} -> return ()
    EKList {..} -> mapM_ checkEffKind _ekList
    _ -> throwError $ "expected a star eff kind, but got " ++ ppr k



checkTypeMatch :: (Has EnvEff sig m) => Type -> Type -> m ()
checkTypeMatch a b = do
  if aeq a b
    then return ()
    else throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b

checkKindMatch :: (Has EnvEff sig m) => Kind -> Kind -> m ()
checkKindMatch a b = do
  if aeq a b
    then return ()
    else throwError $ "type kind mismatch: " ++ ppr a ++ " vs " ++ ppr b

checkEffTypeMatch :: (Has EnvEff sig m) => EffectType -> EffectType -> m ()
checkEffTypeMatch a b = do
  al <- toEffList a
  bl <- toEffList b
  let pos = _effLoc al
  if aeq (al ^. effList) (bl ^. effList)
    && aeq
      (fmap closeEffType $ fmap (\e -> EffVar e pos) $ al ^. effBoundVar)
      (fmap closeEffType $ fmap (\e -> EffVar e pos) $ bl ^. effBoundVar)
    then return ()
    else throwError $ "eff type mismatch: " ++ ppr a ++ " vs " ++ ppr b

checkEffKindMatch :: (Has EnvEff sig m) => EffKind -> EffKind -> m ()
checkEffKindMatch a b = do
  if aeq a b
    then return ()
    else throwError $ "eff type kind mismatch: " ++ ppr a ++ " vs " ++ ppr b
toEffList :: (Has EnvEff sig m) => EffectType -> m EffectType
toEffList a@EffVar {..} = return $ EffList [a] Nothing _effLoc
toEffList a@EffApp {..} = return $ EffList [a] Nothing _effLoc
toEffList a@EffTotal {..} = return $ EffList [a] Nothing _effLoc
toEffList a@EffList {} = return a
toEffList EffAnn {..} = toEffList _effAnnType
toEffList a@BoundEffType {} = do
  ua <- unbindEffType a
  toEffList ua

mergeEffs :: (Has EnvEff sig m) => EffectType -> EffectType -> m EffectType
mergeEffs a@EffList {} b@EffList {} = do
  let al = a ^. effList
      bl = b ^. effList
      av = a ^. effBoundVar
      bv = a ^. effBoundVar
      pos = _effLoc a
      v = case av of
        Just _ -> av
        Nothing -> bv
      l = L.unionBy aeq al bl
  return $ EffList l v pos
mergeEffs a b = do
  al <- toEffList a
  bl <- toEffList b
  mergeEffs al bl

removeEff :: (Has EnvEff sig m) => EffectType -> EffectType -> m EffectType
removeEff f@EffList {} e@EffList {} = do
  let fl = f ^. effList
      el = e ^. effList
      fv = f ^. effBoundVar
      ev = e ^. effBoundVar
      pos = _effLoc f
  v <- case fv of
    Just _ -> case ev of
      Just _ -> return Nothing
      Nothing -> return fv
    Nothing -> case ev of
      Just ev -> throwError $ "eff has no variable, cannot be removed"
      Nothing -> return Nothing
  l <-
    foldM
      ( \l e -> do
          case L.findIndex (aeq e) l of
            Just idx -> return $ L.deleteBy aeq e l
            Nothing -> throwError $ "eff " ++ ppr l ++ " has no " ++ ppr e ++ ", cannot be removed"
      )
      fl
      el
  return $ EffList l v pos
removeEff f e = do
  fl <- toEffList f
  el <- toEffList e
  removeEff fl el

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
      [collectVarBindings a b | a <- fArgTypes | b <- args]
  checkVarBindings bindings
  inferType $ substs bindings $ _tfuncResult f
inferAppResultType t _ = throwError $ "expected a function type, but got " ++ ppr t

inferAppResultEffType :: (Has EnvEff sig m) => Type -> [Type] -> m EffectType
inferAppResultEffType f@TFunc {} args = do
  let fArgTypes = _tfuncArgs f
  if L.length fArgTypes /= L.length args
    then throwError $ "function type argument number mismatch: " ++ ppr fArgTypes ++ " vs " ++ ppr args
    else return ()
  bindings <-
    foldM
      (\s e -> (++) <$> return s <*> e)
      []
      [collectVarBindings a b | a <- fArgTypes | b <- args]
  checkVarBindings bindings
  let resEff = case _tfuncEff f of
        Just e -> e
        Nothing -> EffTotal $ _tloc f
  return $ substs bindings resEff
inferAppResultEffType t _ = throwError $ "expected a function type, but got " ++ ppr t

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
        else throwError $ "try to rebind type: " ++ ppr a ++ " to " ++ show t
    Nothing ->
      let fvars = t ^.. fv
       in if L.foldl' (\r e -> aeq e _tvar || r) False fvars
            then throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr t
            else return [(_tvar, t)]
collectVarBindings a@TFunc {} b@TFunc {} =
  if L.length (_tfuncArgs a) /= L.length (_tfuncArgs b)
    then throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b
    else
      (++)
        <$> ( foldM
                (\s e -> (++) <$> (return s) <*> e)
                []
                [collectVarBindings aarg barg | aarg <- a ^. tfuncArgs | barg <- b ^. tfuncArgs]
            )
        <*> collectVarBindings (_tfuncResult a) (_tfuncResult b)
collectVarBindings a@TApp {} b@TApp {} =
  -- not support higher kind so far
  if L.length (_tappArgs a) == L.length (_tappArgs b)
    && aeq (_tappName a) (_tappName b)
    then
      foldM
        (\s e -> (++) <$> (return s) <*> e)
        []
        [collectVarBindings aarg barg | aarg <- (a ^. tappArgs) | barg <- (b ^. tappArgs)]
    else throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b
collectVarBindings a@TAnn {} b@TAnn {} =
  collectVarBindings (_tannType a) (_tannType b)
collectVarBindings a@BoundType {} b@BoundType {} = do
  at <- unbindType a
  bt <- unbindType b
  collectVarBindings at bt
collectVarBindings a@TNum {} b@TNum {} =
  if (_tnum a) == (_tnum b)
    then return []
    else throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b
collectVarBindings a b = throwError $ "type mismatch: " ++ ppr a ++ " vs " ++ ppr b

checkVarBindings :: (Has EnvEff sig m) => [(TVar, Type)] -> m ()
checkVarBindings bindings = do
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

funcDefType :: FuncDef -> Type
funcDefType f =
  let pos = f ^. funcLoc
      argTypes = f ^. funcArgs ^.. traverse . _2
      effType = f ^. funcEffectType . (non $ EffTotal pos)
      resultType = f ^. funcResultType
      ft =
        BoundType $
          bind (f ^. funcBoundVars) $
            TFunc argTypes (Just effType) resultType pos
   in ft
