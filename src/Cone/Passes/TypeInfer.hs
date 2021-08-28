{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ParallelListComp #-}

module Cone.Passes.TypeInfer(infer) where

import Cone.Parser.AST
import Control.Lens.Plated
import Control.Lens
import Unbound.Generics.LocallyNameless hiding (fresh, Fresh(..))
import Unbound.Generics.LocallyNameless.Unsafe
import Control.Effect.State
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.Sum
import Control.Carrier.State.Strict
import Control.Carrier.Error.Either
import Control.Carrier.Fresh.Strict
import qualified Data.Map as M
import qualified Data.List as L
import Control.Monad

type Eff s e = Fresh :+: State s :+: Error e

type TypeKinds = M.Map String Kind
type EffKinds  = M.Map String EffKind
type EffIntfTypes = M.Map String Type
type ExprTypes = M.Map String Type

data Scope = Scope{_typeKinds::TypeKinds, _effKinds::EffKinds, _exprTypes:: ExprTypes}

makeLenses ''Scope

data Env = Env{_types:: TypeKinds,
               _funcs:: ExprTypes,
               _effs :: EffKinds,
               _effIntfs :: EffIntfTypes}
            deriving (Show)

makeLenses ''Env

initialEnv = Env{_types=M.empty, _funcs=M.empty,
                 _effs=M.empty, _effIntfs=M.empty}

type EnvEff = Eff Env String

initTypeDef :: (Has EnvEff sig m) => Module -> m ()
initTypeDef m = do
  env <- get @Env
  tkinds <- ts env
  put $ set types tkinds env
  where tdefs = universeOn (topStmts.traverse._TDef) m
        ts env = foldM insertTypeKind (env ^. types) tdefs
        insertTypeKind ts t =
           let tn = t ^. typeName
             in case M.lookup tn ts of
                 Just ot -> throwError $
                    "redefine a type: " ++ tn  ++ " vs " ++ show ot
                 Nothing -> return $ M.insert tn (typeKind t) ts 
        typeKind t = 
          let loc = _typeLoc t
              args = t ^. typeArgs
              star = KStar loc
            in if args == [] then star
                else KFunc (fmap (\(_, kk) -> case kk of
                                     Nothing -> star
                                     Just kkk -> kkk) args) star loc

initTypeConDef :: (Has EnvEff sig m) => Module -> m ()
initTypeConDef m = do
  env <- get @Env
  tconTypes <- tcons env
  put $ set funcs tconTypes env
  where tdefs = universeOn (topStmts.traverse._TDef) m
        tcons env = 
          let globalTypes = (fmap (\n -> s2n n) $ M.keys (env ^.types))
           in foldM (insertTconType globalTypes) (env ^. funcs) tdefs
        insertTconType globalTypes fs t = 
           let cons = t ^. typeCons
               f = \fs c -> do
                 let cn = c ^. typeConName
                     cargs = c ^. typeConArgs
                     pos = c ^.typeConLoc
                     targs = (t ^.. typeArgs.traverse._1) ++ globalTypes
                     b = bind targs cargs
                     fvars = (b ^..fv):: [TVar]
                  in do
                      if fvars /= [] then throwError $ 
                        "type constructor's type variables should " ++ 
                        "only exists in type arguments: " ++ show fvars
                      else return ()
                      case M.lookup cn fs of
                        Just t -> throwError $ 
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
              tvars = t ^..typeArgs.traverse._1
              bt = bind tvars $ TFunc targs Nothing (TApp (s2n tn) 
                  (fmap (\t -> TVar t pos) tvars) pos) pos
           in BoundType bt
           
inferTypeKind :: (Has EnvEff sig m) => Scope -> Type -> m Kind
inferTypeKind scope a@TApp{..} = do
  ak <- inferTypeKind scope $ TVar _tappName _tloc
  case ak of
    KStar{} -> throwError $ "expected a func kind, but got " ++ show ak
    KFunc{..} -> if L.length _tappArgs /= L.length _kfuncArgs
      then throwError $ "kind arguments mismatch: " ++ show _tappArgs ++ " vs " ++ show _kfuncArgs
      else do
        mapM (\(a, b) -> do
          t <- inferTypeKind scope a
          checkTypeKind t
          checkTypeKind b
          if aeq t b then return ()
          else throwError $ "kind mismatch: " ++ show t ++ " vs " ++ show b)
          [(a, b) | a <- _tappArgs | b <- _kfuncArgs]
        checkTypeKind _kfuncResult
        return _kfuncResult
inferTypeKind scope a@TAnn{..} = do
  k <- inferTypeKind scope _tannType
  checkTypeKind k
  if aeq k _tannKind then return k
  else throwError $ "kind mismatch: " ++ show k ++ " vs " ++ show _tannKind
inferTypeKind scope b@BoundType{..} = 
  let (bvs, t) = unsafeUnbind $ _boundType
      newScope = L.foldl' (
        \s e ->
          M.insert (name2String e) (KStar $ _tloc t) s) (scope^.typeKinds) bvs
   in inferTypeKind scope{_typeKinds=newScope} t
inferTypeKind scope v@TVar{..} = do
  kinds <- _types <$> get @Env
  case M.lookup (name2String _tvar) (scope^.typeKinds) of
    Just k -> return k
    Nothing -> case M.lookup (name2String _tvar) kinds of
      Just k -> return k
      Nothing -> throwError $ "cannot find type: " ++ show v
inferTypeKind scope f@TFunc{..} = do
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
    KStar{} -> return ()
    _ -> throwError $ "expected a star kind, but got " ++ show k

initEffTypeDef :: (Has EnvEff sig m) => Module -> m () 
initEffTypeDef m = do
  env <- get @Env
  ekinds <- eff env
  put $ set effs ekinds env
  where edefs = universeOn (topStmts.traverse._EDef) m

        eff env = foldM insertEffKind (env ^. effs) edefs
        insertEffKind es e =
           let en = e ^. effectName
             in case M.lookup en es of
                 Just oe -> throwError $
                    "redefine an effect: " ++ en  ++ " vs " ++ show oe
                 Nothing -> return $ M.insert en (effKind e) es 
        effKind e = 
          let loc = _effectLoc e
              args = e ^. effectArgs
              star = KStar loc
              estar = EKStar loc
            in if args == [] then estar
                else EKFunc (fmap (\(_, kk) -> case kk of
                                     Nothing -> star
                                     Just kkk -> kkk) args) estar loc

inferEffKind :: (Has EnvEff sig m) => Scope -> EffectType -> m EffKind
inferEffKind scope a@EffApp{..} = do 
  ak <- inferEffKind scope $ EffVar _effAppName _effLoc
  case ak of
    EKFunc{..} -> if L.length _effAppArgs /= L.length _ekfuncArgs
      then throwError $ "eff kind arguments mismatch: " ++ show _effAppArgs ++ " vs " ++ show _ekfuncArgs
      else do
        mapM (\(a, b) -> do
          e <- inferTypeKind scope a
          checkTypeKind e
          checkTypeKind b
          if aeq e b then return ()
          else throwError $ "eff kind mismatch: " ++ show e ++ " vs " ++ show b)
          [(a, b) | a <- _effAppArgs | b <- _ekfuncArgs]
        checkEffKind _ekfuncResult
        return _ekfuncResult
    _ -> throwError $ "expected a func eff kind, but got " ++ show ak
inferEffKind scope a@EffAnn{..} = do
  k <- inferEffKind scope _effAnnType
  checkEffKind k
  if aeq k _effAnnKind then return k
  else throwError $ "eff kind mismatch: " ++ show k ++ " vs " ++ show _effAnnKind
inferEffKind scope b@BoundEffType{..} = 
  let (bvs, t) = unsafeUnbind $ _boundEffType
      newScope = L.foldl' (
        \s e ->
          M.insert (name2String e) (EKStar $ _effLoc t) s) (scope^.effKinds) bvs
   in inferEffKind scope{_effKinds=newScope} t
inferEffKind scope v@EffVar{..} = do
  kinds <- _effs <$> get @Env
  case M.lookup (name2String _effVarName) (scope^.effKinds) of
    Just k -> return k
    Nothing -> case M.lookup (name2String _effVarName) kinds of
      Just k -> return k
      Nothing -> throwError $ "cannot find type: " ++ show v
inferEffKind scope l@EffList{..} = do
  ls <- mapM (inferEffKind scope) _effList
  mapM_ checkEffKind ls
  return $ EKList ls _effLoc
inferEffKind scope EffTotal{..} = return $ EKStar _effLoc

checkEffKind :: (Has EnvEff sig m) => EffKind -> m ()
checkEffKind k = do
  case k of
    EKStar{} -> return ()
    EKList{..} -> mapM_ checkEffKind _ekList 
    _ -> throwError $ "expected a star eff kind, but got " ++ show k

initEffIntfDef :: (Has EnvEff sig m) => Module -> m ()
initEffIntfDef m = do
  env <- get @Env
  eintfs <- effIntfTypes env
  put $ set effIntfs eintfs env
  where edefs = universeOn (topStmts.traverse._EDef) m
        effIntfTypes env = 
          let globalTypes = (fmap (\n -> s2n n) $ M.keys (env ^.types))
           in foldM (insertEffIntfType globalTypes) (env ^. effIntfs) edefs
        insertEffIntfType globalTypes intfs e = 
           let is = e ^. effectIntfs
               en = e ^. effectName
               f = \is i -> do
                 let intfn = i ^. intfName
                     iargs = i ^. intfArgs
                     iresult = i ^. intfResultType
                     pos = i ^.intfLoc
                     bvars = (i ^. intfBoundVars)
                     targs = (e ^.. effectArgs.traverse._1) ++ globalTypes
                     b = bind (targs++bvars) $ iresult : iargs
                     fvars = (b ^..fv):: [TVar]
                  in do
                      if fvars /= [] then throwError $ 
                        "eff interfaces's type variables should " ++ 
                        "only exists in eff type arguments: " ++ show fvars
                      else return ()
                      case M.lookup intfn is of
                        Just t -> throwError $ 
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
              tvars = e ^..effectArgs.traverse._1
           in BoundType $ bind tvars $ BoundType $ 
                 bind bvars $ TFunc iargs Nothing iresult pos

magicVarName :: Int -> TVar
magicVarName i = s2n $ "__" ++ show i

initFuncDef :: (Has EnvEff sig m) => Module -> m ()
initFuncDef m = do
  env <- get @Env
  fs <- funcTypes env
  put $ set funcs fs env
  where fdefs = universeOn (topStmts.traverse._FDef) m
        funcTypes env = 
          foldM (\fs f ->
            let pos = f ^. funcLoc
                fn = f ^. funcName
                bvars = fmap (\t -> (name2String t, KStar pos)) $ f ^.funcBoundVars
                scope = Scope (M.fromList bvars) M.empty M.empty
             in do argTypes <- (mapM (\(_, a) -> 
                                  case a of
                                    Just t -> do
                                      inferTypeKind scope t
                                      return t
                                    Nothing -> do
                                      v <- fresh
                                      return $ TVar (magicVarName v) pos)
                                (f ^.funcArgs))
                   effType <- (case (f ^.funcEffectType) of
                                Just t -> do
                                  inferEffKind scope t
                                  return t
                                Nothing -> return $ EffTotal pos)
                   resultType <- (case (f ^.funcResultType) of
                                   Just t -> do
                                     inferTypeKind scope t
                                     return t
                                   Nothing -> do
                                     v <- fresh
                                     return $ TVar (magicVarName v) pos)
                   let ft = BoundType $ bind (f ^.funcBoundVars) $
                             TFunc argTypes (Just effType) resultType pos
                    in do inferTypeKind scope ft
                          return $ M.insert fn ft fs)
            (env ^.funcs) fdefs

--inferExprType :: (Has EffEnv sig m) => Expr -> m Type
--inferExprType f = return 

infer :: Module -> Either String (Env, (Int, Module))
infer m = run . runError . (runState initialEnv) . runFresh 0 $ do
           initTypeDef m
           initEffTypeDef m
           initTypeConDef m
           initEffIntfDef m
           initFuncDef m
           return m
