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
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe
import Control.Effect.State
import Control.Effect.Error
import Control.Effect.Sum
import Control.Carrier.State.Strict
import Control.Carrier.Error.Either
import qualified Data.Map as M
import qualified Data.List as L
import Control.Monad

type Eff s e = State s :+: Error e

type TypeKinds = M.Map String Kind

data Env = Env{_types:: TypeKinds,
               _funcs:: M.Map String Type,
               _effs :: M.Map String EffectType}
            deriving (Show)

makeLenses ''Env

initialEnv = Env{_types=M.empty, _funcs=M.empty, _effs=M.empty}

type EnvEff = Eff Env String

initTypeDef :: (Has EnvEff sig m) => Module -> m ()
initTypeDef m = do
  env <- get @Env
  tkinds <- ts env
  put $ set types tkinds env
  env <- get @Env
  tconTypes <- tcons env
  put $ set funcs tconTypes env
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
        
        tcons env = 
          let globalTypes = (fmap (\n -> s2n n) $ M.keys (env ^.types))
           in foldM (insertTconType globalTypes) (env ^. funcs) tdefs
        insertTconType globalTypes fs t = 
           let cons = t ^. typeCons
               f = \fs c -> do
                 env <- get @Env
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
                             inferTypeKind M.empty bt
                             return $ M.insert cn bt fs
            in foldM f fs cons
        tconType c t = 
          let targs = c ^. typeConArgs
              tn = t ^. typeName
              pos = c ^. typeConLoc
              tvars = t ^..typeArgs.traverse._1
              bt = bind tvars $ TFunc targs Nothing (TApp (s2n tn) targs pos) pos
           in BoundType bt
           
inferTypeKind :: (Has EnvEff sig m) => TypeKinds -> Type -> m Kind
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
          M.insert (name2String e) (KStar $ _tloc t) s) scope bvs
   in inferTypeKind newScope t
inferTypeKind scope v@TVar{..} = do
  kinds <- _types <$> get @Env
  case M.lookup (name2String _tvar) scope of
    Just k -> return k
    Nothing -> case M.lookup (name2String _tvar) kinds of
      Just k -> return k
      Nothing -> throwError $ "cannot find type: " ++ show v
inferTypeKind scope f@TFunc{..} = do
  mapM (inferTypeKind scope) _tfuncArgs
  inferTypeKind scope _tfuncResult
  return $ KStar _tloc
inferTypeKind _ t = return $ KStar $ _tloc t

checkTypeKind :: (Has EnvEff sig m) => Kind -> m ()
checkTypeKind k = do
  case k of
    KStar{} -> return ()
    _ -> throwError $ "expected a star kind, but got " ++ show k

inferEffTypeDef :: (Has EnvEff sig m) => Module -> m Module
inferEffTypeDef = return

infer :: Module -> Either String (Env, Module)
infer m = run . runError . runState initialEnv $ do
           initTypeDef m
           return m
