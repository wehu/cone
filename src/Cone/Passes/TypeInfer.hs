{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

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

data Env = Env{_types:: M.Map String Kind,
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
  tconTypes <- tcons env
  put $ set funcs tconTypes env
  where tdefs = universeOn (topStmts.traverse._TDef) m

        ts env = foldM insertTypeKind (env ^. types) tdefs
        insertTypeKind ts t =
           let tn = t ^. typeName
             in if M.member tn ts 
                 then throwError $ "redefine a type: " ++ tn
                 else return $ M.insert tn (typeKind t) ts 
        typeKind t = 
          let loc = _typeLoc t
              args = t ^. typeArgs
              star = KStar loc
            in if args == [] then star
                else KFunc (fmap (\(_, kk) -> case kk of
                                     Nothing -> star
                                     Just kkk -> kkk) args) star loc
        
        tcons env = foldM insertTconType (env ^. funcs) tdefs
        insertTconType fs t = 
           let cons = t ^. typeCons
               f = \fs c -> do
                 let cn = c ^. typeConName
                     cargs = c ^. typeConArgs
                     targs = t ^.. typeArgs.traverse._1
                     b = bind targs cargs
                     fvars = (b ^..fv):: [TVar]
                  in do
                      if fvars /= [] then throwError $ 
                        "type constructor's type variables should " ++ 
                        "only exists in type arguments: " ++ show fvars
                      else return ()
                      if M.member cn fs
                      then throwError $ "type construct has conflict name: " ++ cn
                      else return $ M.insert cn (tconType c t) fs
            in foldM f fs cons
        tconType c t = 
          let targs = c ^. typeConArgs
              tn = t ^. typeName
              pos = c ^. typeConLoc
              tvars = t ^..typeArgs.traverse._1
              bt = bind tvars $ TFunc targs Nothing (TApp (s2n tn) targs pos) pos
            in BoundType bt

inferEffTypeDef :: (Has EnvEff sig m) => Module -> m Module
inferEffTypeDef = return

infer :: Module -> Either String (Env, Module)
infer m = run . runError . runState initialEnv $ do
           initTypeDef m
           return m
