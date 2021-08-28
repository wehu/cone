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
import Unbound.Generics.LocallyNameless.Bind
import Cone.Passes.BindTypeVars
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

inferTypeDef :: (Has EnvEff sig m) => Module -> m Module
inferTypeDef m = do
  env <- get @Env
  newTypes <- ts env
  put $ set types newTypes env
  newTcons <- tcons env
  put $ set funcs newTcons env
  return m
  where tdefs = universeOn (topStmts.traverse._TDef) m

        ts env = foldM insertType (env ^. types) tdefs
        insertType ts (BoundTypeDef (B _ t)) =
           let tn = t ^. typeName
             in if M.member tn ts 
                 then throwError $ "redefine a type: " ++ tn
                 else return $ M.insert tn (k t) ts 
        insertType ts _ = return ts
        k t = 
          let loc = _typeLoc t
              args = t ^. typeArgs
              star = KStar loc
            in if args == [] then star
                else KFunc (fmap (\(_, kk) -> case kk of
                                     Nothing -> star
                                     Just kkk -> kkk) args) star loc
        
        tcons env = foldM insertTcon (env ^. funcs) tdefs
        insertTcon fs (BoundTypeDef (B _ t)) = 
           let cons = t ^. typeCons
               f = \fs c -> do
                 let cn = c ^. typeConName
                  in if M.member cn fs
                      then throwError $ "type construct has conflict name: " ++ cn
                      else return $ M.insert cn (getTconType c t) fs
            in foldM f fs cons
        insertTcon fs _ = return fs
        getTconType c t = 
          let targs = c ^. typeConArgs
              tn = t ^. typeName
              pos = c ^. typeConLoc
           in TFunc targs Nothing (TApp (s2n tn) targs pos) pos

infer :: Module -> Either String (Env, Module)
infer m = run . runError . runState initialEnv $ 
           inferTypeDef $ bindTVars m
