{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

type Eff s e = State s -- :+: Error e

data Env = Env{_types:: M.Map String Kind,
               _funcs:: M.Map String Type,
               _effs :: M.Map String EffectType}
            deriving (Show)

makeLenses ''Env

initialEnv = Env{_types=M.empty, _funcs=M.empty, _effs=M.empty}

type EnvEff = Eff Env String

inferTypeDef :: (Has EnvEff sig m) => Module -> m Module
inferTypeDef m = do
  env::Env <- get
  put $ set types (ts env) env
  return m
  where tdefs = universeOn (topStmts.traverse._TDef) m
        ts env = L.foldl' insertType (env ^. types) tdefs
        insertType ts (BoundTypeDef (B _ t)) = M.insert (t ^. typeName) (k t) ts 
        insertType ts _ = ts
        k t = 
           let loc = _typeLoc t
               args = t ^. typeArgs
               star = KStar loc
            in if args == [] then star
                else KFunc (fmap (\(_, kk) -> case kk of
                                     Nothing -> star
                                     Just kkk -> kkk) args) star loc 

infer :: Module -> Either String (Env, Module)
infer m = run . runError . runState initialEnv $ 
           inferTypeDef $ bindTVars m
