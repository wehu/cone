{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Cone.CodeGen.Backend.CppSource where

import Cone.CodeGen.Backend
import Cone.Parser.AST
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Effect.Sum
import Control.Lens
import Control.Monad
import Data.List
import Data.List.Split
import Data.Maybe
import Data.Proxy
import Debug.Trace
import Prettyprinter
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)

data CppSource a = CppSource

instance Backend CppSource where

  namePath _ _ = emptyDoc

  typeN _ _ _ = emptyDoc

  funcN _ _ _ = emptyDoc

  genImport _ _ = return emptyDoc

  genTypeDef _ _ = return emptyDoc

  genTypeCon _ _ _ = return emptyDoc

  genEffectDef _ _ = return emptyDoc

  genFuncDef _ _ = return emptyDoc

  genExpr _ _ = return emptyDoc

  genPatternMatch _ _ = return emptyDoc
 
  genPrologue _ = return emptyDoc

  genEpilogue _ = return emptyDoc

  genModule proxy Module{..} = do
    let modulePs = splitOn "/" _moduleName
    setEnv _moduleName currentModuleName
    pre <- genPrologue proxy
    imps <- mapM (genImport proxy) _imports
    tops <- mapM (genTopStmt proxy) _topStmts
    pos <- genEpilogue proxy
    return $
      vsep $
        [ sep $ map (\n -> "namespace" <+> pretty n <+> lbrace) modulePs] ++
        [ "#include \"pybind11/pybind11.h\""
        ]
          ++ imps
          ++ [pre]
          ++ tops
          ++ [pos]
          ++ [sep $ map (\_ -> rbrace) modulePs]
