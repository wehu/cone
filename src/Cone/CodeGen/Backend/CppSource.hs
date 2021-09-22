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

  namePath proxy n = pretty n

  typeN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == (take prefixLen n') then (drop (prefixLen + 1) n') else n'
        ns = splitOn "/" n
        ps = init ns
        tn = "Cone__" ++ last ns
     in pretty $ join $ intersperse "::" $ ps ++ [tn]

  funcN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == (take prefixLen n') then (drop (prefixLen + 1) n') else n'
        ns = splitOn "/" n
        ps = init ns
        fn = "cone__" ++ last ns
     in pretty $ join $ intersperse "::" $ ps ++ [fn]

  genImport proxy ImportStmt {..} =
    return $
      ( "#include \"" <> namePath proxy _importPath <> ".h\""
      )
        <+> line

  genTypeDef proxy TypeDef {..} = do
    cons <- mapM (genTypeCon proxy _typeName) _typeCons
    return $ vsep cons

  genTypeCon proxy ptn TypeCon {..} = do
    prefix <- getEnv currentModuleName
    let fn = funcN proxy prefix _typeConName
     in return $ ctrFunc fn
    where
      ctrFunc fn =
        "m.def(\"" <> fn <> "\", &" <> fn <> ");"

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
         [ "#include \"pybind11/pybind11.h\""
         , "#include \"pybind11/functional.h\""
         , "#include \"" <> pretty _moduleName <> ".h\""]
          ++ imps
          ++ ["namespace cone{", sep $ map (\n -> "namespace" <+> pretty n <+> lbrace) modulePs]
          ++ ["namespace py = pybind11;"
             ,"PYBIND11_MODULE(" <> pretty (last modulePs) <> "_c, m) {"
             ,"m.doc() = \""<> pretty _moduleName <>"\";"]
          ++ [pre]
          ++ tops
          ++ [pos]
          ++ ["}"]
         ++ ["}", sep $ map (\_ -> rbrace) modulePs]
