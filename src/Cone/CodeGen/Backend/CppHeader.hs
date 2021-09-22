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

module Cone.CodeGen.Backend.CppHeader where

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

data CppHeader a = CppHeader

pythonTypeNamePath n = 
  let ns = splitOn "/" n
   in "py::module_::import(\"" <> (pretty $ join $ intersperse "." $ init ns) <>
       "____t\").attr(\"" <> pretty ("Cone__" ++ last ns) <> "\")"

instance Backend CppHeader where

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
    let tn = typeN proxy prefix _typeConName
        fn = funcN proxy prefix _typeConName
     in return $ ctrFunc fn tn
    where
      genArgs init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "const object &t" ++ show (length s)]) init _typeConArgs
      genArgs' init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "t" ++ show (length s)]) init _typeConArgs
      ctrFunc fn tn =
        "inline py::object" <+> fn <> 
            genArgs ["const cont &____k", "states ____state", "effects ____effs"] <+>
            braces
            (vsep ["py::object cntr = " <> pythonTypeNamePath _typeConName <> semi
                  ,"return" <+> ("____k" <> parens ("cntr" <> genArgs' ["____k", "____state", "____effs"])) <> semi])

  genEffectDef _ _ = return emptyDoc

  genFuncDef proxy FuncDef {..} = do
    prefix <- getEnv currentModuleName
    body <- case _funcExpr of
      Just e -> do
        es <- genExpr proxy e
        return $ "return" <+> parens (es <> parens "____k, py::list(py::dict()), ____effs") <> semi
      Nothing -> return $ "throw \"" <> pretty _funcName <> " is not implemented\";"
    return $
      vsep
        [ "object" <+> funcN proxy prefix _funcName <> genArgs' ["const cont &____k", "states ____state", "effects ____effs"] prefix <> 
          braces body,
          "object" <+> funcN proxy prefix _funcName <> "_w" <> genArgs' [] prefix <>
          braces ("return" <+> funcN proxy prefix _funcName <> genArgs ["____identity_k", "py::list(py::dict())", "py::list()"] prefix <> semi)
        ]
    where
      genArgs init prefix = encloseSep lparen rparen comma $ init ++ (map (funcN proxy prefix) $ _funcArgs ^.. traverse . _1)
      genArgs' init prefix = encloseSep lparen rparen comma $ init ++ (map (\a -> "const object &" <+> funcN proxy prefix a) $ _funcArgs ^.. traverse . _1)

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
        ["#pragma once"
         ,"#include <iostream>"
         ,"#include \"pybind11/pybind11.h\""
         ,"#include \"pybind11/functional.h\""
         ,"#include \"cone/builtins.h\""]
          ++ imps
          ++ ["namespace py = pybind11;"
             ,"namespace cone{"
             ,sep $ map (\n -> "namespace" <+> pretty n <+> lbrace) modulePs]
          ++ [pre]
          ++ tops
          ++ [pos]
          ++ ["}",sep $ map (\_ -> rbrace) modulePs]