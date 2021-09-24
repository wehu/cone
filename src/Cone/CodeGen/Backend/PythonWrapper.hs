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

module Cone.CodeGen.Backend.PythonWrapper where

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

data PythonWrapper a = PythonWrapper

instance Backend PythonWrapper where
  namePath proxy n = pretty $ join $ intersperse "." $ splitOn "/" n

  typeN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == (take prefixLen n') then (drop (prefixLen + 1) n') else n'
        ns = splitOn "/" n
        ps = init ns
        tn = "Cone__" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [tn]

  funcN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == (take prefixLen n') then (drop (prefixLen + 1) n') else n'
        ns = splitOn "/" n
        ps = init ns
        fn = "cone__" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [fn]

  genImport proxy ImportStmt {..} =
    return $
      ( -- case _importAlias of
        --  Just a -> "import" <+> namePath proxy _importPath <+> "as" <+> pretty a
        --  Nothing ->
        "import" <+> namePath proxy _importPath
      )
        <+> line

  genTypeDef proxy TypeDef {..} = do
    cons <- mapM (genTypeCon proxy _typeName) _typeCons
    return $
      vsep $ {-["class" <+> typeN proxy _typeName <> ":"
             ,indent 4 "pass" <+> line
             ] ++-}
        cons

  genTypeCon proxy ptn TypeCon {..} = do
    prefix <- getEnv currentModuleName
    let tn = typeN proxy prefix _typeConName
        fn = funcN proxy prefix _typeConName
     in return $
          vsep
            [ tn <> "=" <> "____T." <> tn,
              --ctrFunc fn,
              ctrFuncWrapper fn <+> line
            ]
    where
      genArgs init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "t" ++ show (length s)]) init _typeConArgs
      --ctrFunc fn = fn <> "=" <> "____C." <> fn
      ctrFuncWrapper fn = fn <> "=" <> "____C." <> fn <> "_w"

  genEffectDef proxy e = return emptyDoc

  genFuncDef proxy FuncDef {..} = do
    prefix <- getEnv currentModuleName
    let fn = funcN proxy prefix _funcName
    return $ vsep [--fn <> "=" <> "____C." <> fn
                  fn <> "=" <> "____C." <> fn <> "_w"]

  genExpr _ _ = return emptyDoc
 
  genPatternMatch _ _ = return emptyDoc

  genPrologue _ = return emptyDoc

  genEpilogue proxy = do
    prefix <- getEnv currentModuleName
    return $
      vsep
        [ "if __name__ == \"__main__\":",
          indent 4 $ funcN proxy prefix "main()" <+> line
        ]

  genModule proxy Module {..} = do
    setEnv _moduleName currentModuleName
    pre <- genPrologue proxy
    imps <- mapM (genImport proxy) _imports
    tops <- mapM (genTopStmt proxy) _topStmts
    pos <- genEpilogue proxy
    return $
      vsep $
        -- [ "module" <+> namePath proxy _moduleName <+> line]
        [ "import" <+> namePath proxy _moduleName <> "____c as ____C",
          "import" <+> namePath proxy _moduleName <> "____t as ____T"
        ]
          ++ imps
          ++ [pre]
          ++ tops
          ++ [pos]

