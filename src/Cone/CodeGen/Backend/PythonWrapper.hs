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
import Unbound.Generics.LocallyNameless.Unsafe

data PythonWrapper a = PythonWrapper

instance Backend PythonWrapper where
  namePath proxy n = pretty $ join $ intersperse "." $ splitOn "/" n

  typeN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == take prefixLen n' then drop (prefixLen + 1) n' else n'
        ns = splitOn "/" $ replaceSpecialChars n
        ps = init ns
        tn = "Cone__" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [tn]

  funcN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == take prefixLen n' then drop (prefixLen + 1) n' else n'
        ns = splitOn "/" $ replaceSpecialChars n
        ps = init ns
        fn = "cone__" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [fn]

  genImport proxy ImportStmt {..} =
    return $ "import" <+> namePath proxy _importPath <+> line

  genTypeDef proxy TypeDef {..} = do
    cons <- mapM (genTypeCon proxy _typeName) _typeCons
    return $ vsep cons
  genTypeDef proxy (BoundTypeDef b _) = do
    let (_, t) = unsafeUnbind b
    genTypeDef proxy t

  genTypeCon proxy ptn TypeCon {..} = do
    prefix <- getEnv currentModuleName
    let tn = typeN proxy prefix _typeConName
        fn = funcN proxy prefix _typeConName
     in return $
          vsep
            [ tn <> "=" <> "____T." <> tn,
              ctrFuncWrapper fn <+> line
            ]
    where
      genArgs init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "t" ++ show (length s)]) init _typeConArgs
      ctrFuncWrapper fn = fn <> "=" <> "____C." <> fn

  genEffectDef proxy e = return emptyDoc

  genFuncDef proxy FuncDef {..} = do
    prefix <- getEnv currentModuleName
    let fn = funcN proxy prefix _funcName
    return $ fn <> "=" <> "____C." <> fn
  genFuncDef proxy (BoundFuncDef b _) = do
    let (_, f) = unsafeUnbind b
    genFuncDef proxy f
  genFuncDef proxy (BoundEffFuncDef b _) = do
    let (_, f) = unsafeUnbind b
    genFuncDef proxy f

  genImplFuncDef _ _ = return emptyDoc

  genExpr _ _ = return emptyDoc

  genPatternMatch _ _ _ = return emptyDoc

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
        [ "import" <+> namePath proxy _moduleName <> "____c as ____C",
          "import" <+> namePath proxy _moduleName <> "____t as ____T"
        ]
          ++ imps
          ++ [pre]
          ++ tops
          ++ [pos]
