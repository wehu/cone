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

module Cone.CodeGen.Backend.PythonType where

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

data PythonType a = PythonType

instance Backend PythonType where

  namePath proxy n = pretty $ join $ intersperse "." $ splitOn "/" n

  typeN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == take prefixLen n' then drop (prefixLen + 1) n' else n'
        ns = splitOn "/" n
        ps = init ns
        tn = "Cone__" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [tn]

  funcN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == take prefixLen n' then drop (prefixLen + 1) n' else n'
        ns = splitOn "/" n
        ps = init ns
        fn = "cone__" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [fn]

  genImport proxy ImportStmt {..} =
    return $ "import" <+> namePath proxy _importPath <> "____t" <+> line

  genTypeDef proxy TypeDef {..} = do
    cons <- mapM (genTypeCon proxy _typeName) _typeCons
    return $ vsep cons

  genTypeCon proxy ptn TypeCon {..} = do
    prefix <- getEnv currentModuleName
    let tn = typeN proxy prefix _typeConName
        fn = funcN proxy prefix _typeConName
     in return $
          vsep
            [ "class" <+> tn {- <> parens (typeN proxy ptn) -} <> ":",
              indent 4 constructor,
              indent 4 hash,
              indent 4 $ eq tn]
    where
      constructor =
        vsep
          [ "def" <+> "__init__" <> genArgs ["self", "____k", "____state", "____effs"] <> colon,
            indent 4 $ vsep genFields
          ]
      hash =
        vsep
          [ "def __hash__(self):",
            indent 4 $ "return hash(" <> fields <> ")"
          ]
      eq tn =
        vsep
          [ "def __eq__(self, other):",
            indent 4 $ "return" <+> "isinstance(other, " <> tn <> ") and" <+> cmpFields
          ]
      fields = encloseSep lparen rparen comma $ ["self.f" <> pretty i | i <- [0 .. length (_typeConArgs) - 1]]
      cmpFields = encloseSep lparen rparen " and " $ "True" : ["self.f" <> pretty i <+> "==" <+> "other.f" <> pretty i | i <- [0 .. length (_typeConArgs) - 1]]
      genArgs init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "t" ++ show (length s)]) init _typeConArgs
      genFields =
        if null _typeConArgs
          then ["pass"]
          else
            foldl'
              ( \s e ->
                  let i = length s
                      f = "self.f" ++ show i
                      a = "t" ++ show (i + 4)
                   in s ++ [pretty f <+> "=" <+> pretty a]
              )
              []
              _typeConArgs

  genEffectDef _ _ = return emptyDoc

  genFuncDef _ _ = return emptyDoc

  genExpr _ _ = return emptyDoc

  genPatternMatch _ _ = return emptyDoc

  genPrologue _ = return emptyDoc

  genEpilogue _ = return emptyDoc

  genModule proxy Module {..} = do
    setEnv _moduleName currentModuleName
    pre <- genPrologue proxy
    imps <- mapM (genImport proxy) _imports
    tops <- mapM (genTopStmt proxy) _topStmts
    pos <- genEpilogue proxy
    return $
      vsep $
          imps
          ++ [pre]
          ++ tops
          ++ [pos]
