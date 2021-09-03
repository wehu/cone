{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Cone.CodeGen.Backend where

import Cone.Parser.AST
import Data.Proxy
import Data.List
import Control.Lens
import Control.Monad
import Prettyprinter
import Data.List.Split

data Target

class Backend t where
  gen :: t Target -> Module -> Doc a
  gen proxy m = genModule proxy m
  
  namePath :: t Target -> String -> Doc a
  namePath proxy n = pretty $ join $ intersperse "." $ splitOn "/" n

  genImport :: t Target -> ImportStmt -> Doc a
  genImport proxy ImportStmt{..} =
    "import" <+> namePath proxy _importPath <+> (case _importAlias of; Just a -> "as" <+> pretty a; _ -> emptyDoc)

  genTypeDef :: t Target -> TypeDef -> Doc a
  genTypeDef proxy TypeDef{..} = 
    "type" <+> pretty _typeName
  
  genEffectDef :: t Target -> EffectDef -> Doc a
  genEffectDef proxy e = pretty e
  
  genFuncDef :: t Target -> FuncDef -> Doc a
  genFuncDef proxy f = pretty f
  
  genImplFuncDef :: t Target -> ImplFuncDef -> Doc a
  genImplFuncDef proxy f = pretty f

genModule :: Backend t => t Target -> Module -> Doc a
genModule proxy Module{..} =
  vsep $
      ["module" <+> namePath proxy _moduleName]
        ++ (map (genImport proxy) _imports)
        ++ (map (genTopStmt proxy) _topStmts)

genTopStmt :: Backend t => t Target -> TopStmt -> Doc a
genTopStmt proxy TDef{..} = genTypeDef proxy _tdef
genTopStmt proxy EDef{..} = genEffectDef proxy _edef
genTopStmt proxy FDef{..} = genFuncDef proxy _fdef
genTopStmt proxy ImplFDef{..} = genImplFuncDef proxy _implFdef
