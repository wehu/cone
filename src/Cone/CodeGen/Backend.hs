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

  typeName' :: t Target -> String -> Doc a
  typeName' proxy n = pretty $ "T" ++ n

  funcName' :: t Target -> String -> Doc a
  funcName' proxy n = pretty $ "f" ++ n

  genImport :: t Target -> ImportStmt -> Doc a
  genImport proxy ImportStmt{..} =
    "import" <+> namePath proxy _importPath <+> 
     (case _importAlias of; Just a -> "as" <+> pretty a; _ -> emptyDoc) <+> line

  genTypeDef :: t Target -> TypeDef -> Doc a
  genTypeDef proxy TypeDef{..} = 
    vsep $ ["class" <+> typeName' proxy _typeName <> ":"
           ,indent 4 "pass" <+> line
           ] ++ (fmap (genTypeCon proxy _typeName) _typeCons)

  genTypeCon :: t Target -> String -> TypeCon -> Doc a
  genTypeCon proxy ptn TypeCon{..} =
    let tn = typeName' proxy _typeConName 
        fn = funcName' proxy _typeConName
     in vsep ["class" <+> tn <> parens (typeName' proxy ptn) <> ":"
          ,indent 4 constructor
          ,conf fn tn <+> line]
    where constructor =
            vsep ["def" <+> "initialize" <> genArgs <> ":"
                 ,indent 4 $ vsep genFields]
          conf fn tn = vsep ["def" <+> fn <> genArgs <> ":"
                       ,indent 4 ("return" <+> tn <> genArgs)]
          genArgs = encloseSep lparen rparen comma $ foldl' (\s e -> s++[pretty $ "t" ++ show (length s)]) ["self"] _typeConArgs
          genFields =
            if _typeConArgs == []
            then ["pass"]
            else foldl' (\s e -> 
                  let i = show $ length s
                      f = "self.f" ++ i
                      a = "t" ++ i
                   in s++[pretty f <+> "=" <+> pretty a]) [] _typeConArgs
  
  genEffectDef :: t Target -> EffectDef -> Doc a
  genEffectDef proxy e = pretty e
  
  genFuncDef :: t Target -> FuncDef -> Doc a
  genFuncDef proxy f = pretty f
  
  genImplFuncDef :: t Target -> ImplFuncDef -> Doc a
  genImplFuncDef proxy f = pretty f

genModule :: Backend t => t Target -> Module -> Doc a
genModule proxy Module{..} =
  vsep $
      ["module" <+> namePath proxy _moduleName <+> line]
        ++ (map (genImport proxy) _imports)
        ++ (map (genTopStmt proxy) _topStmts)

genTopStmt :: Backend t => t Target -> TopStmt -> Doc a
genTopStmt proxy TDef{..} = genTypeDef proxy _tdef
genTopStmt proxy EDef{..} = genEffectDef proxy _edef
genTopStmt proxy FDef{..} = genFuncDef proxy _fdef
genTopStmt proxy ImplFDef{..} = genImplFuncDef proxy _implFdef
