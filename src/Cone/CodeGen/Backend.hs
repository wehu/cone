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
          ,ctrFunc fn tn <+> line]
    where constructor =
            vsep ["def" <+> "__init__" <> genArgs ["self"] <> colon
                 ,indent 4 $ vsep genFields]
          genArgs init = encloseSep lparen rparen comma $ 
                 foldl' (\s e -> s ++ [pretty $ "t" ++ show (length s)]) init _typeConArgs
          genFields =
            if _typeConArgs == []
            then ["pass"]
            else foldl' (\s e -> 
                  let i = length s
                      f = "self.f" ++ show i
                      a = "t" ++ show (i + 1)
                   in s++[pretty f <+> "=" <+> pretty a]) [] _typeConArgs
          ctrFunc fn tn = vsep ["def" <+> fn <> genArgs [] <> ":"
                       ,indent 4 ("return" <+> tn <> genArgs [])]
  
  genEffectDef :: t Target -> EffectDef -> Doc a
  genEffectDef proxy e = emptyDoc
  
  genFuncDef :: t Target -> FuncDef -> Doc a
  genFuncDef proxy FuncDef{..} = 
    vsep ["def" <+> funcName' proxy _funcName <> genArgs <> colon
         ,indent 4 $ case _funcExpr of
                       Just e -> vsep ["____state = {}", "return" <+> genExpr proxy e <> brackets "-1"]
                       Nothing -> "pass"]
    where genArgs = encloseSep lparen rparen comma $ map pretty $ _funcArgs ^..traverse._1
  
  genExpr :: t Target -> Expr -> Doc a
  genExpr proxy EVar{..} = parens $ "____state[" <> fns <> "] if" <+> fns <+> "in ____state" <+>  "else" <+> fn
    where fn = funcName' proxy _evarName
          fns = "\"" <> fn <> "\""
  genExpr proxy ESeq{..} = encloseSep lbracket rbracket comma $ fmap (genExpr proxy) _eseq
  genExpr proxy ELit{..} = pretty _lit
  genExpr proxy ELam{..} = parens $ "lambda" <+> genArgs <> colon <+> genBody _elamExpr
    where genArgs = sep $ map pretty $ _elamArgs ^..traverse._1
          genBody e = case e of
                       Just e -> genExpr proxy e
                       Nothing -> "pass" 
  genExpr proxy EWhile{..} = "while" <+> genExpr proxy _ewhileCond <> colon <+> genExpr proxy _ewhileBody
  genExpr proxy ELet{..} = parens $ "f____assign" <> 
        parens ("____state" <> comma <+> genPattern proxy _eletPattern <> comma <+> genExpr proxy _eletExpr)
  genExpr proxy EAnn{..} = genExpr proxy _eannExpr
  genExpr proxy EApp{..} = 
    let fn = _eappFunc ^.evarName
     in case fn of
         "____add" -> binary "+"
         "____sub" -> binary "-"
         "____mul" -> binary "*"
         "____div" -> binary "/"
         "____mod" -> binary "%"
         _ -> genExpr proxy _eappFunc <> genArgs
    where genArgs = encloseSep lparen rparen comma
            (if _eappFunc ^.evarName == "____assign" then  
              "____state":("\"" <> (funcName' proxy $ _eappArgs !! 0 ^.evarName) <> "\""):(tail $ map (genExpr proxy) _eappArgs)
            else (map (genExpr proxy) _eappArgs))
          binary :: String -> Doc a
          binary op = parens $ genExpr proxy (_eappArgs !! 0) <+> pretty op <+> genExpr proxy (_eappArgs !! 1)
          
  genPattern :: t Target -> Pattern -> Doc a
  genPattern proxy PVar{..} = pretty '"' <> funcName' proxy _pvar <> pretty '"'
  genPattern proxy PExpr{..} = genExpr proxy _pExpr

  genPrologue :: t Target -> Doc a
  genPrologue proxy = 
    vsep ["def f____assign(state, k, v):"
          ,indent 4 $ "state[k] = v" <+> line
          ,"def fprint(a):"
          ,indent 4 $ "print(a)" <+> line]

  genEpilogue :: t Target -> Doc a
  genEpilogue proxy =
    vsep ["if __name__ == \"__main__\":"
          ,indent 4 $ "fmain()" <+> line]
  
genImplFuncDef :: Backend t => t Target -> ImplFuncDef -> Doc a
genImplFuncDef proxy ImplFuncDef{..} = genFuncDef proxy _implFunDef 

genModule :: Backend t => t Target -> Module -> Doc a
genModule proxy Module{..} =
  vsep $
      -- [ "module" <+> namePath proxy _moduleName <+> line]
        [genPrologue proxy]
        ++ (map (genImport proxy) _imports)
        ++ (map (genTopStmt proxy) _topStmts)
        ++ [line, genEpilogue proxy]

genTopStmt :: Backend t => t Target -> TopStmt -> Doc a
genTopStmt proxy TDef{..} = genTypeDef proxy _tdef
genTopStmt proxy EDef{..} = genEffectDef proxy _edef
genTopStmt proxy FDef{..} = genFuncDef proxy _fdef
genTopStmt proxy ImplFDef{..} = genImplFuncDef proxy _implFdef
