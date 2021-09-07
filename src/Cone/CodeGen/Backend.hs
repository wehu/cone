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

  typeN :: t Target -> String -> Doc a
  typeN proxy n = 
    let ns = splitOn "/" n
        ps = init ns
        tn = "T" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [tn]

  funcN :: t Target -> String -> Doc a
  funcN proxy n =
    let ns = splitOn "/" n
        ps = init ns
        fn = "f" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [fn]

  genImport :: t Target -> ImportStmt -> Doc a
  genImport proxy ImportStmt{..} =
    "import" <+> namePath proxy _importPath <+> 
     (case _importAlias of; Just a -> "as" <+> pretty a; _ -> emptyDoc) <+> line

  genTypeDef :: t Target -> TypeDef -> Doc a
  genTypeDef proxy TypeDef{..} = 
    vsep $ ["class" <+> typeN proxy _typeName <> ":"
           ,indent 4 "pass" <+> line
           ] ++ (fmap (genTypeCon proxy _typeName) _typeCons)

  genTypeCon :: t Target -> String -> TypeCon -> Doc a
  genTypeCon proxy ptn TypeCon{..} =
    let tn = typeN proxy _typeConName 
        fn = funcN proxy _typeConName
     in vsep ["class" <+> tn <> parens (typeN proxy ptn) <> ":"
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
    vsep ["def" <+> funcN proxy _funcName <> genArgs <> colon
         ,indent 4 $ case _funcExpr of
                       Just e -> let es = genExpr proxy e
                                  in vsep $ init es ++ ["return" <+> last es]
                       Nothing -> "pass"]
    where genArgs = encloseSep lparen rparen comma $ map pretty $ _funcArgs ^..traverse._1
  
  genExpr :: t Target -> Expr -> [Doc a]
  genExpr proxy EVar{..} = [funcN proxy _evarName]
  genExpr proxy ESeq{..} = join $ fmap (genExpr proxy) _eseq
  genExpr proxy ELit{..} = [pretty _lit]
  genExpr proxy ELam{..} = [parens $ vsep ["def" <+> "lambdaxxx" <+> genArgs <> colon
                                          ,indent 4 $ vsep $ genBody _elamExpr]]
    where genArgs = encloseSep lparen rparen comma $ map pretty $ _elamArgs ^..traverse._1
          genBody e = case e of
                       Just e -> let es = genExpr proxy e
                                  in init es ++ ["return" <+> last es]
                       Nothing -> ["pass"]
  genExpr proxy EWhile{..} = [vsep ["while" <+> (genExpr proxy _ewhileCond) !! 0 <> colon
                                    ,indent 4 $ vsep $ genExpr proxy _ewhileBody]]
  genExpr proxy ELet{..} = [genPattern proxy _eletPattern <+> "=" <+> (genExpr proxy _eletExpr) !! 0]
  genExpr proxy EAnn{..} = genExpr proxy _eannExpr
  genExpr proxy EApp{..} = 
    let fn = _eappFunc ^.evarName
     in case fn of
         "____add" -> binary "+"
         "____sub" -> binary "-"
         "____mul" -> binary "*"
         "____div" -> binary "/"
         "____mod" -> binary "%"
         "____eq" -> binary "=="
         "____ne" -> binary "!="
         "____gt" -> binary ">"
         "____lt" -> binary "<"
         "____ge" -> binary ">="
         "____le" -> binary "<="
         "____and" -> binary "and"
         "____or" -> binary "or"
         "____assign" -> [(funcN proxy $ _eappArgs !! 0 ^.evarName) <+> "=" <+> ((genExpr proxy $ _eappArgs !! 1)) !! 0]
         _ -> [(genExpr proxy _eappFunc) !! 0 <> genArgs]
    where genArgs = encloseSep lparen rparen comma $ map (\a -> (genExpr proxy a) !! 0) _eappArgs
          binary :: String -> [Doc a]
          binary op = [parens $ (genExpr proxy (_eappArgs !! 0)) !! 0 <+> pretty op <+> (genExpr proxy (_eappArgs !! 1)) !! 0]
  -- genExpr proxy EHandle{..} =
          
  genPattern :: t Target -> Pattern -> Doc a
  genPattern proxy PVar{..} = funcN proxy _pvar
  genPattern proxy PExpr{..} = (genExpr proxy _pExpr) !! 0

  genPrologue :: t Target -> Doc a
  genPrologue proxy = 
    vsep ["def "<> funcN proxy "print" <> "(a):"
          ,indent 4 $ "print(a)" <+> line]

  genEpilogue :: t Target -> Doc a
  genEpilogue proxy =
    vsep ["if __name__ == \"__main__\":"
          ,indent 4 $ funcN proxy "main" <> "()" <+> line]
  
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
