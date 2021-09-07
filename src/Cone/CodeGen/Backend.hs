{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module Cone.CodeGen.Backend where

import Cone.Parser.AST
import Data.Proxy
import Data.List
import Control.Lens
import Control.Monad
import Prettyprinter
import Data.List.Split
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Effect.Sum
import Control.Carrier.Error.Either
import Control.Carrier.Fresh.Strict
import Control.Carrier.State.Strict

type Eff s e = Fresh :+: State s :+: Error e

data Env = Env {
  _lambdas :: forall a. [Doc a]
}

makeLenses ''Env

initialEnv =
  Env
    { _lambdas = []
    }

type EnvEff = Eff Env String

data Target

class Backend t where
  gen :: t Target -> Module -> Either String (Doc a)
  gen proxy m = do
    (env, (id, doc)) <- run . runError . (runState initialEnv) . runFresh 0 $ genModule proxy m
    return doc
  
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

  genImport :: (Has EnvEff sig m) => t Target -> ImportStmt -> m (Doc a)
  genImport proxy ImportStmt{..} = return $
    "import" <+> namePath proxy _importPath <+> 
     (case _importAlias of; Just a -> "as" <+> pretty a; _ -> emptyDoc) <+> line

  genTypeDef :: (Has EnvEff sig m) => t Target -> TypeDef -> m (Doc a)
  genTypeDef proxy TypeDef{..} = do
    cons <- mapM (genTypeCon proxy _typeName) _typeCons
    return $
      vsep $ ["class" <+> typeN proxy _typeName <> ":"
             ,indent 4 "pass" <+> line
             ] ++ cons

  genTypeCon :: (Has EnvEff sig m) => t Target -> String -> TypeCon -> m (Doc a)
  genTypeCon proxy ptn TypeCon{..} =
    let tn = typeN proxy _typeConName 
        fn = funcN proxy _typeConName
     in return $ vsep ["class" <+> tn <> parens (typeN proxy ptn) <> ":"
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
  
  genEffectDef :: (Has EnvEff sig m) => t Target -> EffectDef -> m (Doc a)
  genEffectDef proxy e = return emptyDoc
  
  genFuncDef :: (Has EnvEff sig m) => t Target -> FuncDef -> m (Doc a)
  genFuncDef proxy FuncDef{..} = do
    body <- case _funcExpr of
              Just e -> do es <- genExpr proxy e 
                           return $ vsep $ init es ++ ["return" <+> last es]
              Nothing -> return "pass"
    return $ vsep ["def" <+> funcN proxy _funcName <> genArgs <> colon
         ,indent 4 body]
    where genArgs = encloseSep lparen rparen comma $ map pretty $ _funcArgs ^..traverse._1
  
  genExpr :: (Has EnvEff sig m) => t Target -> Expr -> m [Doc a]
  genExpr proxy EVar{..} = return [funcN proxy _evarName]
  genExpr proxy ESeq{..} = do
    es <- mapM (genExpr proxy) _eseq
    return $ join es
  genExpr proxy ELit{..} = return [pretty _lit]
  genExpr proxy ELam{..} = do
    es <- genBody _elamExpr
    return [parens $ vsep ["def" <+> "lambdaxxx" <+> genArgs <> colon
                                          ,indent 4 $ vsep es]]
    where genArgs = encloseSep lparen rparen comma $ map pretty $ _elamArgs ^..traverse._1
          genBody e = case e of
                       Just e -> do es <- genExpr proxy e
                                    return $ init es ++ ["return" <+> last es]
                       Nothing -> return ["pass"]
  genExpr proxy EWhile{..} = do
    c <- head <$> genExpr proxy _ewhileCond
    es <- genExpr proxy _ewhileBody
    return $ [vsep ["while" <+> c <> colon
                   ,indent 4 $ vsep es]]
  genExpr proxy ELet{..} = do
    p <- genPattern proxy _eletPattern
    e <- head <$> genExpr proxy _eletExpr
    return [p <+> "=" <+> e]
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
         "____assign" -> do
           e <- head <$> genExpr proxy (_eappArgs !! 1)
           return [(funcN proxy $ _eappArgs !! 0 ^.evarName) <+> "=" <+> e]
         _ -> do
           f <- head <$> genExpr proxy _eappFunc
           args <- genArgs
           return [f <> args]
    where genArgs = do
            args <- mapM (\a -> head <$> genExpr proxy a) _eappArgs
            return $ encloseSep lparen rparen comma args
          binary :: (Has EnvEff sig m) => String -> m [Doc a]
          binary op = do
            lhs <- head <$> genExpr proxy (_eappArgs !! 0)
            rhs <- head <$> genExpr proxy (_eappArgs !! 1)
            return [parens $ lhs <+> pretty op <+> rhs]
  -- genExpr proxy EHandle{..} =
          
  genPattern :: (Has EnvEff sig m) => t Target -> Pattern -> m (Doc a)
  genPattern proxy PVar{..} = return $ funcN proxy _pvar
  genPattern proxy PExpr{..} = head <$> genExpr proxy _pExpr

  genPrologue :: (Has EnvEff sig m) => t Target -> m (Doc a)
  genPrologue proxy = 
    return $ vsep ["def "<> funcN proxy "print" <> "(a):"
          ,indent 4 $ "print(a)" <+> line]

  genEpilogue :: (Has EnvEff sig m) => t Target -> m (Doc a)
  genEpilogue proxy =
    return $ vsep ["if __name__ == \"__main__\":"
          ,indent 4 $ funcN proxy "main" <> "()" <+> line]
  
genImplFuncDef :: (Has EnvEff sig m) => Backend t => t Target -> ImplFuncDef -> m (Doc a)
genImplFuncDef proxy ImplFuncDef{..} = genFuncDef proxy _implFunDef 

genModule :: (Has EnvEff sig m) => Backend t => t Target -> Module -> m (Doc a)
genModule proxy Module{..} = do
  pre <- genPrologue proxy
  imps <- mapM (genImport proxy) _imports
  tops <- mapM (genTopStmt proxy) _topStmts
  pos <- genEpilogue proxy
  return $ vsep $
      -- [ "module" <+> namePath proxy _moduleName <+> line]
        [pre]
        ++ imps
        ++ tops
        ++ [pos]

genTopStmt :: (Has EnvEff sig m) => Backend t => t Target -> TopStmt -> m (Doc a)
genTopStmt proxy TDef{..} = genTypeDef proxy _tdef
genTopStmt proxy EDef{..} = genEffectDef proxy _edef
genTopStmt proxy FDef{..} = genFuncDef proxy _fdef
genTopStmt proxy ImplFDef{..} = genImplFuncDef proxy _implFdef
