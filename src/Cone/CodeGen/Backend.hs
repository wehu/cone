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
import Data.Maybe
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Effect.Sum
import Control.Carrier.Error.Either
import Control.Carrier.Fresh.Strict
import Control.Carrier.State.Strict

type Eff s e = Fresh :+: State s :+: Error e

data Env = Env {
  _lambdas :: [String]
}

makeLenses ''Env

initialEnv =
  Env
    { _lambdas = []
    }

type EnvEff = Eff Env String

-- | Get value by a lens from env
getEnv :: (Has EnvEff sig m) => Getter Env a -> m a
getEnv l = do
  env <- get @Env
  return $ view l env

-- | Set value by a lens into env
setEnv :: (Has EnvEff sig m) => b -> Setter Env Env a b -> m ()
setEnv v l = do
  env <- get @Env
  put $ set l v env

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
        tn = "Cone__" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [tn]

  funcN :: t Target -> String -> Doc a
  funcN proxy n =
    let ns = splitOn "/" n
        ps = init ns
        fn = "cone__" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [fn]

  genImport :: (Has EnvEff sig m) => t Target -> ImportStmt -> m (Doc a)
  genImport proxy ImportStmt{..} = return $
    "import" <+> namePath proxy _importPath <+> 
     (case _importAlias of; Just a -> "as" <+> pretty a; _ -> emptyDoc) <+> line

  genTypeDef :: (Has EnvEff sig m) => t Target -> TypeDef -> m (Doc a)
  genTypeDef proxy TypeDef{..} = do
    cons <- mapM (genTypeCon proxy _typeName) _typeCons
    return $
      vsep $ {-["class" <+> typeN proxy _typeName <> ":"
             ,indent 4 "pass" <+> line
             ] ++-} cons

  genTypeCon :: (Has EnvEff sig m) => t Target -> String -> TypeCon -> m (Doc a)
  genTypeCon proxy ptn TypeCon{..} =
    let tn = typeN proxy _typeConName 
        fn = funcN proxy _typeConName
     in return $ vsep ["class" <+> tn {- <> parens (typeN proxy ptn) -} <> ":"
          ,indent 4 constructor
          ,ctrFunc fn tn
          ,ctrFuncWrapper fn <+> line]
    where constructor =
            vsep ["def" <+> "__init__" <> genArgs ["self", "____k", "____state"] <> colon
                 ,indent 4 $ vsep genFields]
          genArgs init = encloseSep lparen rparen comma $ 
                 foldl' (\s e -> s ++ [pretty $ "t" ++ show (length s)]) init _typeConArgs
          genFields =
            if _typeConArgs == []
            then ["pass"]
            else foldl' (\s e -> 
                  let i = length s
                      f = "self.f" ++ show i
                      a = "t" ++ show (i + 3)
                   in s++[pretty f <+> "=" <+> pretty a]) [] _typeConArgs
          ctrFunc fn tn = vsep ["def" <+> fn <> genArgs ["____k", "____state"] <> ":"
                               ,indent 4 ("return" <+> (tn <> genArgs ["____k", "____state"]))]
          ctrFuncWrapper fn = vsep ["def" <+> fn <> "_w" <> genArgs [] <> ":"
                                   ,indent 4 ("return" <+> (fn <> genArgs ["lambda x:x", "{}"]))]
  
  genEffectDef :: (Has EnvEff sig m) => t Target -> EffectDef -> m (Doc a)
  genEffectDef proxy e = return emptyDoc
  
  genFuncDef :: (Has EnvEff sig m) => t Target -> FuncDef -> m (Doc a)
  genFuncDef proxy FuncDef{..} = do
    body <- case _funcExpr of
              Just e -> do es <- genExpr proxy e 
                           return $ "return" <+> callWithCps es
              Nothing -> return "pass"
    return $ vsep ["def" <+> funcN proxy _funcName <> genArgs ["____k","____state"] <> colon
                  ,indent 4 body
                  ,"def" <+> funcN proxy _funcName <> "_w" <> genArgs [] <> colon
                  ,indent 4 $ "return" <+> funcN proxy _funcName <> genArgs ["lambda x:x", "{}"]]
    where genArgs init = encloseSep lparen rparen comma $ init ++ (map (funcN proxy) $ _funcArgs ^..traverse._1)
  
  genExpr :: (Has EnvEff sig m) => t Target -> Expr -> m (Doc a)
  genExpr proxy EVar{..} = 
    let fn = funcN proxy _evarName
        fnQ = "\"" <> fn <> "\""
     in return $ exprToCps $ "____state[" <> fnQ <> "] if" <+> fnQ <+> "in" <+> "____state" <+> "else" <+> fn 
  genExpr proxy ESeq{..} = do
    let e:es = (reverse _eseq)
    e' <- genExpr proxy e
    foldM (\doc e -> do
      e' <- genExpr proxy e
      return $ exprToCps $ brackets (callWithCps e' <> comma <+> callWithCps doc) <> brackets "-1")
      e'
      es
  genExpr proxy ELit{..} = return $ exprToCps $ pretty _lit
  genExpr proxy ELam{..} = do
    es <- genBody _elamExpr
    return $ parens $ "lambda ____k, ____state" <> colon <+> es
    where genArgs = encloseSep emptyDoc emptyDoc comma $ "____k":"____state":(map (funcN proxy) $ _elamArgs ^..traverse._1)
          genBody e = case e of
                       Just e -> do es <- genExpr proxy e
                                    return $ "lambda" <+> genArgs <> colon <+> callWithCpsClonedState es
                       Nothing -> return $ "lambda" <+> colon <> "pass"
  genExpr proxy EWhile{..} = do
    c <- genExpr proxy _ewhileCond
    es <- genExpr proxy _ewhileBody
    return $ exprToCps $ "____while" <> encloseSep lparen rparen comma ["____k", "____state", c, es]
  genExpr proxy ELet{..} = do
    e <- callWithCps <$> genExpr proxy _eletExpr
    exprToCps <$> genPatternMatch proxy _eletPattern e
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
           e <- genExpr proxy (_eappArgs !! 1)
           return $ exprToCps $ "____update_state(____state, \"" <> (funcN proxy $ _eappArgs !! 0 ^.evarName) <> "\"," <+> callWithCps e <> ")"
         _ -> do
           f <- genExpr proxy _eappFunc
           args <- genArgs
           return $ exprToCps $ callWithCps f <> args
    where genArgs = do
            args <- mapM (\a -> callWithCps <$> genExpr proxy a) _eappArgs
            return $ encloseSep lparen rparen comma $ "____k":"____state":args
          binary :: (Has EnvEff sig m) => String -> m (Doc a)
          binary op = do
            lhs <- callWithCps <$> genExpr proxy (_eappArgs !! 0)
            rhs <- callWithCps <$> genExpr proxy (_eappArgs !! 1)
            return $ exprToCps $ lhs <+> pretty op <+> rhs
  genExpr proxy EHandle{..} = do
    scope <- genExpr proxy _ehandleScope
    handlers <- mapM (\intf -> do
      e <- genExpr proxy (fromJust $ _funcExpr intf)
      let n = funcN proxy $ _funcName intf
          args = encloseSep emptyDoc emptyDoc comma $ "____k":"____state":(map (\(n, _) -> funcN proxy n) (_funcArgs intf))
      return $ "\"" <> n <> "\" :" <+> parens ("lambda" <+> args <> colon <+> callWithCps e)) _ehandleBindings
    return $ exprToCps $ "____handle(____k, ____state, " <> scope <> comma <+> 
      (encloseSep lbrace rbrace comma handlers) <> ")"
  genExpr proxy ECase{..} = do
    c <- callWithCps <$> genExpr proxy _ecaseExpr
    cs <- mapM (\p -> exprToCps <$> genPatternMatch proxy p c) $ _ecaseBody ^.. traverse . casePattern
    es <- mapM (genExpr proxy) $ _ecaseBody ^.. traverse . caseExpr
    return $ exprToCps $ "____case(____k, ____state, " <> 
        encloseSep lbracket rbracket comma cs <> comma <+>
        encloseSep lbracket rbracket comma es <> ")"
  genExpr proxy e = throwError $ "unsupported expression: " ++ ppr e ++ ppr (_eloc e)
          
  genPatternMatch :: (Has EnvEff sig m) => t Target -> Pattern -> Doc a -> m (Doc a)
  genPatternMatch proxy PVar{..} e = 
    return $ "[____update_state(____state, \"" <> funcN proxy _pvar <> "\""<> comma <+> e <> "), True][-1]"
  genPatternMatch proxy PExpr{..} e = do
    p <- callWithCps <$> genExpr proxy _pExpr
    return $ parens $ p <+> "==" <+> e
  genPatternMatch proxy PApp{..} e = do
    bindings <- mapM (\(p, e) -> do
                b <- genPatternMatch proxy p e
                return $ encloseSep lbracket rbracket comma 
                 [b, "isinstance(" <> e <> comma <+> typeN proxy _pappName <> ")"] <> brackets "-1") 
               [(arg, parens $ e <> ".f" <> pretty id) | arg <- _pappArgs | id <- [0::Int ..]]
    return $ encloseSep lbracket rbracket comma bindings

  genPrologue :: (Has EnvEff sig m) => t Target -> m (Doc a)
  genPrologue proxy = 
    return $
     vsep ["def "<> funcN proxy "print(k, s, a):"
          ,indent 4 $ "print(a)"
          ,"def ____update_state(state, k, v):"
          ,indent 4 $ "state[k] = v"
          ,"def ____while(____k, ____state, cond, body):"
          ,indent 4 $ vsep ["if cond(____k, ____state):"
                           ,indent 4 $ "[body(____k, ____state), ____while(____k, ____state, cond, body)][-1]"
                           ,"else:"
                           ,indent 4 $ "pass"]
          ,"def ____case(____k, ____state, conds, exprs):"
          ,indent 4 $ vsep ["for (p, e) in zip(conds, exprs):"
                           ,indent 4 $ vsep ["if p(____k, ____state):"
                                            ,indent 4 $ "return e(____k, ____state)"]]
          ,"def ____handle(____k, ____state, scope, handlers):"
          ,indent 4 $ vsep ["____state.update(handlers)"
                           ,"scope(lambda x: x, ____state)"]
          ,"def "<> funcN proxy "resume(k, s, a):"
          ,indent 4 $ "return k(a)"
          ,"unit = None"
          ,"true = True"
          ,"false = False"]

  genEpilogue :: (Has EnvEff sig m) => t Target -> m (Doc a)
  genEpilogue proxy = do
    ls <- getEnv lambdas
    return $ vsep $ map pretty ls ++ 
          ["if __name__ == \"__main__\":"
          ,indent 4 $ funcN proxy "main_w()" <+> line]

exprToCps :: Doc a -> Doc a
exprToCps e = parens $ "lambda" <+> "____k" <> comma <+> "____state" <> colon <+> e

callWithCps :: Doc a -> Doc a
callWithCps e = parens $ e <> (encloseSep lparen rparen comma $ "____k":"____state":[])

callWithCpsEmptyState :: Doc a -> Doc a
callWithCpsEmptyState e = parens $ e <> lparen <> "____k" <> comma <+> "{}" <> rparen

callWithCpsClonedState :: Doc a -> Doc a
callWithCpsClonedState e = parens $ e <> lparen <> "____k" <> comma <+> "____state.copy()" <> rparen

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
