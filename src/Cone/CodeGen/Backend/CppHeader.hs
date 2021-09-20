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
        "#include" <+> "\"" <> namePath proxy _importPath <> ".h\""
        <+> line

  genTypeDef proxy TypeDef {..} = do
    cons <- mapM (genTypeCon proxy _typeName) _typeCons
    return $ vsep cons

  genTypeCon proxy ptn TypeCon {..} = do
    prefix <- getEnv currentModuleName
    let tn = typeN proxy prefix _typeConName
        fn = funcN proxy prefix _typeConName
     in return $
          vsep
            [ "struct" <+> tn <+> braces (vsep [
              indent 4 $ constructor tn,
              indent 4 $ eq tn]),
              ctrFunc fn tn,
              ctrFuncWrapper fn tn <+> line
            ]
    where
      constructor tn =
        tn <> genArgs ["const cont &____k", "states &&____state", "effects &&____effs"] <+> braces (indent 4 $ vsep genFields)
      eq tn =
        "bool operator==(const object &other)" <+> braces (
            indent 4 $ "return" <+> "other.type() == typeid(" <> tn <> ") &&" <+> cmpFields tn <> semi)
      fields = encloseSep lparen rparen comma $ ["object f" <> pretty i | i <- [0 .. length (_typeConArgs) - 1]]
      cmpFields tn = encloseSep lparen rparen " && " $ "true" : ["f" <> pretty i <+> "==" <+> 
         "std::any_cast<"<> tn <> ">(other).f" <> pretty i | i <- [0 .. length (_typeConArgs) - 1]]
      genArgs init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "const object &t" ++ show (length s)]) init _typeConArgs
      genFields =
            foldl'
              ( \s e ->
                  let i = length s
                      f = "f" ++ show i
                      a = "t" ++ show (i + 4)
                   in s ++ [pretty f <+> "=" <+> pretty a <> semi]
              )
              []
              _typeConArgs
      ctrFunc fn tn =
        tn <+> fn <> genArgs ["const cont &____k", "states &&____state", "effects &&____effs"] <> braces (
            indent 4 ("return" <+> ("____k" <> parens (tn <> genArgs ["____k", "std::move(____state)", "std::move(____effs)"]))))
      ctrFuncWrapper tn fn =
        tn <+> fn <> "_w" <> genArgs [] <> braces (
            indent 4 ("return" <+> (fn <> genArgs ["identity_k", "{{}}", "{}"])))

  genEffectDef proxy e = return emptyDoc

  genFuncDef proxy FuncDef {..} = do
    prefix <- getEnv currentModuleName
    body <- case _funcExpr of
      Just e -> do
        es <- genExpr proxy e
        return $ "return" <+> parens (es <> parens "____k, [{}], ____effs")
      Nothing -> return $ "raise Exception(\"" <> pretty _funcName <> " is not implemented\")"
    return $
      vsep
        [ "def" <+> funcN proxy prefix _funcName <> genArgs ["____k", "____state", "____effs"] prefix <> colon,
          indent 4 body,
          "def" <+> funcN proxy prefix _funcName <> "_w" <> genArgs [] prefix <> colon,
          indent 4 $ "return" <+> funcN proxy prefix _funcName <> genArgs ["lambda x:x", "[{}]", "[]"] prefix
        ]
    where
      genArgs init prefix = encloseSep lparen rparen comma $ init ++ (map (funcN proxy prefix) $ _funcArgs ^.. traverse . _1)

  genExpr proxy EVar {..} = do
    prefix <- getEnv currentModuleName
    let fn = funcN proxy prefix (name2String _evarName)
        fnQ = "\"" <> fn <> "\""
     in return $
          exprToCps $
            "____k(____lookup_eff(____effs, " <> fnQ <> ") if " <> "____lookup_eff(____effs, " <> fnQ <> ") != None"
              <+> "else (____lookup_var(____state, " <> fnQ <> ") if"
              <+> "____lookup_var(____state, " <> fnQ <> ") != None else"
              <+> fn <> "))"
  genExpr proxy ESeq {..} = do
    let e : es = (reverse _eseq)
    e' <- genExpr proxy e
    foldM
      ( \doc e -> do
          e' <- genExpr proxy e
          return $ exprToCps $ callWithCps e' ("lambda ____unused: " <> callWithCps doc "____k")
      )
      e'
      es
  genExpr proxy ELit {..} =
    return $
      exprToCps $
        "____k"
          <> parens
            ( case _litType of
                TPrim Pred _ -> if _lit == "true" then "True" else "False"
                TPrim Unit _ -> "None"
                _ -> pretty _lit
            )
  genExpr proxy ELam {..} = do
    es <- genBody _elamExpr
    return $ parens $ "lambda ____k2, ____state, ____effs" <> colon <+> es
    where
      genArgs prefix = encloseSep emptyDoc emptyDoc comma $ "____k" : "____state_unused" : "____effs" : (map (funcN proxy prefix) $ _elamArgs ^.. traverse . _1)
      genBody e = do
        prefix <- getEnv currentModuleName
        case e of
          Just e -> do
            es <- genExpr proxy e
            return $ "____k2(" <> (parens $ "lambda" <+> genArgs prefix <> colon <+> parens ("____call_cps_with_cleared_vars" <> callCpsWithclearedVars es prefix)) <> ")"
          Nothing -> throwError $ "lambda expected a expression"
      callCpsWithclearedVars es prefix =
        encloseSep lparen rparen comma $
          "____k" : "____state" : "____effs" : (encloseSep lbracket rbracket comma $ map (\n -> "\"" <> funcN proxy prefix n <> "\"") $ _elamArgs ^.. traverse . _1) : [es]
  genExpr proxy EWhile {..} = do
    c <- genExpr proxy _ewhileCond
    es <- genExpr proxy _ewhileBody
    return $ exprToCps $ "____while" <> encloseSep lparen rparen comma ["____k", "____state", "____effs", c, es]
  genExpr proxy ELet {..} = do
    e <- genExpr proxy _eletExpr
    p <- genPatternMatch proxy _eletPattern
    b <- genExpr proxy _eletBody
    return $ exprToCps $ callWithCps (exprToCps $ callWithCps e ("lambda ____e: ____k(" <> p <> parens "____e" <> ")")) ("lambda ____unused: " <> callWithCps b "____k")
  genExpr proxy EAnn {..} = genExpr proxy _eannExpr
  genExpr proxy EApp {..} =
    let fn = name2String $ (removeAnn _eappFunc) ^. evarName
     in case fn of
          "core/prelude/____add" -> binary "+"
          "core/prelude/____sub" -> binary "-"
          "core/prelude/____mul" -> binary "*"
          "core/prelude/____div" -> binary "/"
          "core/prelude/____mod" -> binary "%"
          "core/prelude/____eq" -> binary "=="
          "core/prelude/____ne" -> binary "!="
          "core/prelude/____gt" -> binary ">"
          "core/prelude/____lt" -> binary "<"
          "core/prelude/____ge" -> binary ">="
          "core/prelude/____le" -> binary "<="
          "core/prelude/____and" -> binary "and"
          "core/prelude/____or" -> binary "or"
          "core/prelude/____assign" -> do
            prefix <- getEnv currentModuleName
            e <- genExpr proxy (_eappArgs !! 1)
            return $
              exprToCps $
                callWithCps
                  e
                  ( "lambda ____e : ____k(____update_state(____state, \""
                      <> (funcN proxy prefix $ name2String $ removeAnn (_eappArgs !! 0) ^. evarName)
                      <> "\"," <+> "____e))"
                  )
          "core/prelude/inline_python" -> return $ exprToCps $ "____k(" <> (pretty $ (read (removeAnn (_eappArgs !! 0) ^. lit) :: String)) <> ")"
          _ -> do
            f <- genExpr proxy _eappFunc
            args <- mapM (genExpr proxy) _eappArgs
            let argNames = map (\i -> "____arg" <> pretty i) [0 .. (length _eappArgs) - 1]
            return $
              exprToCps $
                foldl'
                  ( \s (e, n) ->
                      parens $ callWithCps e ("lambda " <> n <> ": " <> s)
                  )
                  ("____f" <> (encloseSep lparen rparen comma ("____k" : "____state" : "____effs" : argNames)))
                  [(e, n) | e <- (reverse $ f : args) | n <- (reverse $ "____f" : argNames)]
    where
      binary :: (Has EnvEff sig m) => String -> m (Doc a)
      binary op = do
        lhs <- genExpr proxy (_eappArgs !! 0)
        rhs <- genExpr proxy (_eappArgs !! 1)
        return $
          exprToCps $
            callWithCps rhs $
              callWithCps lhs ("lambda ____lhs: (lambda ____rhs : ____k(____lhs" <+> pretty op <+> "____rhs))")
      removeAnn EAnn {..} = _eannExpr
      removeAnn EAnnMeta {..} = _eannMetaExpr
      removeAnn e = e
  genExpr proxy EHandle {..} = do
    prefix <- getEnv currentModuleName
    scope <- genExpr proxy _ehandleScope
    handlers <-
      mapM
        ( \intf -> do
            e <- genExpr proxy (fromJust $ _funcExpr intf)
            let n = funcN proxy prefix $ _funcName intf
                args =
                  encloseSep emptyDoc emptyDoc comma $
                    "____k" :
                    "____state_unused" :
                    "____effs" :
                    (map (\(n, _) -> funcN proxy prefix n) (_funcArgs intf))
            return $
              "\"" <> n <> "\" :"
                <+> parens
                  ( "lambda" <+> args <> colon
                      <+> "____call_with_resumed_k(____k, ____state, ____effs, " <> e <> ")"
                  )
        )
        _ehandleBindings
    return $
      exprToCps $
        "____handle(____k, ____state, ____effs, " <> scope <> comma
          <+> (encloseSep lbrace rbrace comma handlers) <> ")"
  genExpr proxy ECase {..} = do
    c <- genExpr proxy _ecaseExpr
    cs <- mapM (genPatternMatch proxy) $ _ecaseBody ^.. traverse . casePattern
    es <- mapM (genExpr proxy) $ _ecaseBody ^.. traverse . caseExpr
    return $
      exprToCps $
        c
          <> encloseSep
            lparen
            rparen
            comma
            [ "lambda ____c: ____case(____k, ____state, ____effs, ____c" <> comma
                <+> encloseSep lbracket rbracket comma cs <> comma
                <+> encloseSep lbracket rbracket comma es <> ")",
              "____state",
              "____effs"
            ]
  genExpr proxy EAnnMeta {..} = genExpr proxy _eannMetaExpr
  genExpr proxy e = throwError $ "unsupported expression: " ++ ppr e ++ ppr (_eloc e)

  genPatternMatch proxy PVar {..} = do
    prefix <- getEnv currentModuleName
    return $
      parens $
        "lambda ____e: [____add_var(____state, \"" <> funcN proxy prefix (name2String _pvar)
          <> "\""
          <> comma <+> "____e), True][-1]"
  genPatternMatch proxy PExpr {..} = do
    p <- (\e -> callWithCps e "lambda x : x") <$> genExpr proxy _pExpr
    return $ parens $ "lambda ____e:" <+> p <+> "== ____e"
  genPatternMatch proxy PApp {..} = do
    prefix <- getEnv currentModuleName
    bindings <-
      mapM
        ( \(p, ee) -> do
            b <- genPatternMatch proxy p
            return $
              parens $
                "isinstance(____e" <> comma
                  <+> typeN proxy prefix (name2String $ _evarName _pappName) <> ") and " <> b <> parens ee
        )
        [(arg, parens $ "____e" <> ".f" <> pretty id) | arg <- _pappArgs | id <- [0 :: Int ..]]
    return $ parens $ "lambda ____e: all(" <> encloseSep lbracket rbracket comma bindings <> ")"

  genPrologue proxy = do
    prefix <- getEnv currentModuleName
    return emptyDoc 

  genEpilogue proxy = do
    prefix <- getEnv currentModuleName
    return $
      vsep
        [ "if __name__ == \"__main__\":",
          indent 4 $ funcN proxy prefix "main_w()" <+> line
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
        [ "#include \"core/prelude.h\""
        ]
          ++ imps
          ++ [pre]
          ++ tops
          ++ [pos]

-- | Convert a experision to cps
exprToCps :: Doc a -> Doc a
exprToCps e = parens $ "lambda" <+> "____k" <> comma <+> "____state" <> comma <+> "____effs" <> colon <+> e

-- | Call a cps function
callWithCps :: Doc a -> Doc a -> Doc a
callWithCps e k = parens $ e <> (encloseSep lparen rparen comma $ (parens k) : "____state" : ["____effs"])