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
import qualified Data.Map as M
import Data.Maybe
import Data.Proxy
import Debug.Trace
import Prettyprinter
import Unbound.Generics.LocallyNameless hiding (Fresh (..), fresh)

data CppHeader a = CppHeader

pythonTypeNamePath n =
  let ns = splitOn "/" n
   in "py::module_::import(\"" <> (pretty $ join $ intersperse "." $ init ns)
        <> "____t\").attr(\""
        <> pretty ("Cone__" ++ last ns)
        <> "\")"

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
      ( "#include \"" <> namePath proxy _importPath <> ".h\""
      )
        <+> line

  genTypeDef proxy TypeDef {..} = do
    cons <- mapM (genTypeCon proxy _typeName) _typeCons
    return $ vsep cons

  genTypeCon proxy ptn TypeCon {..} = underScope $ do
    prefix <- getEnv currentModuleName
    let tn = typeN proxy prefix _typeConName
        fn = funcN proxy prefix _typeConName
     in return $ vsep [ctrFunc fn tn, ctrFuncWrapper fn]
    where
      genArgs init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "const object &t" ++ show (length s)]) init _typeConArgs
      genArgs' init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "t" ++ show (length s)]) init _typeConArgs
      genArgs'' init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "t" ++ show (length s - 3)]) init _typeConArgs
      ctrFunc fn tn =
        "inline object" <+> fn
          <> genArgs ["const cont &____k", "states ____state", "effects ____effs"]
          <+> braces
            ( vsep
                [ "object cntr = " <> pythonTypeNamePath _typeConName <> semi,
                  "return" <+> ("____k" <> parens ("cntr" <> genArgs' ["____k", "____state", "____effs"])) <> semi
                ]
            )
      ctrFuncWrapper fn =
        "inline object" <+> fn <> "_w" <> genArgs []
          <> braces
            ("auto ____state2 = py::list(); ____state2.insert(0, py::dict()); return" <+> (fn <> genArgs'' ["____identity_k", "____state2", "py::list()"]) <> semi)

  genEffectDef proxy EffectDef {..} = do
    prefix <- getEnv currentModuleName
    return $
      vsep $
        map
          ( \intf ->
              if (_intfName intf) == "core/prelude/print"
                then ""
                else
                  "inline object" <+> funcN proxy prefix (_intfName intf)
                    <> genArgs intf ["const cont &, states, effects"] prefix
                    <> "{ throw(\"unimplemented\"); }"
          )
          _effectIntfs
    where
      genArgs intf init prefix = encloseSep lparen rparen comma $ init ++ (map (\_ -> "const object &") $ (_intfArgs intf))

  genFuncDef proxy FuncDef {..} = underScope $ do
    forM_ (_funcArgs ^.. traverse . _1) $ \n -> do
      setEnv (Just True) $ parameters . at n
      l <- getEnv localState
      setEnv (M.delete n l) localState
    prefix <- getEnv currentModuleName
    body <- case _funcExpr of
      Just e -> do
        es <- genExpr proxy e
        return $ "auto ____state2 = py::list(); ____state2.insert(0, py::dict()); return" <+> parens (es <> parens "____k, ____state2, ____effs") <> semi
      Nothing -> return $ "throw \"" <> pretty _funcName <> " is not implemented\";"
    return $
      vsep
        [ "inline object" <+> funcN proxy prefix _funcName <> genArgs' ["const cont &____k", "states ____state", "effects ____effs"] prefix
            <> braces body,
          "inline object" <+> funcN proxy prefix _funcName <> "_w" <> genArgs' [] prefix
            <> braces ("auto ____state2 = py::list(); ____state2.insert(0, py::dict()); return" <+> funcN proxy prefix _funcName <> genArgs ["____identity_k", "____state2", "py::list()"] prefix <> semi)
        ]
    where
      genArgs init prefix = encloseSep lparen rparen comma $ init ++ (map (funcN proxy prefix) $ _funcArgs ^.. traverse . _1)
      genArgs' init prefix = encloseSep lparen rparen comma $ init ++ (map (\a -> "const object &" <+> funcN proxy prefix a) $ _funcArgs ^.. traverse . _1)

  genImplFuncDef _ _ = return emptyDoc

  genExpr proxy EVar {..} = do
    prefix <- getEnv currentModuleName
    l <- getEnv $ localState . at (name2String _evarName)
    p <- getEnv $ parameters . at (name2String _evarName)
    let fn = funcN proxy prefix (name2String _evarName)
        fnQ = "\"" <> fn <> "\""
        vn = case l of
          Just _ -> "py::none()"
          Nothing -> case p of
            Just _ -> fn
            Nothing -> "py::cpp_function" <> parens fn
     in return $
          exprToCps $
            "____k(!____lookup_eff(____effs, " <> fnQ <> ").is(py::none()) ? " <> "____lookup_eff(____effs, " <> fnQ <> ") : "
              <+> "(!____lookup_var(____state, " <> fnQ <> ").is(py::none()) ? " <> "____lookup_var(____state, " <> fnQ <> ") : "
              <+> vn <> "))"
  genExpr proxy ESeq {..} = do
    let e : es = (reverse _eseq)
    e' <- genExpr proxy e
    foldM
      ( \doc e -> do
          e' <- genExpr proxy e
          return $ exprToCps $ callWithCps e' ("[=](const object &____unused) -> object" <> braces ("return" <+> callWithCps doc "____k" <> semi))
      )
      e'
      es
  genExpr proxy ELit {..} =
    return $
      exprToCps $
        "____k"
          <> parens
            ( case _litType of
                TPrim Pred _ -> "py::bool_(" <> pretty _lit <> ")"
                TPrim Unit _ -> "py::none()"
                TPrim I8 _ -> "py::int_(" <> pretty _lit <> ")"
                TPrim I16 _ -> "py::int_(" <> pretty _lit <> ")"
                TPrim I32 _ -> "py::int_(" <> pretty _lit <> ")"
                TPrim I64 _ -> "py::int_(" <> pretty _lit <> ")"
                TPrim U8 _ -> "py::int_(" <> pretty _lit <> ")"
                TPrim U16 _ -> "py::int_(" <> pretty _lit <> ")"
                TPrim U32 _ -> "py::int_(" <> pretty _lit <> ")"
                TPrim U64 _ -> "py::int_(" <> pretty _lit <> ")"
                TPrim F16 _ -> "py::float_(" <> pretty _lit <> ")"
                TPrim F32 _ -> "py::float_(" <> pretty _lit <> ")"
                TPrim F64 _ -> "py::float_(" <> pretty _lit <> ")"
                TPrim Str _ -> "py::str(" <> pretty _lit <> ")"
                _ -> pretty _lit
            )
  genExpr proxy ELam {..} = underScope $ do
    forM_ (_elamArgs ^.. traverse . _1) $ \n -> do
      setEnv (Just True) $ parameters . at n
      l <- getEnv localState
      setEnv (M.delete n l) localState
    es <- genBody _elamExpr
    return $ parens $ "py::cpp_function([=](const cont &____k2, states ____state, effects ____effs) -> object" <+> braces ("return" <+> es <> semi) <> ")"
    where
      genArgs prefix = encloseSep lparen rparen comma $ "const cont &____k" : "states ____state_unused" : "effects ____effs" : (map (\a -> "const object &" <> funcN proxy prefix a) $ _elamArgs ^.. traverse . _1)
      genBody e = do
        prefix <- getEnv currentModuleName
        case e of
          Just e -> do
            es <- genExpr proxy e
            return $ "____k2(" <> (parens $ "py::cpp_function([=]" <+> genArgs prefix <> " -> object " <> braces ("return " <> parens ("____call_cps_with_cleared_vars" <> callCpsWithclearedVars es prefix) <> semi) <> "))")
          Nothing -> throwError $ "lambda expected a expression"
      callCpsWithclearedVars es prefix =
        encloseSep lparen rparen comma $
          "____k" : "____state" : "____effs" : ("std::vector<std::string>" <> encloseSep lbrace rbrace comma (map (\n -> "\"" <> funcN proxy prefix n <> "\"") $ _elamArgs ^.. traverse . _1)) : [es]
  genExpr proxy EWhile {..} = do
    c <- genExpr proxy _ewhileCond
    underScope $ do
      es <- genExpr proxy _ewhileBody
      return $ exprToCps $ "____while" <> encloseSep lparen rparen comma ["____k", "____state", "____effs", c, es]
  genExpr proxy ELet {..} = underScope $ do
    e <- genExpr proxy _eletExpr
    p <- genPatternMatch proxy _eletPattern
    b <- genExpr proxy _eletBody
    return $
      exprToCps $
        callWithCps
          (exprToCps $ callWithCps e ("[=](const object &____e) -> object {return ____k(" <> p <> parens "____e" <> ");}"))
          ("[=](const object &____unused) -> object " <> braces ("return" <+> callWithCps b "____k" <> semi))
  genExpr proxy EAnn {..} = genExpr proxy _eannExpr
  genExpr proxy EApp {..} =
    let fn = name2String $ (removeAnn _eappFunc) ^. evarName
     in case fn of
          "core/prelude/____add" -> binary "____lhs + ____rhs"
          "core/prelude/____sub" -> binary "____lhs - ____rhs"
          "core/prelude/____mul" -> binary "____lhs * ____rhs"
          "core/prelude/____div" -> binary "____lhs / ____rhs"
          "core/prelude/____mod" -> binary "____lhs % ____rhs"
          "core/prelude/____eq" -> binary "py::bool_(____lhs.attr(\"__eq__\")(____rhs))"
          "core/prelude/____ne" -> binary "py::bool_(____lhs.attr(\"__ne__\")(____rhs))"
          "core/prelude/____gt" -> binary "py::bool_(____lhs > ____rhs)"
          "core/prelude/____lt" -> binary "py::bool_(____lhs < ____rhs)"
          "core/prelude/____ge" -> binary "py::bool_(____lhs >= ____rhs)"
          "core/prelude/____le" -> binary "py::bool_(____lhs <= ____rhs)"
          "core/prelude/____and" -> binary "py::bool_(____lhs && ____rhs)"
          "core/prelude/____or" -> binary "py::bool_(____lhs || ____rhs)"
          "core/prelude/____assign" -> do
            prefix <- getEnv currentModuleName
            e <- genExpr proxy (_eappArgs !! 1)
            return $
              exprToCps $
                callWithCps
                  e
                  ( "[=](const object &____e) -> object {return ____k(____update_state(____state, \""
                      <> (funcN proxy prefix $ name2String $ removeAnn (_eappArgs !! 0) ^. evarName)
                      <> "\"," <+> "____e));}"
                  )
          "core/prelude/inline_python" -> return $ exprToCps $ "____k((py::exec(" <> (pretty $ removeAnn (_eappArgs !! 0) ^. lit) <> "), py::none()))"
          _ -> do
            f <- genExpr proxy _eappFunc
            args <- mapM (genExpr proxy) _eappArgs
            let argNames = map (\i -> "____arg" <> pretty i) [0 .. (length _eappArgs) - 1]
            return $
              exprToCps $
                foldl'
                  ( \s (e, n) ->
                      parens $ callWithCps e ("[=](const object &" <> n <> ") -> object" <> braces ("return " <> s <> semi))
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
            callWithCps
              lhs
              ( "[=](const object &____lhs) -> object { return "
                  <> callWithCps rhs ("[=](const object &____rhs) -> object {return ____k(" <+> pretty op <+> ");}")
                  <> ";}"
              )
      removeAnn EAnn {..} = _eannExpr
      removeAnn EAnnMeta {..} = _eannMetaExpr
      removeAnn e = e
  genExpr proxy EHandle {..} = underScope $ do
    prefix <- getEnv currentModuleName
    scope <- genExpr proxy _ehandleScope
    handlers <-
      mapM
        ( \intf -> underScope $ do
            forM_ ((_funcArgs intf) ^.. traverse . _1) $ \n -> do
              setEnv (Just True) $ parameters . at n
              l <- getEnv localState
              setEnv (M.delete n l) localState
            e <- genExpr proxy (fromJust $ _funcExpr intf)
            let n = funcN proxy prefix $ _funcName intf
                args =
                  encloseSep lparen rparen comma $
                    "const cont &____k" :
                    "states ____state_unused" :
                    "effects ____effs" :
                    (map (\(n, _) -> "const object &" <> funcN proxy prefix n) (_funcArgs intf))
            return $
              "{\"" <> n <> "\", "
                <+> parens
                  ( "py::cpp_function([=]" <+> args <> " -> object "
                      <> braces
                        ("return ____call_with_resumed_k(____k, ____state, ____effs, " <> e <> ");")
                      <> ")"
                  )
                  <> "}"
        )
        _ehandleBindings
    return $
      exprToCps $
        "____handle(____k, ____state, ____effs, " <> scope <> comma
          <+> (encloseSep lbrace rbrace comma handlers) <> ")"
  genExpr proxy ECase {..} = do
    c <- genExpr proxy _ecaseExpr
    pes <- mapM (\pe -> underScope $ (,) <$> genPatternMatch proxy (_casePattern pe) <*> genExpr proxy (_caseExpr pe)) $ _ecaseBody
    let cs = [fst pe | pe <- pes]
        es = [snd pe | pe <- pes]
    return $
      exprToCps $
        "py::cast<funcWithCont>(" <> c <> ")"
          <> encloseSep
            lparen
            rparen
            comma
            [ "[=](const object &____c) -> object { return ____case(____k, ____state, ____effs, ____c" <> comma
                <+> encloseSep lbrace rbrace comma cs <> comma
                <+> encloseSep lbrace rbrace comma es <> ");}",
              "____state",
              "____effs"
            ]
  genExpr proxy EAnnMeta {..} = genExpr proxy _eannMetaExpr
  genExpr proxy e = throwError $ "unsupported expression: " ++ ppr e ++ ppr (_eloc e)

  genPatternMatch proxy PVar {..} = do
    setEnv (Just True) $ localState . at (name2String _pvar)
    prefix <- getEnv currentModuleName
    return $
      parens $
        "[=](const object &____e) -> object {____add_var(____state, \"" <> funcN proxy prefix (name2String _pvar)
          <> "\""
          <> comma <+> "____e); return py::bool_(true);}"
  genPatternMatch proxy PExpr {..} = do
    p <- (\e -> callWithCps e "____identity_k") <$> genExpr proxy _pExpr
    return $ parens $ "[=](const object &____e) -> object { return py::bool_(" <+> p <+> ".attr(\"__eq__\")(____e));}"
  genPatternMatch proxy PApp {..} = do
    prefix <- getEnv currentModuleName
    bindings <-
      mapM
        ( \(p, ee) -> do
            b <- genPatternMatch proxy p
            return $
              parens $
                "py::isinstance(____e" <> comma
                  <+> pythonTypeNamePath (name2String $ _evarName _pappName) <> ") && " <> b <> parens ee
        )
        [(arg, parens $ "____e.attr(\"f" <> pretty id <> "\")") | arg <- _pappArgs | id <- [0 :: Int ..]]
    return $ parens $ "[=](const object &____e) -> object { return py::bool_" <> encloseSep lparen rparen "&&" bindings <> ";}"

  genPrologue _ = return emptyDoc

  genEpilogue _ = return emptyDoc

  genModule proxy Module {..} = do
    let modulePs = splitOn "/" _moduleName
    setEnv _moduleName currentModuleName
    pre <- genPrologue proxy
    imps <- mapM (genImport proxy) _imports
    tops <- mapM (genTopStmt proxy) _topStmts
    pos <- genEpilogue proxy
    return $
      vsep $
        [ "#pragma once",
          "#include <iostream>",
          "#include \"cone/builtins.h\"",
          "#include \"core/prelude.h\""
        ]
          ++ imps
          ++ [ "namespace py = pybind11;",
               "namespace cone{",
               sep $ map (\n -> "namespace" <+> pretty n <+> lbrace) modulePs
             ]
          ++ [pre]
          ++ tops
          ++ [pos]
          ++ ["}", sep $ map (\_ -> rbrace) modulePs]

-- | Convert a experision to cps
exprToCps :: Doc a -> Doc a
exprToCps e =
  parens $
    "py::cpp_function([=](" <+> "const cont &____k"
      <> comma <+> "states ____state"
      <> comma <+> "effects ____effs"
      <> ") -> object " <+> braces ("return" <+> e <> semi)
      <> ")"

-- | Call a cps function
callWithCps :: Doc a -> Doc a -> Doc a
callWithCps e k = parens $ "py::cast<funcWithCont>(" <> e <> ")" <> (encloseSep lparen rparen comma $ (parens k) : "____state" : ["____effs"])
