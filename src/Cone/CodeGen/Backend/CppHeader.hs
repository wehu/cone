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
   in "py::module_::import(\"" <> pretty (join (intersperse "." (init ns)))
        <> "____t\").attr(\""
        <> pretty ("Cone__" ++ last ns)
        <> "\")"

genTopFw :: (Has EnvEff sig m, Backend t) => t Target -> TopStmt -> m (Doc a)
genTopFw proxy TDef {..} = do
  cons <- mapM (genTypeCon proxy) (_typeCons _tdef)
  return $ vsep cons
  where
    genTypeCon proxy TypeCon{..} = do
      prefix <- getEnv currentModuleName
      let fn = funcN proxy prefix _typeConName
       in return $ vsep [ctrFunc fn]
      where
        genArgTypesInternal init =
          encloseSep lparen rparen comma $
            foldl' (\s e -> s ++ ["const object_t &"]) init _typeConArgs
        ctrFunc fn =
          "extern const std::function<object_t" <> genArgTypesInternal ["const cont_t &", "stack_t", "effects_t"] <> ">" <+> fn <> semi
genTopFw proxy FDef {..} = do
  prefix <- getEnv currentModuleName
  return $
    vsep
      [ "extern const std::function<object_t" <> genArgTypesInternal ["const cont_t &", "stack_t", "effects_t"] <> ">"
          <+> funcN proxy prefix (_funcName _fdef) <> semi
      ]
  where
    genArgTypesInternal init = encloseSep lparen rparen comma $
       init ++ map (const "const object_t &") (_funcArgs _fdef ^.. traverse . _1)
genTopFw proxy _ = return emptyDoc

evalType1 :: Type -> [Type] -> (Int -> Int) -> Type
evalType1 t args f =
  if not (any (isn't _TNum) args)
    then
      let arg : rest = fmap _tnum args
       in TNum (fmap f arg) (_tloc t)
    else t

evalType2 :: Type -> [Type] -> (Int -> Int -> Int) -> Type
evalType2 t args f =
  if not (any (isn't _TNum) args)
    then
      let arg : rest = fmap _tnum args
       in TNum (foldl' (\a b -> f <$> a <*> b) arg rest) (_tloc t)
    else t

inferType :: Type -> Type
inferType a@TApp {..} =
  let args = map inferType _tappArgs
      t = a {_tappArgs = args}
   in case name2String (_tvar _tappName) of
    "core/prelude/neg" -> evalType1 t args (\e -> (-e))
    "core/prelude/add" -> evalType2 t args (+)
    "core/prelude/sub" -> evalType2 t args (-)
    "core/prelude/mul" -> evalType2 t args (*)
    "core/prelude/div" -> evalType2 t args div
    "core/prelude/mod" -> evalType2 t args mod
    "core/prelude/max" -> evalType2 t args max
    "core/prelude/min" -> evalType2 t args min
    _ -> t
inferType a@TAnn {..} =
  let t = inferType _tannType
   in a {_tannType = t}
inferType l@TList {..} =
  let es = map inferType _tlist
   in l {_tlist = es}
inferType t = t

genTypeInfo :: Type -> Doc a
genTypeInfo t@TList {..} = "[]()" <> braces
  (fst (foldl'
    ( \(s, i) e ->
        (s <>
          "____t" <> brackets (pretty i) <> "=" <>
           (case e of
             TNum d _ -> maybe "-1" pretty d
             t -> genTypeInfo t) <> semi,
        i+1)
    )
    ("auto ____t =  py::tuple(" <> pretty (length _tlist) <> ");", 0::Int)
    _tlist) <> "return ____t;") <> "()"
genTypeInfo TPrim{..} =
  case _tprim of
    I8  -> "py::module_::import(\"numpy\").attr(\"int8\")"
    I16 -> "py::module_::import(\"numpy\").attr(\"int16\")"
    I32 -> "py::module_::import(\"numpy\").attr(\"int32\")"
    I64 -> "py::module_::import(\"numpy\").attr(\"int64\")"
    U8  -> "py::module_::import(\"numpy\").attr(\"uint8\")"
    U16 -> "py::module_::import(\"numpy\").attr(\"uint16\")"
    U32 -> "py::module_::import(\"numpy\").attr(\"uint32\")"
    U64 -> "py::module_::import(\"numpy\").attr(\"uint64\")"
    F16 -> "py::module_::import(\"numpy\").attr(\"float16\")"
    F32 -> "py::module_::import(\"numpy\").attr(\"float32\")"
    F64 -> "py::module_::import(\"numpy\").attr(\"float64\")"
    Pred -> "py::module_::import(\"numpy\").attr(\"bool8\")"
    Str -> "py::module_::import(\"numpy\").attr(\"string_\")"
    _ -> "py::none()"
genTypeInfo t = "py::none()"

genTypeArgs :: [Type] -> Doc a
genTypeArgs ts = "py::object([]()" <> braces
  (fst (foldl'
    ( \(s, i) t ->
        (s <> "____t" <> brackets (pretty i) <> "=" <> genTypeInfo t <> semi,
        i+1)
    )
    ("auto ____t =  py::list(" <> pretty (length ts) <> ");", 0::Int)
    (map inferType ts)) <> "return ____t;") <> "())"

builtinFuncs = ["core/prelude/inline_python",
                "data/tensor/full"]

instance Backend CppHeader where
  namePath proxy n = pretty n

  typeN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == take prefixLen n' then drop (prefixLen + 1) n' else n'
        ns = splitOn "/" n
        ps = init ns
        tn = "Cone__" ++ last ns
     in pretty $ join $ intersperse "::" $ ps ++ [tn]

  funcN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == take prefixLen n' then drop (prefixLen + 1) n' else n'
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
      genWrapperArgTypes init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "const py::object &t" ++ show (length s)]) init _typeConArgs
      genCntrArgs init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "____to_py_object(t" ++ show (length s) ++ ")"]) init _typeConArgs
      genWrapperArgs init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "t" ++ show (length s - 3)]) init _typeConArgs
      genArgsInternal init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ [pretty $ "const object_t &t" ++ show (length s)]) init _typeConArgs
      genArgTypesInternal init =
        encloseSep lparen rparen comma $
          foldl' (\s e -> s ++ ["const object_t &"]) init _typeConArgs
      ctrFunc fn tn =
        "const std::function<object_t" <> genArgTypesInternal ["const cont_t &", "stack_t", "effects_t"] <> ">" <+> fn <> "= [=]"
          <> genArgsInternal ["const cont_t &____k", "stack_t ____stack", "effects_t ____effs"]
          <> " -> object_t "
          <+> braces
            ( vsep
                [ "py::object cntr = " <> pythonTypeNamePath _typeConName <> semi,
                  "return" <+> ("____k(py::object" <> parens ("cntr" <> genCntrArgs ["py::none()", "py::none()", "py::none()"])) <> ")" <> semi
                ]
            )
          <> semi
      ctrFuncWrapper fn =
        "inline py::object" <+> fn <> "_w____" <> genWrapperArgTypes []
          <> braces
            ("return ____to_py_object(" <> (fn <> genWrapperArgs ["____identity_k", "____make_empty_stack()", "____make_empty_effs()"]) <> ")" <> semi)

  genEffectDef proxy EffectDef {..} = do
    prefix <- getEnv currentModuleName
    return $
      vsep $
        map
          ( \intf ->
              if (_intfName intf) == "core/prelude/print"
                then ""
                else
                  "inline object_t" <+> funcN proxy prefix (_intfName intf)
                    <> genArgs intf ["const cont_t &, stack_t, effects_t"] prefix
                    <> "{ throw ____cone_exception(\"unimplemented\"); }"
          )
          _effectIntfs
    where
      genArgs intf init prefix = encloseSep lparen rparen comma $ init ++ (map (\_ -> "const object_t &") $ (_intfArgs intf))

  genFuncDef proxy FuncDef {..} = underScope $ do
    forM_ (_funcArgs ^.. traverse . _1) $ \n -> do
      setEnv (Just True) $ parameters . at n
      l <- getEnv localState
      setEnv (M.delete n l) localState
    prefix <- getEnv currentModuleName
    body <- case _funcExpr of
      Just e -> do
        es <- genExpr proxy e
        let names = genParameterNames [] prefix
            ps = genParameters [] prefix
            stack = "____set_parameters(____make_empty_stack(), "<> names <> "," <> ps <>")"
        return $ "return" <+> parens ("std::experimental::any_cast<func_with_cont_t>(" <> es <> ")" <> parens ("____k, " <> stack <> ", ____effs")) <> semi
      Nothing -> return $ "throw ____cone_exception(\"" <> pretty _funcName <> " is not implemented\");"
    let fn = funcN proxy prefix _funcName
    return $
      vsep
        [ if _funcName `elem` builtinFuncs then emptyDoc
          else "const std::function<object_t" <> genArgTypesInternal ["const cont_t &", "stack_t", "effects_t"] <> ">"
            <+> fn
            <> "= [=]"
            <> genArgsInternal ["const cont_t &____k", "stack_t ____stack", "effects_t ____effs"] prefix
            <> " -> object_t "
            <> braces body
            <> semi,
          "inline py::object" <+> fn <> "_w____" <> genWrapperArgTypes [] prefix
            <> braces ("return ____to_py_object(" <> fn <> genWrapperArgs ["____identity_k", "____make_empty_stack()", "____make_empty_effs()"] prefix <> ")" <> semi)
        ]
    where
      genParameterNames init prefix = encloseSep lbrace rbrace comma $ init ++ (map (\a -> "\"" <> funcN proxy prefix a <> "\"") $ _funcArgs ^.. traverse . _1)
      genParameters init prefix = encloseSep lbrace rbrace comma $ init ++ (map (funcN proxy prefix) $ _funcArgs ^.. traverse . _1)
      genWrapperArgs init prefix = encloseSep lparen rparen comma $ init ++ (map (funcN proxy prefix) $ _funcArgs ^.. traverse . _1)
      genWrapperArgTypes init prefix = encloseSep lparen rparen comma $ init ++ (map (\a -> "const py::object &" <+> funcN proxy prefix a) $ _funcArgs ^.. traverse . _1)
      genArgsInternal init prefix = encloseSep lparen rparen comma $ init ++ (map (\a -> "const object_t &" <+> funcN proxy prefix a) $ _funcArgs ^.. traverse . _1)
      genArgTypesInternal init = encloseSep lparen rparen comma $ init ++ (map (\a -> "const object_t &") $ _funcArgs ^.. traverse . _1)

  genImplFuncDef _ _ = return emptyDoc

  genExpr proxy EVar {..} = do
    prefix <- getEnv currentModuleName
    l <- getEnv $ localState . at (name2String _evarName)
    p <- getEnv $ parameters . at (name2String _evarName)
    let fn = funcN proxy prefix (name2String _evarName)
        fnQ = "\"" <> fn <> "\""
        vn = case l of
          Just _ -> "py::object(py::none())"
          Nothing -> case p of
            Just _ -> fn
            Nothing -> "object_t(" <> fn <> ")"
     in return $
          exprToCps $
            "____k(!____is_none(____lookup_eff(____effs, " <> fnQ <> ")) ? " <> "____lookup_eff(____effs, " <> fnQ <> ") : "
              <+> "(!____is_none(____lookup_var(____stack, " <> fnQ <> ")) ? " <> "____lookup_var(____stack, " <> fnQ <> ") : "
              <+> vn <> "))"
  genExpr proxy ESeq {..} = do
    let e : es = reverse _eseq
    e' <- genExpr proxy e
    foldM
      ( \doc e -> do
          e' <- genExpr proxy e
          return $ exprToCps $ callWithCps e' ("[=](const object_t &____unused) -> object_t" <> braces ("return" <+> callWithCps doc "____k" <> semi))
      )
      e'
      es
  genExpr proxy ELit {..} = do
    lit <- case _litType of
             TPrim Pred _ -> return $ "py::bool_(" <> pretty _lit <> ")"
             TPrim Unit _ -> return $ "py::none()"
             TPrim I8 _ ->   return $ "py::int_(" <> pretty _lit <> ")"
             TPrim I16 _ ->  return $ "py::int_(" <> pretty _lit <> ")"
             TPrim I32 _ -> return $ "py::int_(" <> pretty _lit <> ")"
             TPrim I64 _ -> return $ "py::int_(" <> pretty _lit <> ")"
             TPrim U8 _ ->  return $ "py::int_(" <> pretty _lit <> ")"
             TPrim U16 _ -> return $ "py::int_(" <> pretty _lit <> ")"
             TPrim U32 _ -> return $ "py::int_(" <> pretty _lit <> ")"
             TPrim U64 _ -> return $ "py::int_(" <> pretty _lit <> ")"
             TPrim F16 _ -> return $ "py::float_(" <> pretty _lit <> ")"
             TPrim F32 _ -> return $ "py::float_(" <> pretty _lit <> ")"
             TPrim F64 _ -> return $ "py::float_(" <> pretty _lit <> ")"
             TPrim Str _ -> return $ "py::str(" <> pretty _lit <> ")"
             TPrim Ch _ -> return $ "py::str(\"" <> pretty (read _lit :: Char) <> "\")"
             _ -> throwError $ "unsupported literal type: " ++ ppr _litType
    return $
      exprToCps $
        "____k(py::object(" <> lit <> "))"
  genExpr proxy ELam {..} = underScope $ do
    forM_ (_elamArgs ^.. traverse . _1) $ \n -> do
      setEnv (Just True) $ parameters . at n
      l <- getEnv localState
      setEnv (M.delete n l) localState
    es <- genBody _elamExpr
    return $ parens $ "object_t(func_with_cont_t([=](const cont_t &____k2, stack_t ____stack, effects_t ____effs) -> object_t" <+> braces ("return" <+> es <> semi) <> "))"
    where
    genArgs prefix = encloseSep lparen rparen comma $ "const cont_t &____k" : "stack_t ____stack_unused" : "effects_t ____effs" : (map (\a -> "const object_t &" <> funcN proxy prefix a) $ _elamArgs ^.. traverse . _1)
    genArgTypes = encloseSep lparen rparen comma $ "const cont_t &" : "stack_t" : "effects_t" : (map (\_ -> "const object_t &") $ _elamArgs ^.. traverse . _1)
    genBody e = do
      prefix <- getEnv currentModuleName
      case e of
        Just e -> do
          es <- genExpr proxy e
          return $
            "____k2("
              <> parens (
                      "object_t(std::function<object_t" <> genArgTypes
                        <> ">([=]" <+> genArgs prefix
                        <> " -> object_t "
                        <> braces
                          ( "return "
                              <> parens ("____call_cps_with_cleared_vars" <> callCpsWithclearedVars es prefix)
                              <> semi
                          )
                        <> ")))")
        Nothing -> throwError $ "lambda expected a expression"
    parameterNames prefix = encloseSep lbrace rbrace comma (map (\n -> "\"" <> funcN proxy prefix n <> "\"") $ _elamArgs ^.. traverse . _1)
    parameterValues prefix = encloseSep lbrace rbrace comma (map (funcN proxy prefix) $ _elamArgs ^.. traverse . _1)
    callCpsWithclearedVars es prefix =
      encloseSep lparen rparen comma $
        "____k" : "____stack" : "____effs" : parameterNames prefix : parameterValues prefix : [es]
  genExpr proxy EWhile {..} = do
    c <- genExpr proxy _ewhileCond
    underScope $ do
      es <- genExpr proxy _ewhileBody
      return $ exprToCps $ "____while" <> encloseSep lparen rparen comma ["____k", "____stack", "____effs", c, es]
  genExpr proxy ELet {..} = underScope $ do
    e <- genExpr proxy _eletExpr
    p <- genPatternMatch proxy _eletPattern
    b <- genExpr proxy _eletBody
    return $
      exprToCps $
        callWithCps
          (exprToCps $ callWithCps e ("[=](const object_t &____e) -> object_t {auto ____matched = " <> p <> parens "____e" <>
                              "; if(!py::cast<bool>(____to_py_object(____matched))) throw ____cone_exception(\"let decont_truction failed\"); return ____k(____matched);}"))
          ("[=](const object_t &____unused) -> object_t " <> braces ("return" <+> callWithCps b "____k" <> semi))
  genExpr proxy EAnn {..} = genExpr proxy _eannExpr
  genExpr proxy EApp {..} =
    let fn = name2String $ removeAnn _eappFunc ^. evarName
     in case fn of
          "core/prelude/____add" -> binary "____to_py_object(____lhs) + ____to_py_object(____rhs)"
          "core/prelude/____sub" -> binary "____to_py_object(____lhs) - ____to_py_object(____rhs)"
          "core/prelude/____mul" -> binary "____to_py_object(____lhs) * ____to_py_object(____rhs)"
          "core/prelude/____div" -> binary "____to_py_object(____lhs) / ____to_py_object(____rhs)"
          "core/prelude/____mod" -> binary "____to_py_object(____lhs) % ____to_py_object(____rhs)"
          "core/prelude/____eq" -> binary "py::bool_(____to_py_object(____lhs).attr(\"__eq__\")(____to_py_object(____rhs)))"
          "core/prelude/____ne" -> binary "py::bool_(____to_py_object(____lhs).attr(\"__ne__\")(____to_py_object(____rhs)))"
          "core/prelude/____gt" -> binary "py::bool_(____to_py_object(____lhs) > ____to_py_object(____rhs))"
          "core/prelude/____lt" -> binary "py::bool_(____to_py_object(____lhs) < ____to_py_object(____rhs))"
          "core/prelude/____ge" -> binary "py::bool_(____to_py_object(____lhs) >= ____to_py_object(____rhs))"
          "core/prelude/____le" -> binary "py::bool_(____to_py_object(____lhs) <= ____to_py_object(____rhs))"
          "core/prelude/____and" -> binary "py::bool_(____to_py_object(____lhs) && ____to_py_object(____rhs))"
          "core/prelude/____or" -> binary "py::bool_(____to_py_object(____lhs) || ____to_py_object(____rhs))"
          "core/prelude/____assign" -> do
            prefix <- getEnv currentModuleName
            e <- genExpr proxy (_eappArgs !! 1)
            return $
              exprToCps $
                callWithCps
                  e
                  ( "[=](const object_t &____e) -> object_t {return ____k(____update_stack(____stack, \""
                      <> funcN proxy prefix (name2String (removeAnn (head _eappArgs) ^. evarName))
                      <> "\"," <+> "____e));}"
                  )
          _ -> do
            f <- genExpr proxy _eappFunc
            args <- mapM (genExpr proxy) _eappArgs
            let argNames = map (\i -> "____arg" <> pretty i) [0 .. length _eappArgs - 1]
                argTypes = map (const ", const object_t &") [0 .. length _eappArgs - 1]
                typeArgs = genTypeArgs _eappTypeArgs
            return $
              exprToCps $
                foldl'
                  ( \s (e, n) ->
                      parens $ callWithCps e ("[=](const object_t &" <> n <> ") -> object_t" <> braces ("return " <> s <> semi))
                  )
                  ( "(____set_typeargs(____stack, " <> typeArgs <> "), " <>
                    "std::experimental::any_cast<std::function<object_t(const cont_t &, stack_t, effects_t " <> sep argTypes
                      <> ")>>(____f)"
                      <> encloseSep lparen rparen comma ("____k" : "____stack" : "____effs" : argNames) <> ")"
                  )
                  [(e, n) | e <- reverse $ f : args | n <- reverse $ "____f" : argNames]
    where
      binary :: (Has EnvEff sig m) => String -> m (Doc a)
      binary op = do
        lhs <- genExpr proxy (head _eappArgs)
        rhs <- genExpr proxy (_eappArgs !! 1)
        return $
          exprToCps $
            callWithCps
              lhs
              ( "[=](const object_t &____lhs) -> object_t { return "
                  <> callWithCps rhs ("[=](const object_t &____rhs) -> object_t {return ____k(py::object(" <+> pretty op <+> "));}")
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
            forM_ (_funcArgs intf ^.. traverse . _1) $ \n -> do
              setEnv (Just True) $ parameters . at n
              l <- getEnv localState
              setEnv (M.delete n l) localState
            e <- genExpr proxy (fromJust $ _funcExpr intf)
            let n = funcN proxy prefix $ _funcName intf
                args =
                  encloseSep lparen rparen comma $
                    "const cont_t &____k" :
                    "stack_t ____stack_unused" :
                    "effects_t ____effs" :
                    map (\(n, _) -> "const object_t &" <> funcN proxy prefix n) (_funcArgs intf)
                argTypes =
                  encloseSep lparen rparen comma $
                    "const cont_t &" :
                    "stack_t" :
                    "effects_t" :
                    map (const "const object_t &") (_funcArgs intf)
            return $
              "{\"" <> n <> "\", "
                <+> parens
                  ( "object_t(std::function<object_t" <> argTypes <> ">([=]" <+> args <> " -> object_t "
                      <> braces
                        ("return ____call_with_resumed_k(____k, ____stack, ____effs, " <> e <> ");")
                      <> "))"
                  )
                  <> "}"
        )
        _ehandleBindings
    return $
      exprToCps $
        "____handle(____k, ____stack, ____effs, " <> scope <> comma
          <+> encloseSep lbrace rbrace comma handlers <> ")"
  genExpr proxy ECase {..} = do
    c <- genExpr proxy _ecaseExpr
    pes <- mapM (\pe -> underScope $ (,) <$> genPatternMatch proxy (_casePattern pe) <*> genExpr proxy (_caseExpr pe)) $ _ecaseBody
    let cs = [fst pe | pe <- pes]
        es = [snd pe | pe <- pes]
    return $
      exprToCps $
        "std::experimental::any_cast<func_with_cont_t>(" <> c <> ")"
          <> encloseSep
            lparen
            rparen
            comma
            [ "[=](const object_t &____c) -> object_t { return ____case(____k, ____stack, ____effs, ____c" <> comma
                <+> encloseSep lbrace rbrace comma cs <> comma
                <+> encloseSep lbrace rbrace comma es <> ");}",
              "____stack",
              "____effs"
            ]
  genExpr proxy EAnnMeta {..} = genExpr proxy _eannMetaExpr
  genExpr proxy e = throwError $ "unsupported expression: " ++ ppr e ++ ppr (_eloc e)

  genPatternMatch proxy PVar {..} = do
    setEnv (Just True) $ localState . at (name2String _pvar)
    prefix <- getEnv currentModuleName
    return $
      parens $
        "[=](const object_t &____e) -> object_t {____add_var(____stack, \"" <> funcN proxy prefix (name2String _pvar)
          <> "\""
          <> comma <+> "____e); return py::object(py::bool_(true));}"
  genPatternMatch proxy PExpr {..} = do
    p <- (`callWithCps` "____identity_k") <$> genExpr proxy _pExpr
    return $ parens $ "[=](const object_t &____e) -> object_t { return py::object(py::bool_(____to_py_object(" <+> p <+> ").attr(\"__eq__\")(____to_py_object(____e))));}"
  genPatternMatch proxy PApp {..} = do
    prefix <- getEnv currentModuleName
    bindings <-
      mapM
        ( \(p, ee) -> do
            b <- genPatternMatch proxy p
            return $
              parens $ "py::cast<bool>(____to_py_object(" <> b <> parens ee <> "))"
        )
        [(arg, parens $ "py::object(____to_py_object(____e).attr(\"f" <> pretty id <> "\"))") | arg <- _pappArgs | id <- [0 :: Int ..]]
    return $ parens $ "[=](const object_t &____e) -> object_t { return py::object(py::bool_" <> encloseSep lparen rparen "&&"
                  (("py::isinstance(____to_py_object(____e)" <> comma <+> pythonTypeNamePath (name2String $ _evarName _pappName) <> ")") : bindings) <> ");}"

  genPrologue _ = return emptyDoc

  genEpilogue _ = return emptyDoc

  genModule proxy Module {..} = do
    let modulePs = splitOn "/" _moduleName
    setEnv _moduleName currentModuleName
    pre <- genPrologue proxy
    imps <- mapM (genImport proxy) _imports
    fws <- mapM (genTopFw proxy) _topStmts
    tops <- mapM (genTopStmt proxy) _topStmts
    pos <- genEpilogue proxy
    return $
      vsep $
        [ "#pragma once",
          "#include <iostream>",
          "#include \"cone/builtins.h\"",
          "#include \"cone/data/tensor.h\"",
          "#include \"core/prelude.h\""
        ]
          ++ imps
          ++ [ "namespace py = pybind11;",
               "namespace cone{",
               sep $ map (\n -> "namespace" <+> pretty n <+> lbrace) modulePs
             ]
          ++ [pre]
          ++ fws
          ++ tops
          ++ [pos]
          ++ ["}", sep $ map (const rbrace) modulePs]

-- | Convert a experision to cps
exprToCps :: Doc a -> Doc a
exprToCps e =
  parens $
    "object_t(func_with_cont_t([=](" <+> "const cont_t &____k"
      <> comma <+> "stack_t ____stack"
      <> comma <+> "effects_t ____effs"
      <> ") -> object_t " <+> braces ("return" <+> e <> semi)
      <> "))"

-- | Call a cps function
callWithCps :: Doc a -> Doc a -> Doc a
callWithCps e k = parens $ "std::experimental::any_cast<func_with_cont_t>(" <> e <> ")" <> encloseSep lparen rparen comma ((parens k) : "____stack" : ["____effs"])
