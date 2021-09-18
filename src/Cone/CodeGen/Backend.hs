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

module Cone.CodeGen.Backend where

import Cone.Parser.AST
import Control.Carrier.Error.Either
import Control.Carrier.Fresh.Strict
import Control.Carrier.State.Strict
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

type Eff s e = Fresh :+: State s :+: Error e

data Env = Env
  { _currentModuleName :: String
  }

makeLenses ''Env

initialEnv =
  Env
    { _currentModuleName = ""
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

-- | Targe proxy
data Target

-- | Backend interfaces
class Backend t where
  -- | Generate a module
  gen :: t Target -> Module -> Either String (Doc a)
  gen proxy m = do
    (env, (id, doc)) <- run . runError . (runState initialEnv) . runFresh 0 $ genModule proxy m
    return doc

  namePath :: t Target -> String -> Doc a
  namePath proxy n = pretty $ join $ intersperse "." $ splitOn "/" n

  typeN :: t Target -> String -> String -> Doc a
  typeN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == (take prefixLen n') then (drop (prefixLen + 1) n') else n'
        ns = splitOn "/" n
        ps = init ns
        tn = "Cone__" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [tn]

  funcN :: t Target -> String -> String -> Doc a
  funcN proxy prefix n' =
    let prefixLen = length prefix
        n = if prefix == (take prefixLen n') then (drop (prefixLen + 1) n') else n'
        ns = splitOn "/" n
        ps = init ns
        fn = "cone__" ++ last ns
     in pretty $ join $ intersperse "." $ ps ++ [fn]

  genImport :: (Has EnvEff sig m) => t Target -> ImportStmt -> m (Doc a)
  genImport proxy ImportStmt {..} =
    return $
      ( -- case _importAlias of
        --  Just a -> "import" <+> namePath proxy _importPath <+> "as" <+> pretty a
        --  Nothing ->
        "import" <+> namePath proxy _importPath
      )
        <+> line

  genTypeDef :: (Has EnvEff sig m) => t Target -> TypeDef -> m (Doc a)
  genTypeDef proxy TypeDef {..} = do
    cons <- mapM (genTypeCon proxy _typeName) _typeCons
    return $
      vsep $ {-["class" <+> typeN proxy _typeName <> ":"
             ,indent 4 "pass" <+> line
             ] ++-}
        cons

  genTypeCon :: (Has EnvEff sig m) => t Target -> String -> TypeCon -> m (Doc a)
  genTypeCon proxy ptn TypeCon {..} = do
    prefix <- getEnv currentModuleName
    let tn = typeN proxy prefix _typeConName
        fn = funcN proxy prefix _typeConName
     in return $
          vsep
            [ "class" <+> tn {- <> parens (typeN proxy ptn) -} <> ":",
              indent 4 constructor,
              indent 4 hash,
              indent 4 $ eq tn,
              ctrFunc fn tn,
              ctrFuncWrapper fn <+> line
            ]
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
        if _typeConArgs == []
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
      ctrFunc fn tn =
        vsep
          [ "def" <+> fn <> genArgs ["____k", "____state", "____effs"] <> ":",
            indent 4 ("return" <+> ("____k" <> parens (tn <> genArgs ["____k", "____state", "____effs"])))
          ]
      ctrFuncWrapper fn =
        vsep
          [ "def" <+> fn <> "_w" <> genArgs [] <> ":",
            indent 4 ("return" <+> (fn <> genArgs ["lambda x:x", "[{}]", "[]"]))
          ]

  genEffectDef :: (Has EnvEff sig m) => t Target -> EffectDef -> m (Doc a)
  genEffectDef proxy e = return emptyDoc

  genFuncDef :: (Has EnvEff sig m) => t Target -> FuncDef -> m (Doc a)
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

  genExpr :: (Has EnvEff sig m) => t Target -> Expr -> m (Doc a)
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
          "core/prelude/add" -> binary "+"
          "core/prelude/sub" -> binary "-"
          "core/prelude/mul" -> binary "*"
          "core/prelude/div" -> binary "/"
          "core/prelude/mod" -> binary "%"
          "core/prelude/eq" -> binary "=="
          "core/prelude/ne" -> binary "!="
          "core/prelude/gt" -> binary ">"
          "core/prelude/lt" -> binary "<"
          "core/prelude/ge" -> binary ">="
          "core/prelude/le" -> binary "<="
          "core/prelude/and" -> binary "and"
          "core/prelude/or" -> binary "or"
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

  genPatternMatch :: (Has EnvEff sig m) => t Target -> Pattern -> m (Doc a)
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

  genPrologue :: (Has EnvEff sig m) => t Target -> m (Doc a)
  genPrologue proxy = do
    prefix <- getEnv currentModuleName
    return $
      vsep
        [ "def " <> funcN proxy prefix "print(k, s, effs, a):",
          indent 4 $ vsep ["return k(print(a))"],
          "def ____lookup_var(state, k):",
          indent 4 $
            vsep
              [ "for s in reversed(state):",
                indent 4 $
                  vsep
                    [ "if k in s:",
                      indent 4 $ vsep ["return s[k]"]
                    ]
              ],
          indent 4 $ "return None",
          "def ____lookup_eff(effs, k):",
          indent 4 $
            vsep
              [ "for s in reversed(effs):",
                indent 4 $
                  vsep
                    [ "if k in s:",
                      indent 4 $ vsep ["return s[k]"]
                    ]
              ],
          indent 4 $ "return None",
          "def ____add_var(state, k, v):",
          indent 4 $ "state[-1][k] = v",
          "def ____update_state(state, k, v):",
          indent 4 $
            vsep
              [ "for s in reversed(state):",
                indent 4 $
                  vsep
                    [ "if k in s:",
                      indent 4 $
                        vsep
                          [ "s[k] = v",
                            "return"
                          ]
                    ]
              ],
          "def ____call_cps_with_cleared_vars(k, state, effs, ks, e):",
          indent 4 $
            vsep
              [ "state = copy.deepcopy(state)",
                "effs = []",
                "for s in state:",
                indent 4 $
                  vsep
                    [ "for k_ in ks:",
                      indent 4 $
                        vsep
                          [ "if k_ in s:",
                            indent 4 "del s[k_]"
                          ]
                    ],
                "return e(k, state, effs)"
              ],
          "def ____while(k, state, effs, cond, body):",
          indent 4 $
            vsep
              [ "state.append({})",
                "def k3(o):",
                indent 4 $
                  vsep
                    [ "del state[-1]",
                      "cond(k2, state, effs)"
                    ],
                "def k2(o):",
                indent 4 $
                  vsep
                    [ "if o:",
                      indent 4 $
                        vsep
                          [ "state.append({})",
                            "body(k3, state, effs)"
                          ],
                      "else:",
                      indent 4 $
                        vsep
                          [ "k(o)"
                          ]
                    ],
                "return cond(k2, state, effs)"
              ],
          "def ____case(k, state, effs, ce, conds, exprs):",
          indent 4 $
            vsep
              [ "for (p, e) in zip(conds, exprs):",
                indent 4 $
                  vsep
                    [ "state.append({})",
                      "def k2(o):",
                      indent 4 $
                        vsep
                          [ "del state[-1]",
                            "return k(o)"
                          ],
                      "if p(ce):",
                      indent 4 $ vsep ["return e(k2, state, effs)"],
                      "del state[-1]"
                    ]
              ],
          "def ____handle(k, state, effs, scope, handlers):",
          indent 4 $
            vsep
              [ "state.append({})",
                "effs.append({})",
                "try:",
                indent 4 $
                  vsep
                    [ "effs[-1].update(handlers)",
                      "o = scope(lambda x: x, state, effs)"
                    ],
                "finally:",
                indent 4 $ vsep ["del state[-1]", "del effs[-1]"],
                "return k(o)"
              ],
          "def ____call_with_resumed_k(k, state, effs, handler):",
          indent 4 $
            vsep
              [ "state.append({})",
                "state[-1]['____resumed_k'] = k",
                "try:",
                indent 4 $ vsep ["o = handler(lambda x: x, state, effs)"],
                "finally:",
                indent 4 $ "del state[-1]",
                "return o"
              ],
          "def " <> funcN proxy prefix "resume(k, s, effs, a):",
          indent 4 $ vsep ["return k(s[-1]['____resumed_k'](a))"],
          "unit = None",
          "true = True",
          "false = False"
        ]

  genEpilogue :: (Has EnvEff sig m) => t Target -> m (Doc a)
  genEpilogue proxy = do
    prefix <- getEnv currentModuleName
    return $
      vsep
        [ "if __name__ == \"__main__\":",
          indent 4 $ funcN proxy prefix "main_w()" <+> line
        ]

-- | Convert a experision to cps
exprToCps :: Doc a -> Doc a
exprToCps e = parens $ "lambda" <+> "____k" <> comma <+> "____state" <> comma <+> "____effs" <> colon <+> e

-- | Call a cps function
callWithCps :: Doc a -> Doc a -> Doc a
callWithCps e k = parens $ e <> (encloseSep lparen rparen comma $ (parens k) : "____state" : ["____effs"])

genImplFuncDef :: (Has EnvEff sig m) => Backend t => t Target -> ImplFuncDef -> m (Doc a)
genImplFuncDef proxy ImplFuncDef {..} = genFuncDef proxy _implFunDef

genModule :: (Has EnvEff sig m) => Backend t => t Target -> Module -> m (Doc a)
genModule proxy Module {..} = do
  setEnv _moduleName currentModuleName
  pre <- genPrologue proxy
  imps <- mapM (genImport proxy) _imports
  tops <- mapM (genTopStmt proxy) _topStmts
  pos <- genEpilogue proxy
  return $
    vsep $
      -- [ "module" <+> namePath proxy _moduleName <+> line]
      [ "import core.prelude",
        "import copy"
      ]
        ++ imps
        ++ [pre]
        ++ tops
        ++ [pos]

genTopStmt :: (Has EnvEff sig m) => Backend t => t Target -> TopStmt -> m (Doc a)
genTopStmt proxy TDef {..} = genTypeDef proxy _tdef
genTopStmt proxy EDef {..} = genEffectDef proxy _edef
genTopStmt proxy FDef {..} = genFuncDef proxy _fdef
genTopStmt proxy ImplFDef {..} = genImplFuncDef proxy _implFdef
