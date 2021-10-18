module Cone.CodeGen.Backend.Cone where

import Cone.CodeGen.Backend
import Cone.Parser.AST
import Prettyprinter

data Cone a = Cone

instance Backend Cone where
  gen proxy m = return $ pretty m

  namePath _ _ = emptyDoc

  typeN _ _ _ = emptyDoc

  funcN _ _ _ = emptyDoc

  genImport _ _ = return emptyDoc

  genTypeDef _ _ = return emptyDoc

  genTypeCon _ _ _ = return emptyDoc

  genEffectDef _ _ = return emptyDoc

  genFuncDef _ _ = return emptyDoc

  genExpr _ _ = return emptyDoc

  genPatternMatch _ _ _ = return emptyDoc

  genPrologue _ = return emptyDoc

  genEpilogue _ = return emptyDoc

  genModule _ _ = return emptyDoc
