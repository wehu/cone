module Cone.CodeGen.Backend.Cone where

import Cone.CodeGen.Backend
import Cone.Parser.AST
import Prettyprinter

data Cone a = Cone

instance Backend Cone where
  gen proxy m = return $ pretty m