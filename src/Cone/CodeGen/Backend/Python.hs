module Cone.CodeGen.Backend.Python where

import Cone.CodeGen.Backend
import Cone.Parser.AST
import Prettyprinter

data Python a = Python

instance Backend Python where