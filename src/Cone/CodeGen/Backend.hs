{-# LANGUAGE EmptyDataDecls #-}

module Cone.CodeGen.Backend where

import Cone.Parser.AST
import Data.Proxy
import Prettyprinter

data Target

class Backend t where
  gen :: Module -> t Target -> Doc b
