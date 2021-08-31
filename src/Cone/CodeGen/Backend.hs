{-# LANGUAGE EmptyDataDecls #-}

module Cone.CodeGen.Backend where

import Data.Proxy
import Cone.Parser.AST
import Prettyprinter

data Target

class Backend t where
  gen :: Module -> t Target -> Doc b