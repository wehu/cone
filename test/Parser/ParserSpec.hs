module Parser.ParserSpec where

import Test.Hspec
import Cone.Parser.Parser
import Cone.Parser.AST
import Data.Either
import Control.Lens

moduleSpec = hspec $ do
  describe "module" $ do
    it "empty module" $ do
       ((parse "" "module foo\\bar")^._Right.moduleName) `shouldBe` ["foo", "bar"]

parserSpec = do
    moduleSpec
