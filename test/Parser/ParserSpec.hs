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
    
    it "module with one import" $ do
       ((parse "" "module foo\\bar; import foo")
          ^._Right.imports ^? ix 0 ^._Just.importPath) `shouldBe` ["foo"]

    it "module with two imports" $ do
       ((parse "" "module foo\\bar; import foo\nimport bar")
          ^._Right.imports ^? ix 1 ^._Just.importPath) `shouldBe` ["bar"]

parserSpec = do
    moduleSpec
