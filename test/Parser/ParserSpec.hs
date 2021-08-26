{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Parser.ParserSpec where

import Test.Hspec
import Cone.Parser.Parser
import Cone.Parser.AST
import Data.Either
import Data.Text
import Control.Lens
import NeatInterpolation (text)

moduleSpec = hspec $ do
  describe "module syntax" $ do
    it "empty module" $ do
       let source = unpack [text|
           module foo\bar
       |]
       ((parse "" source)^._Right.moduleName) `shouldBe` ["foo", "bar"]
    
    it "module with one import" $ do
       let source = unpack [text|
           module foo\bar
	   import foo
       |]
       ((parse "" source)
          ^._Right.imports ^? ix 0 ^._Just.importPath) `shouldBe` ["foo"]

    it "module with two imports" $ do
       let source = unpack [text|
           module foo\bar;
	   import foo
	   import bar;
       |]
       ((parse "" source)
          ^._Right.imports ^? ix 1 ^._Just.importPath) `shouldBe` ["bar"]

    it "module with import alias" $ do
       let source = unpack [text|
           module foo\bar
	   import foo as f
	   import bar\baz
       |]
       ((parse "" source)
          ^._Right.imports ^? ix 0 ^._Just.importAlias) `shouldBe` (Just "f")

parserSpec = do
    moduleSpec
