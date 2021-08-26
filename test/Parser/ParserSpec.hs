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

    it "module with fun definition" $ do
       let source = unpack [text|
           module foo\bar
	   import foo

	   fun aaa(a : b) : c {
		   a
	   }
       |]
       --(show $ parse "" source) `shouldBe` ""
       ((parse "" source)
          ^._Right.topStmts ^? ix 0 ^._Just._FDef.funcName) `shouldBe` "aaa"

typeSpec = hspec $ do
  describe "type syntax" $ do
    it "app type" $ do
       let source = unpack [text|
           module foo

	   fun a(a : a<b>) : c {
		   a
	   }
       |]
       --(show $ parse "" source) `shouldBe` "a"
       ((parse "" source)
           ^._Right.topStmts ^? ix 0 ^._Just._FDef.funcArgs
           ^? ix 0 ^._Just._2.tappArgs
           ^? ix 0 ^._Just.tvar) `shouldBe` "b"

    it "func type" $ do
       let source = unpack [text|
           module foo

	   fun a(a : (a<b>) -> e c) : c {
		   a
	   }
       |]
       --(show $ parse "" source) `shouldBe` "a"
       ((parse "" source)
           ^._Right.topStmts ^? ix 0 ^._Just._FDef.funcArgs
           ^? ix 0 ^._Just._2.tfuncResult.tvar) `shouldBe` "c"

    it "type annotation" $ do
       let source = unpack [text|
           module foo

	   fun a(a : (c: *)) : c {
		   a
	   }
       |]
       --(show $ parse "" source) `shouldBe` "a"
       ((parse "" source)
           ^._Right.topStmts ^? ix 0 ^._Just._FDef.funcArgs
           ^? ix 0 ^._Just._2.tannType.tvar) `shouldBe` "c"


    it "func kind" $ do
       let source = unpack [text|
           module foo

	   fun a(a : (c: (*, *) -> *)) : c {
		   a
	   }
       |]
       --(show $ parse "" source) `shouldBe` "a"
       ((parse "xxx" source)
           ^._Right.topStmts ^? ix 0 ^._Just._FDef.funcArgs
           ^? ix 0 ^._Just._2
           .tannKind.kfuncResult.kloc.fileName) `shouldBe` "xxx"


parserSpec = do
    moduleSpec
    typeSpec
