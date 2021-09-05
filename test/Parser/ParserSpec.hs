{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Parser.ParserSpec where

import Cone.Parser.AST
import Cone.Parser.Parser
import Control.Lens
import Data.Either
import Data.Text
import NeatInterpolation (text)
import Test.Hspec
import Unbound.Generics.LocallyNameless

moduleSpec = hspec $ do
  describe "module syntax" $ do
    it "empty module" $ do
      let source =
            unpack
              [text|
           module foo/bar
       |]
      ((parse "" source) ^. _Right . moduleName) `shouldBe` "foo/bar"

    it "module with one import" $ do
      let source =
            unpack
              [text|
           module foo/bar
	   import foo
       |]
      ( (parse "" source)
          ^. _Right . imports ^? ix 0
          ^. _Just . importPath
        )
        `shouldBe` "foo"

    it "module with two imports" $ do
      let source =
            unpack
              [text|
           module foo/bar;
	   import foo
	   import bar;
       |]
      ( (parse "" source)
          ^. _Right . imports ^? ix 1
          ^. _Just . importPath
        )
        `shouldBe` "bar"

    it "module with import alias" $ do
      let source =
            unpack
              [text|
           module foo/bar
	   import foo as f
	   import bar/baz
       |]
      ( (parse "" source)
          ^. _Right . imports ^? ix 0
          ^. _Just . importAlias
        )
        `shouldBe` (Just "f")

    it "module with fun definition" $ do
      let source =
            unpack
              [text|
           module foo/bar
	   import foo

	   fun aaa(a : b) : c {
		   a
	   }
       |]
      --(show $ parse "" source) `shouldBe` ""
      ( (parse "" source)
          ^. _Right . topStmts ^? ix 0
          ^. _Just . _FDef . funcName
        )
        `shouldBe` "aaa"

typeSpec = hspec $ do
  describe "type syntax" $ do
    it "app type" $ do
      let source =
            unpack
              [text|
           module foo

	   fun a(a : a<b>) : c {
		   a
	   }
       |]
      --(show $ parse "" source) `shouldBe` "a"
      ( name2String $
          (parse "" source)
            ^. _Right . topStmts
            ^? ix 0
            ^. _Just . _FDef . funcArgs
            ^? ix 0
            ^. _Just . _2 . tappArgs
            ^? ix 0
            ^. _Just . tvar
        )
        `shouldBe` "b"

    it "func type" $ do
      let source =
            unpack
              [text|
           module foo

	   fun a(a : (a<b>) -> e c) : c {
		   a
	   }
       |]
      --(show $ parse "" source) `shouldBe` "a"
      ( name2String $
          (parse "" source)
            ^. _Right . topStmts
            ^? ix 0
            ^. _Just . _FDef . funcArgs
            ^? ix 0
            ^. _Just . _2 . tfuncResult . tvar
        )
        `shouldBe` "c"

    it "type annotation" $ do
      let source =
            unpack
              [text|
           module foo

	   fun a(a : (c: *)) : c {
		   a
	   }
       |]
      --(show $ parse "" source) `shouldBe` "a"
      ( name2String $
          (parse "" source)
            ^. _Right . topStmts
            ^? ix 0
            ^. _Just . _FDef . funcArgs
            ^? ix 0
            ^. _Just . _2 . tannType . tvar
        )
        `shouldBe` "c"

    it "func kind" $ do
      let source =
            unpack
              [text|
           module foo

	   fun a(a : (c: (*, *) -> *)) : c {
		   a
	   }
       |]
      --(show $ parse "" source) `shouldBe` "a"
      ( (parse "xxx" source)
          ^. _Right . topStmts
          ^? ix 0
          ^. _Just . _FDef . funcArgs
          ^? ix 0
          ^. _Just . _2 
            . tannKind
            . kfuncResult
            . kloc
            . fileName
        )
        `shouldBe` "xxx"

    it "eff app" $ do
      let source =
            unpack
              [text|
           module foo

	   fun a(a : (c) -> e<c> d, b : f32) : c {
		   a
	   }
       |]
      --(show $ parse "" source) `shouldBe` "a"
      ( name2String $
          (parse "xxx" source)
            ^. _Right . topStmts
            ^? ix 0
            ^. _Just . _FDef . funcArgs
            ^? ix 0
            ^. _Just . _2 . tfuncEff . effAppArgs
            ^? ix 0
            ^. _Just . tvar
        )
        `shouldBe` "c"

    it "eff list" $ do
      let source =
            unpack
              [text|
           module foo

	   fun a(a : (c) -> [e1<d>, e<c>] d) : f16 {
		   a
	   }
       |]
      --(show $ parse "" source) `shouldBe` "a"
      ( name2String $
          (parse "xxx" source)
            ^. _Right . topStmts
            ^? ix 0
            ^. _Just . _FDef . funcArgs
            ^? ix 0
            ^. _Just . _2 . tfuncEff . effList
            ^? ix 1
            ^. _Just . effAppArgs
            ^? ix 0
            ^. _Just . tvar
        )
        `shouldBe` "c"

    it "eff kind" $ do
      let source =
            unpack
              [text|
           module foo

	   fun a(a : (i8) -> [e1<d>, e<c> : *] d) : i32 {
		   a
	   }
       |]
      --(show $ parse "" source) `shouldBe` "a"
      ( name2String $
          (parse "xxx" source)
            ^. _Right . topStmts
            ^? ix 0
            ^. _Just . _FDef . funcArgs
            ^? ix 0
            ^. _Just . _2 . tfuncEff . effList
            ^? ix 1
            ^. _Just . effAnnType . effAppArgs
            ^? ix 0
            ^. _Just . tvar
        )
        `shouldBe` "c"

exprSpec = hspec $ do
  describe "expr syntax" $ do
    it "expr app" $ do
      let source =
            unpack
              [text|
           module foo

	   fun a(a : a<b>) : c {
		   foo(a, a)
	   }
       |]
      --(show $ parse "" source) `shouldBe` "a"
      ( (parse "" source)
          ^. _Right . topStmts ^? ix 0
          ^. _Just . _FDef . funcExpr
            . _Just
            . eappFunc
            . evarName
        )
        `shouldBe` "foo"

    it "expr lambda" $ do
      let source =
            unpack
              [text|
           module foo

	   fun a(a : \
        a<b>) : c {
		   fn(arg:a):a {a} \
	   }
       |]
      --(show $ parse "" source) `shouldBe` "a"
      ( (parse "" source)
          ^. _Right . topStmts
          ^? ix 0
          ^. _Just . _FDef . funcExpr . _Just . elamArgs
          ^? ix 0
          ^. _Just . _1
        )
        `shouldBe` "arg"

typeDefSpec = hspec $ do
  describe "type definition syntax" $ do
    it "type def with one construct" $ do
      let source =
            unpack
              [text|
           module foo

	   type tt<b> {a(b)
       }
       |]
      --(show $ parse "" source) `shouldBe` "a"
      ( (parse "" source)
          ^. _Right . topStmts ^? ix 0
          ^. _Just . _TDef . typeName
        )
        `shouldBe` "tt"

effectDefSpec = hspec $ do
  describe "effect definition syntax" $ do
    it "effect def with one intf" $ do
      let source =
            unpack
              [text|
           module foo

	   effect ee <b> {
           fun a(b) : b
       }
       |]
      --(show $ parse "" source) `shouldBe` "a"
      ( (parse "" source)
          ^. _Right . topStmts ^? ix 0
          ^. _Just . _EDef . effectName
        )
        `shouldBe` "ee"

parserSpec = do
  moduleSpec
  typeSpec
  exprSpec
  typeDefSpec
  effectDefSpec
