{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Passes.TypeInferSpec where

import Cone.Parser.AST
import Cone.Parser.Parser
import Cone.Passes.TypeInfer
import Control.Lens
import Data.Either
import Data.Text
import NeatInterpolation (text)
import Test.Hspec
import Unbound.Generics.LocallyNameless

inferTypeDefSpec = hspec $ do
  describe "infer type def kinds" $ do
    it "infer " $ do
      let source =
            unpack
              [text|
           module foo\bar
          
          type ff {
            fff
          }

	   type a<b> {
		   c(b, ff)
       c1(b)
     }

     effect a<b,c> {
       fun test(a<b>) : a<b>
       fun test1(b,c) : b
     }

     fun sub[a](a: a, b:a) : a{
       a - b
     }

     fun add[a](a: a, b:a) : a{
       a + b
     }

     fun bar(a: i32) : i32 {
       foo(1 - 2 + 3)
     }

     fun foo[a](a: a) : a {
        fn[c](a:c):c{a}(a:a)
     }

     // xxxx

       |]
      --(show $ fmap (\m -> infer m) $ parse "" source) `shouldBe` ""
      ( fmap
          (\m -> do infer m; return ())
          (parse "" source)
        )
        `shouldBe` (Right $ Right ())

inferTypeSpec = do
  inferTypeDefSpec
