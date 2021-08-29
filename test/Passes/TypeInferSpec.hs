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

     fun bar(a: a<i32>) : a<i32> {
       foo(a)
     }

     fun foo[b](a: a<b>) : a<b> {
        fn[a](a:a){a}(a)
     }

       |]
      --(show $ fmap (\m -> infer m) $ parse "" source) `shouldBe` ""
      ( fmap
          (\m -> do infer m; return ())
          (parse "" source)
        )
        `shouldBe` (Right $ Right ())

inferTypeSpec = do
  inferTypeDefSpec
