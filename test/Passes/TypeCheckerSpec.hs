{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Passes.TypeCheckerSpec where

import Cone.Parser.AST
import Cone.Parser.Parser
import Cone.Passes.TypeChecker
import Control.Lens
import Data.Either
import Data.Text
import NeatInterpolation (text)
import Test.Hspec
import Unbound.Generics.LocallyNameless

typeCheckerSpec = hspec $ do
  describe "infer type def kinds" $ do
    it "infer " $ do
      let source =
            unpack
              [text|
           module foo/bar
          
          type ff {
            fff
          }

	   type a<b> {
		   c(b, ff)
       c1(b)
       c2(a<b>, ff)
     }

     effect a<b> {
       fun test(a<b>) : a<b>
     }

     fun sub[a](a: a, b:a) : a

     fun add[a](a: a, b:a) : a

     impl fun add(a: i32, b: i32) : i32 {
       a + b
     }

     fun bar(a: i32) : i32 {
       
      case c1(1) {
        c(b, ff) -> {b}
        c1(b) -> {b}
     }
      var c(c2(c1(e), f), d) = c(c2(c1(1), fff), fff)
      foo(1 - 3 + e)
      var c(c2(c1(e1), f1), d1) = c(c2(c1(1), fff), fff)

      case a {
        2 -> {a}
        3 -> {a}
      }

      while true {
        1}

      if true {1} else {2}

     }

     fun foo[a](a: a) : a {
        fn[c](a:c):c{a}(a:a)
     }

      fun zzz[a1](a:a<a1>) : i32 {
        handle a<a1> {
          test(a)
          3
        } with {
          fun test(a: a<a1>) : a<a1> {
            a
          }
        }
        1
      }

     // xxxx

       |]
      -- (show $ fmap (\m -> initModule m initialEnv 0) $ parse "" source) `shouldBe` ""
      ( fmap
          (\m -> do
            let (Right (env, (id, _))) = initModule m initialEnv 0
            checkType m env id; return ())
          (parse "" source)
        )
        `shouldBe` (Right $ Right ())

