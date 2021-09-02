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

     type ____add<a, a>{}

     effect a<b> {
       fun test(a<b>) : a<b>
     }
     
     type ccc<a> {
       ccc
     }

     fun typeTest[a](a:ccc<a>) : ccc<a+1>

     fun runTypeTest(a:ccc<1>) : ccc<2> {
       typeTest(a)
     }

     fun ____sub[a](a: a, b:a) : a

     fun ____add[a](a: a, b:a) : a

     impl fun ____add(a: i32, b: i32) : i32 {
       a + b
     }

     fun ____assign[a](a:a, a:a) : a

     fun bar(a: i32) : i32 {
       
      case c1(1) {
        c(b, ff) -> {b}
        c1(b) -> {b}
     }
      var c(c2(c1(e), f), d) = c(c2(c1(1), fff), fff)
      foo(1 - 3 + e)
      var c(c2(c1(e1), f1), d1) = c(c2(c1(1), fff), fff)

      e1 = e1 + 1

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
          test(c1(1))
          3
        } with {
          fun test(a: a<i32>) : a<i32> {
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

