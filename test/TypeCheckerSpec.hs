{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module TypeCheckerSpec where

import Cone.Parser.AST
import Cone.Parser.Parser
import Cone.TypeChecker
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

     type ____add<a, a>

     effect a<b> {
       fun test(a<b>) : a<b>
     }
     
     type tensor<a,s> {
       tensor
     }

     type ____pair<a, b>

     fun inline_python<b>(c:str) : b 

     type max<a, a>

     fun typeTest<i,j, k>() : tensor<i32, [i+1, j+2, k+3]>

     fun runTypeTest(a:tensor<i32, [1, 2, ?]>) : tensor<i32, [2, 4, ?]> {
       tensor<i32, [1, 2, max<4, 3>]>
      case tensor<i32, [1, 2, 4]> {
        tensor<i32, [1, 2, 4]> -> {1}
        tensor<i32, [1, 2, 4]> -> {2}
      }
       typeTest<1, 2, ?>()
     }


     fun ____sub<a>(a: a, b:a) : a {
       inline_python<a>("aaa")
     }

     fun ____add<a>(a: a, b:a) : a

     impl fun ____add(a: i32, b: i32) : i32 {
       a + b
     }

     fun ____assign<a>(a:a, a:a) : a

     fun bar(a: i32) : i32 {
       
      case c1(1) {
        c(b, ff) -> {b}
        c1(b) -> {b}
      }
      var c(c2(c1(e), f), d) = c(c2(c1(1), fff), fff)
      foo(1 - 3 + e)
      var c(c2(c1(e1), f1), d1) = c(c2(c1(1), fff), fff)

      e1 = e1 + 1

      case a+1 {
        2 -> {a}
        3 -> {a}
      }

      while true {
        1}
        
      if true {1} else {2}

     }

     fun foo<a>(a: a) : a {
        fn<c>(a:c):c{a}(a:a)
     }

      fun zzz<a1>(a:a<a1>, b:tensor<i32, [2, 4]>, c:tensor<i32, [4,6]>) : i32 {


      [a[i, j] += b[i, k] * c[k, j]] : tensor<i32, [2, 6]>
      var c = 2
        handle a<a1> {
          test<i32>(c1(1))
          3
        } with {
          fun test<b>(a: a<b>) : a<b> {
            c
            a
          }
        }
        1
      }

      fun test2<a, b>(a: (a)->b, b : a) : b {
        a(b)
      }

      fun test3<a>(c:i32) : (i32) -> i32 {
        var a = 1
        fn<b>(b:i32): i32{ c }
        a = a+1
        fn<b>(b:i32): i32{ c }
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

