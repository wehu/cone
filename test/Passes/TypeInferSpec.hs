{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Passes.TypeInferSpec where

import Test.Hspec
import Cone.Parser.Parser
import Cone.Parser.AST
import Cone.Passes.TypeInfer
import Data.Either
import Data.Text
import Control.Lens
import NeatInterpolation (text)
import Unbound.Generics.LocallyNameless

inferTypeDefSpec = hspec $ do
  describe "infer type def kinds" $ do
    it "infer " $ do
       let source = unpack [text|
           module foo\bar

	   type a<b> {
		   c(b, a<b>)
     }

     effect a<b> {
       fun test(a<b>) : a<b>
     }

       |]
       --(show $ fmap (\m -> infer m) $ parse "" source) `shouldBe` ""
       (fmap (\m -> do infer m; return ())
          (parse "" source)) `shouldBe` (Right $ Right ())

inferTypeSpec = do
  inferTypeDefSpec