{-# LANGUAGE TypeApplications #-}

module Cone.CodeGen.Compiler (compile) where

import Cone.CodeGen.Backend
import Cone.CodeGen.Backend.Cone
import Cone.CodeGen.ModuleLoader
import Control.Monad
import Control.Monad.Except
import Data.Proxy

compile :: [FilePath] -> FilePath -> String -> IO (Either String String)
compile paths f target = do
  res <- runExceptT $ loadModule paths f
  case res of
    Left e -> return $ Left e
    Right (env, id, m) -> do
            let output = case target of
                           "cone" -> Right $ show $ gen m (Cone::(Cone Target))
                           _ -> Left $ "unknown target: " ++ target
            return output