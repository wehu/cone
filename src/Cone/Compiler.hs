{-# LANGUAGE TypeApplications #-}

module Cone.Compiler (compile) where

import Cone.CodeGen.Backend
import Cone.CodeGen.Backend.Cone
import Cone.ModuleLoader
import Control.Monad
import Control.Monad.Except
import Data.Proxy

compile :: [FilePath] -> FilePath -> String -> ExceptT String IO String
compile paths f target = do
  (env, id, m) <- loadModule paths f
  case target of
    "cone" -> return $ show $ gen m (Cone :: (Cone Target))
    _ -> throwError $ "unknown target: " ++ target
