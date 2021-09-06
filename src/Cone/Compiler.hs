{-# LANGUAGE TypeApplications #-}

module Cone.Compiler (compile) where

import Cone.CodeGen.Backend
import Cone.CodeGen.Backend.Cone
import Cone.CodeGen.Backend.Python
import Cone.ModuleLoader
import Control.Monad
import Control.Monad.Except
import Data.Proxy

-- | Compile a file
compile :: [FilePath] -> FilePath -> String -> ExceptT String IO String
compile paths f target = do
  (env, id, m) <- loadModule paths f
  case target of
    "cone" -> return $ show $ gen (Cone :: (Cone Target)) m
    "python" -> return $ show $ gen (Python :: (Python Target)) m
    _ -> throwError $ "unknown target: " ++ target
