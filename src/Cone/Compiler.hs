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
    "cone" -> case gen (Cone :: (Cone Target)) m of
                Left err -> throwError err
                Right doc -> return $ show doc
    "python" -> case gen (Python :: (Python Target)) m of
                  Left err -> throwError err
                  Right doc -> return $ show doc
    _ -> throwError $ "unknown target: " ++ target
