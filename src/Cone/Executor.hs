module Cone.Executor where

import System.Process
import System.Environment
import System.FilePath
import Cone.Compiler (coneUserDataDir)

runCode :: FilePath -> [String] -> String -> IO String
runCode exe args input = do
  userDataDir <- coneUserDataDir
  path <- lookupEnv "PYTHONPATH"
  case path of
   Just path -> setEnv "PYTHONPATH" $ (userDataDir </> "python") ++ ";" ++ path
   Nothing -> setEnv "PYTHONPATH" $ (userDataDir </> "python")
  readProcess exe args input