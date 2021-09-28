module Cone.Executor where

import Cone.Compiler (coneUserDataDir)
import Control.Monad
import Data.List
import Data.List.Split
import System.Environment
import System.FilePath
import System.Process

runCode :: FilePath -> [String] -> String -> FilePath -> IO String
runCode exe args input fn =
  if exe == "python"
    then do
      userDataDir <- coneUserDataDir
      path <- lookupEnv "PYTHONPATH"
      case path of
        Just path -> setEnv "PYTHONPATH" $ (userDataDir </> "python") ++ ";" ++ path
        Nothing -> setEnv "PYTHONPATH" (userDataDir </> "python")
      readProcess exe (args ++ ["-m", join $ intersperse "." $ splitOn "/" $ dropExtension fn]) ""
    else return ""
