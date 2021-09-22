module Cone.Executor where

import System.Process
import System.Environment
import System.FilePath
import Data.List.Split
import Data.List
import Control.Monad
import Cone.Compiler (coneUserDataDir)

runCode :: FilePath -> [String] -> String -> FilePath -> IO String
runCode exe args input fn =
  if exe == "python" then do
    userDataDir <- coneUserDataDir
    path <- lookupEnv "PYTHONPATH"
    case path of
     Just path -> setEnv "PYTHONPATH" $ (userDataDir </> "python") ++ ";" ++ path
     Nothing -> setEnv "PYTHONPATH" $ (userDataDir </> "python")
    readProcess exe (args ++ ["-m", join $ intersperse "." $ splitOn "/" fn]) ""
  else return ""