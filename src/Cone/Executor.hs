module Cone.Executor where

import Cone.Compiler (coneUserDataDir)
import Control.Monad
import Data.List
import Data.List.Split
import System.Environment
import System.FilePath
import System.Process
import System.Exit

runCode :: FilePath -> [String] -> String -> FilePath -> IO String
runCode exe args input fn =
  if exe == "python"
    then do
      userDataDir <- coneUserDataDir
      path <- lookupEnv "PYTHONPATH"
      case path of
        Just path -> setEnv "PYTHONPATH" $ (userDataDir </> "python") ++ ";" ++ path
        Nothing -> setEnv "PYTHONPATH" (userDataDir </> "python")
      runC "." (args ++ ["-m", join $ intersperse "." $ splitOn "/" $ dropExtension fn])
      return ""
    else return ""
  where runC d args = do
          ec <- runProcess exe args (Just d) Nothing Nothing Nothing Nothing >>= waitForProcess
          when (ec /= ExitSuccess) $ exitWith ec
