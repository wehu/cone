{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Cone.Packager (installPackage) where

import Cone.Compiler
import Control.Monad
import Data.List
import Data.List.Split
import Data.Text (unpack, pack)
import NeatInterpolation (trimming)
import System.Directory
import System.FilePath
import System.IO.Temp
import System.Process
import System.Exit
import GHC.IO.Exception

setupPy :: String -> String
setupPy pn =
  let package = pack pn
   in unpack [trimming|
from setuptools import setup, find_packages

VERSION = '0.0.1'
DESCRIPTION = '${package}'

# Setting up
setup(
    name="$package",
    version=VERSION,
    author="Cone",
    author_email="<mail@cone.com>",
    description=DESCRIPTION,
    packages=find_packages(),
    install_requires=['numpy', 'immutables'],
    keywords=['python'],
    package_data={'${takeDirectory package}':['*.so', '*.cone']},
    classifiers=[
        "Development Status :: 1 - Planning",
        "Intended Audience :: Developers",
        "Programming Language :: Python :: 3",
        "Operating System :: Unix",
        "Operating System :: MacOS :: MacOS X",
        "Operating System :: Microsoft :: Windows",
    ]
)
    |]

createSetupPy :: FilePath -> FilePath -> IO FilePath
createSetupPy d package = do
  let contents = setupPy package
      fn = d </> "setup.py"
  writeFile fn contents
  return fn

copyPackageFiles :: String -> FilePath -> FilePath -> IO ()
copyPackageFiles target d package = do
  let dstDir = d </> takeDirectory package
  userDir <- (</> target) <$> coneUserDataDir
  createDirectoryIfMissing True dstDir
  forM_ [".py", "____t.py", "____c.so", ".cone"] $ \f ->
    copyFile (userDir </> package ++ f) (d </> package ++ f)
  copyFile (userDir </> takeDirectory package </> "__init__.py") (d </> takeDirectory package </> "__init__.py")

installPackage :: String -> FilePath -> IO ()
installPackage target fn = do
  let package = dropExtension fn
  withSystemTempDirectory "cone" $ \d -> do
    putStrLn d
    when (target == "python") $ do
      fn <- createSetupPy d package
      copyPackageFiles target d package
      ec <- runProcess target [fn, "bdist"] (Just d) Nothing Nothing Nothing Nothing >>= waitForProcess
      when (ec /= ExitSuccess) $ exitWith ec
      ec <- runProcess target [fn, "install", "--user"] (Just d) Nothing Nothing Nothing Nothing >>= waitForProcess
      when (ec /= ExitSuccess) $ exitWith ec 