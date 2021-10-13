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

setupPy :: String -> String
setupPy pn =
  let ps = splitOn "/" pn
      package = pack $ join (intersperse "." (if length ps <= 1 then ps else init ps))
      dir = pack $ if length ps <= 1 then pn else takeDirectory pn
   in unpack [trimming|
from setuptools import setup, find_packages

VERSION = '0.0.1'
DESCRIPTION = '${package}'

# Setting up
setup(
    name="$package",
    version=VERSION,
    author="Cone",
    author_email="<wei.hu@enflame-tech.com>",
    description=DESCRIPTION,
    packages=['${package}'],
    install_requires=['numpy', 'immutables', 'torch'],
    keywords=['python'],
    package_dir={'${package}':'${dir}'},
    package_data={'${package}':['*.so', '*.cone']},
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
  -- putStrLn contents
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
      runC d [fn, "bdist"]
      runC d [fn, "install", "--user"]
  where runC d args = do
          ec <- runProcess target args (Just d) Nothing Nothing Nothing Nothing >>= waitForProcess
          when (ec /= ExitSuccess) $ exitWith ec