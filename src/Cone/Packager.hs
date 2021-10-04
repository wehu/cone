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
import System.Process

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
    packages=find_packages(include=["$package"]),
    install_requires=['numpy', 'immutables'],
    keywords=['python'],
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

createSetupPy :: String -> String -> IO String
createSetupPy target package = do
  let contents = setupPy package
  fn <- (\d -> d </> target </> "setup.py") <$> coneUserDataDir
  writeFile fn contents
  return fn

installPackage :: String -> String -> IO ()
installPackage target fn = do
  let package = dropExtension fn
  when (target == "python") $ do
    fn <- createSetupPy target package
    readProcess target [fn, "install", "--user"] ""
    return ()