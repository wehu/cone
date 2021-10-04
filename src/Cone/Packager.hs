{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Cone.Packager where

import Cone.Compiler
import Data.Text
import NeatInterpolation (trimming)
import System.Directory

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
    package_data={'${package}':['*.so', '*.cone']}
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

