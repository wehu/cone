{-# LANGUAGE RecordWildCards #-}

module Cone
  ( coneMain,
  )
where

import Cone.CodeGen.ModuleLoader
import Cone.CodeGen.Compiler
import Control.Monad
import Control.Monad.Except
import Data.Semigroup ((<>))
import Options.Applicative
import System.Directory
import System.Environment
import System.FilePath

data Opts = Opts {inputFiles :: [String]}

coneOpts :: Parser Opts
coneOpts = Opts <$> some (argument str (metavar "FILES..."))

coneMain :: IO ()
coneMain = play =<< execParser opts
  where
    opts =
      info
        (coneOpts <**> helper)
        ( fullDesc <> progDesc "Compile cone files"
            <> header "Cone - "
        )

play :: Opts -> IO ()
play Opts{..} = do
  forM_ inputFiles $ \f -> do
    currentPath <- getCurrentDirectory
    execPath <- getExecutablePath
    let libPath = (takeDirectory $ takeDirectory execPath) </> "lib"
        paths = currentPath : libPath : []
    res <- compile paths f
    case res of
      Left e -> putStrLn e
      Right s -> putStrLn s
