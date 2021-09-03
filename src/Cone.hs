{-# LANGUAGE RecordWildCards #-}

module Cone
  ( coneMain,
  )
where

import Cone.Compiler
import Cone.ModuleLoader
import Control.Monad
import Control.Monad.Except
import Data.Semigroup ((<>))
import Options.Applicative
import System.Directory
import System.Environment
import System.FilePath

data Opts = Opts {inputFiles :: [String], target :: String, run :: String}

coneOpts :: Parser Opts
coneOpts =
  Opts <$> some (argument str (metavar "FILES..."))
    <*> strOption
      ( long "target"
          <> short 't'
          <> metavar "TARGET"
          <> value "python"
          <> help "Target for codegen"
      )
    <*> strOption
      ( long "run"
          <> short 'r'
          <> metavar "Run"
          <> value "python"
          <> help "Run code"
      )

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
play Opts {..} = do
  forM_ inputFiles $ \f -> do
    currentPath <- getCurrentDirectory
    execPath <- getExecutablePath
    let sharedPath = (takeDirectory $ takeDirectory execPath) </> "share"
    -- may get old version???
    d0 <- fmap (sharedPath </>) <$> listDirectory sharedPath
    d1 <- mapM (\p -> (fmap (p </>)) <$> listDirectory p) d0
    let paths = currentPath : (map (\p -> p </> "lib") $ join d1)
    res <- runExceptT $ compile paths f target
    case res of
      Left e -> putStrLn e
      Right s -> putStrLn s
