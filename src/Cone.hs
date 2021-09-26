{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}

module Cone
  ( coneMain,
  )
where

import Cone.Compiler
import Cone.Executor
import Cone.ModuleLoader
import Control.Monad
import Control.Monad.Except
import Data.Semigroup ((<>))
import Options.Applicative
import System.Directory
import System.Environment
import System.FilePath
import System.Info
import Paths_cone (version)
import Data.Version (showVersion)

data Opts = Opts {inputFiles :: [String], target :: String, dump :: Bool}

-- | Option definitions
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
    <*> switch
      ( long "dump"
          <> short 'd'
          <> help "Dump code"
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

coneSearchPaths :: String -> IO [FilePath]
coneSearchPaths f = do
  currentPath <- getCurrentDirectory
  execPath <- getExecutablePath
#if defined(__GLASGOW_HASKELL_PATCHLEVEL2__)
  let ghcVersion = show (div __GLASGOW_HASKELL__ 100) ++ "." ++ show (mod __GLASGOW_HASKELL__ 100) ++ "." 
                     ++ show __GLASGOW_HASKELL_PATCHLEVEL1__ ++ "." ++ show __GLASGOW_HASKELL_PATCHLEVEL2__
#else
#if defined(__GLASGOW_HASKELL_PATCHLEVEL1__)
  let ghcVersion = show (div __GLASGOW_HASKELL__ 100) ++ "." ++ show (mod __GLASGOW_HASKELL__ 100) ++ "."
                     ++ show __GLASGOW_HASKELL_PATCHLEVEL1__
#else
  let ghcVersion = show (div __GLASGOW_HASKELL__ 100) ++ "." ++ show (mod __GLASGOW_HASKELL__ 100)
#endif
#endif
  let coneVersion = showVersion version
  let libPath = (takeDirectory $ takeDirectory execPath) </> "share" </> arch ++ "-" ++ os ++ "-ghc-" ++ ghcVersion </> "cone-" ++ coneVersion </> "lib"
  let paths = (takeDirectory f): currentPath : [libPath]
  return paths

-- | Run the compilier and executor
play :: Opts -> IO ()
play Opts {..} = do
  forM_ inputFiles $ \f -> do
    paths <- coneSearchPaths f
    res <- runExceptT $ compile paths f target
    case res of
      Left err -> putStrLn err
      Right code ->
        if dump
          then putStrLn code
          else runCode target [] code f >>= putStrLn
