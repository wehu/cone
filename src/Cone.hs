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

data BuildOpts = BuildOpts {inputFiles :: [String], target :: String}

data DumpOpts = DumpOpts

buildOpts =
  BuildOpts <$> some (argument str (metavar "MODULES..."))
    <*> strOption
      ( long "target"
          <> short 't'
          <> metavar "TARGET"
          <> value "python"
          <> help "Target for codegen"
      )

coneOpts :: Parser (IO ())
coneOpts = subparser (
  command "build" (info (build <$> buildOpts)
    ( fullDesc <> progDesc "Compile cone modules"
               <> header "Cone - "))
  <> command "run" (info (buildAndRun <$> buildOpts)
    ( fullDesc <> progDesc "Compile and run cone modules"
               <> header "Cone - "))
  <> command "dump" (info (dump <$> buildOpts)
    ( fullDesc <> progDesc "Dump cone files"
               <> header "Cone - ")))

coneMain :: IO ()
coneMain = join $ execParser (info coneOpts
             ( fullDesc <> progDesc "Compile/Run/Release cone modules"
              <> header "Cone - "
             ))

coneSearchPaths :: String -> IO [FilePath]
coneSearchPaths f = do
  currentPath <- getCurrentDirectory
  execPath <- getExecutablePath





  let ghcVersion = show (div 810 100) ++ "." ++ show (mod 810 100) ++ "."
                     ++ show 4




  let coneVersion = showVersion version
  let libPath = takeDirectory (takeDirectory execPath) </> "share" </> arch ++ "-" ++ os ++ "-ghc-" ++ ghcVersion </> "cone-" ++ coneVersion </> "lib"
  let paths = takeDirectory f: currentPath : [libPath]
  return paths

build :: BuildOpts -> IO ()
build BuildOpts {..} = do
  forM_ inputFiles $ \f -> do
    paths <- coneSearchPaths f
    res <- runExceptT $ compile paths f target
    case res of
      Left err -> putStrLn err
      Right code -> return ()

buildAndRun :: BuildOpts -> IO ()
buildAndRun BuildOpts {..} = do
  forM_ inputFiles $ \f -> do
    paths <- coneSearchPaths f
    res <- runExceptT $ compile paths f target
    case res of
      Left err -> putStrLn err
      Right code -> runCode target [] code f >>= putStrLn

dump :: BuildOpts -> IO ()
dump BuildOpts {..} = do
  forM_ inputFiles $ \f -> do
    paths <- coneSearchPaths f
    res <- runExceptT $ compile paths f target
    case res of
      Left err -> putStrLn err
      Right code -> putStrLn code
