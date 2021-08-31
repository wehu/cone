module Cone
  ( coneMain,
  )
where

import Cone.CodeGen.ModuleLoader
import Cone.Parser.AST (ppr)
import Control.Monad
import Control.Monad.Except
import Data.Semigroup ((<>))
import Options.Applicative
import System.Directory
import System.Environment
import System.FilePath

data Opts = InputFiles {inputFiles :: [String]}

coneOpts :: Parser Opts
coneOpts = InputFiles <$> some (argument str (metavar "FILES..."))

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
play (InputFiles files) = do
  forM_ files $ \f -> do
    currentPath <- getCurrentDirectory
    execPath <- getExecutablePath
    let libPath = (takeDirectory $ takeDirectory execPath) </> "lib"
        paths = currentPath : libPath : []
    res <- runExceptT $ loadModule paths f
    case res of
      Left e -> putStrLn e
      Right (_, _, m) -> do
        putStrLn $ ppr m
