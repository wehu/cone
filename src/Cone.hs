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
    contents <- compile paths f
    putStrLn contents
