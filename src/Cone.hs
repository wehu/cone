module Cone
  ( coneMain,
  )
where

import Options.Applicative
import Data.Semigroup ((<>))
import Cone.CodeGen.ModuleLoader
import Control.Monad
import Control.Monad.Except
import System.Environment
import System.Directory
import System.FilePath

data Opts = InputFiles {inputFiles :: [String]}

coneOpts :: Parser Opts
coneOpts = InputFiles <$> some (argument str (metavar "FILES..."))

coneMain :: IO ()
coneMain = play =<< execParser opts
  where opts = info (coneOpts <**> helper)
               (fullDesc <> progDesc "Compile cone files"
                         <> header "Cone - ")

play :: Opts -> IO ()
play (InputFiles files) = do
  forM_ (("core" </> "prelude.cone"):files) $ \f -> do 
    currentPath <- getCurrentDirectory
    execPath <- getExecutablePath
    let libPath = (takeDirectory $ takeDirectory execPath) </> "lib"
        paths = currentPath:libPath:[]
    res <- runExceptT $ loadModule paths f
    case res of
      Left e -> putStrLn e
      Right _ -> return ()