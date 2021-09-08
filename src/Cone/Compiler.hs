{-# LANGUAGE TypeApplications #-}

module Cone.Compiler (compile, coneUserDataDir) where

import Cone.CodeGen.Backend
import Cone.CodeGen.Backend.Cone
import Cone.CodeGen.Backend.Python
import Cone.Parser.AST
import Cone.ModuleLoader
import Control.Monad
import Control.Lens
import Control.Monad.Except
import Data.Proxy
import Data.List.Split
import System.Directory
import System.FilePath
import System.IO

type CompileEnv a = ExceptT String IO a

targetEx :: String -> String
targetEx t = 
  case t of
    "python" -> "py"
    _ -> "cone"

coneUserDataDir = getAppUserDataDirectory "cone"

-- | Check and compile imports
checkAndCompileImport :: [FilePath] -> String -> String -> CompileEnv ()
checkAndCompileImport paths i target = do
  userDataDir <- liftIO $ coneUserDataDir
  let fn = userDataDir </> target </> (addExtension (joinPath $ splitOn "/" i) $ targetEx target)
      initFn = userDataDir </> target </> (addExtension "__init__" (targetEx target))
      d = takeDirectory fn
  coneFn <- searchFile paths (addExtension (joinPath $ splitOn "/" i) coneEx)
  liftIO $ createDirectoryIfMissing True d
  liftIO $ putStrLn fn
  found <- liftIO $ doesFileExist fn
  if found then do
    fTS <- liftIO $ getModificationTime fn
    coneFTS <- liftIO $ getModificationTime coneFn
    if fTS /= coneFTS
    then do
      (o, _) <- compile' paths coneFn target
      liftIO $ writeFile fn o
      liftIO $ writeFile initFn ""
    else
      return ()
  else do
    (o, _) <- compile' paths coneFn target
    liftIO $ writeFile fn o
    liftIO $ writeFile initFn ""

checkAndCompileImports :: [FilePath] -> Module -> String -> CompileEnv ()
checkAndCompileImports paths m target = do
  let ims = m ^..imports.traverse . importPath
  forM_ ims (\i -> checkAndCompileImport paths i target)

-- | Compile a file
compile' :: [FilePath] -> FilePath -> String -> CompileEnv (String, Module)
compile' paths f target = do
  (env, id, m) <- loadModule paths f
  case target of
    "cone" -> case gen (Cone :: (Cone Target)) m of
                Left err -> throwError err
                Right doc -> return $ (show doc, m)
    "python" -> case gen (Python :: (Python Target)) m of
                  Left err -> throwError err
                  Right doc -> return $ (show doc, m)
    _ -> throwError $ "unknown target: " ++ target

-- | Compile a file
compile :: [FilePath] -> FilePath -> String -> CompileEnv String
compile paths f target = do
  forM_ preloadedModules $ \p ->
    checkAndCompileImport paths p target
  (o, m) <- compile' paths f target
  checkAndCompileImports paths m target
  return o
