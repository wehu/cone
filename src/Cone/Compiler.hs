{-# LANGUAGE TypeApplications #-}

module Cone.Compiler (compile, coneUserDataDir) where

import Cone.CodeGen.Backend
import Cone.CodeGen.Backend.Cone
import Cone.CodeGen.Backend.Python
import Cone.CodeGen.Backend.CppSource
import Cone.ModuleLoader
import Cone.Parser.AST
import Control.Lens
import Control.Monad
import Control.Monad.Except
import Data.List
import Data.List.Split
import Data.Proxy
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

      d = takeDirectory fn
  coneFn <- searchFile paths (addExtension (joinPath $ splitOn "/" i) coneEx)
  liftIO $ createDirectoryIfMissing True d
  found <- liftIO $ doesFileExist fn
  if found
    then do
      fTS <- liftIO $ getModificationTime fn
      coneFTS <- liftIO $ getModificationTime coneFn
      if fTS /= coneFTS
        then do
          (o, _, _) <- compile' paths coneFn target
          liftIO $ writeFile fn o
          addInitFile userDataDir i
        else return ()
    else do
      (o, _, _) <- compile' paths coneFn target
      liftIO $ writeFile fn o
      addInitFile userDataDir i
  where
    addInitFile userDataDir i = do
      let ds = splitOn "/" i
      foldM
        ( \s d -> do
            let initFn = userDataDir </> joinPath s </> (addExtension "__init__" (targetEx target))
            liftIO $ writeFile initFn ""
            return $ s ++ [d]
        )
        [target]
        ds
      return ()

checkAndCompileImports :: [FilePath] -> Module -> String -> CompileEnv ()
checkAndCompileImports paths m target = do
  let ims = m ^.. imports . traverse . importPath
  forM_ ims (\i -> checkAndCompileImport paths i target)

-- | Compile a file
compile' :: [FilePath] -> FilePath -> String -> CompileEnv (String, Module, [String])
compile' paths f target = do
  (env, id, m, imports) <- loadModule paths f
  case target of
    "cone" -> case gen (Cone :: (Cone Target)) m of
      Left err -> throwError err
      Right doc -> return $ (show doc, m, imports)
    "python" -> case gen (Python :: (Python Target)) m of
      Left err -> throwError err
      Right doc -> return $ (show doc, m, imports)
    _ -> throwError $ "unknown target: " ++ target

compileToCpp :: [FilePath] -> FilePath -> String -> CompileEnv String
compileToCpp paths f target = do
  (env, id, m, imports) <- loadModule paths f
  case target of
    "cone" -> return ""
    "python" -> case gen (CppSource :: (CppSource Target)) m of
      Left err -> throwError err
      Right doc -> return $ show doc
    _ -> throwError $ "unknown target: " ++ target

-- | Compile a file
compile :: [FilePath] -> FilePath -> String -> CompileEnv String
compile paths f target = do
  (o, m, imports) <- compile' paths f target
  forM_ (nub $ (dropExtension f):imports) $ \p ->
    checkAndCompileImport paths p target
  return o
