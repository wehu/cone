{-# LANGUAGE TypeApplications #-}

module Cone.Compiler (compile, coneUserDataDir) where

import Cone.CodeGen.Backend
import Cone.CodeGen.Backend.Cone
import Cone.CodeGen.Backend.CppHeader
import Cone.CodeGen.Backend.CppSource
import Cone.CodeGen.Backend.Python
import Cone.CodeGen.Backend.PythonType
import Cone.CodeGen.Backend.PythonWrapper
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
import System.Process

type CompileEnv a = ExceptT String IO a

coneUserDataDir = getAppUserDataDirectory "cone"

checkTimeStamp :: FilePath -> FilePath -> CompileEnv Bool
checkTimeStamp f dep = do
  found <- liftIO $ doesFileExist f
  if found
  then do
    fTS <- liftIO $ getModificationTime f
    depTS <- liftIO $ getModificationTime dep
    return $ fTS < depTS
  else return True

checkTimeStampAndDo :: FilePath -> FilePath -> CompileEnv () -> CompileEnv ()
checkTimeStampAndDo f dep action = do
  doit <- checkTimeStamp f dep
  if doit then action
  else return ()

-- | Check and compile
checkAndCompile :: [FilePath] -> String -> String -> CompileEnv ()
checkAndCompile paths i target = do
  userDataDir <- liftIO $ coneUserDataDir
  let pyFn = userDataDir </> target </> (addExtension (joinPath $ splitOn "/" i) "py")
      pyTyFn = addExtension (dropExtension pyFn ++ "____t") "py" 
      cppHeaderFn = addExtension (dropExtension pyFn) "h"
      cppLibFn = addExtension (dropExtension pyFn ++ "____c") "so"
      d = takeDirectory pyFn
  coneFn <- searchFile paths (addExtension (joinPath $ splitOn "/" i) coneEx)
  liftIO $ createDirectoryIfMissing True d

  checkTimeStampAndDo pyTyFn coneFn $ do
    o <- compilePythonType paths coneFn target
    liftIO $ writeFile pyTyFn o
  
  checkTimeStampAndDo cppHeaderFn coneFn $ do
    o <- compileToCppHeader paths coneFn target
    liftIO $ writeFile cppHeaderFn o
    
  checkTimeStampAndDo cppLibFn coneFn $ do
    compileToCppSource paths coneFn target >>= compileCppToLib paths cppLibFn
    return ()
  
  checkTimeStampAndDo pyFn coneFn $ do
    o <- compilePythonWrapper paths coneFn target
    liftIO $ writeFile pyFn o

  checkTimeStampAndDo pyFn coneFn $ do
    let ds = splitOn "/" i
    foldM
      ( \s d -> do
          let initFn = userDataDir </> joinPath s </> (addExtension "__init__" "py")
          liftIO $ writeFile initFn ""
          return $ s ++ [d]
      )
      [target]
      ds
    return ()

-- | Compile a file
compilePythonWrapper :: [FilePath] -> FilePath -> String -> CompileEnv String
compilePythonWrapper paths f target = do
  (env, id, m, imports) <- loadModule paths f
  case gen (PythonWrapper :: (PythonWrapper Target)) m of
    Left err -> throwError err
    Right doc -> return $ show doc

compilePythonType :: [FilePath] -> FilePath -> String -> CompileEnv String
compilePythonType paths f target = do
  (env, id, m, imports) <- loadModule paths f
  case gen (PythonType :: (PythonType Target)) m of
    Left err -> throwError err
    Right doc -> return $ show doc

compileToCppHeader :: [FilePath] -> FilePath -> String -> CompileEnv String
compileToCppHeader paths f target = do
  (env, id, m, imports) <- loadModule paths f
  case gen (CppHeader :: (CppHeader Target)) m of
    Left err -> throwError err
    Right doc -> return $ show doc

compileToCppSource :: [FilePath] -> FilePath -> String -> CompileEnv String
compileToCppSource paths f target = do
  (env, id, m, imports) <- loadModule paths f
  liftIO $ putStrLn $ "compiling " ++ f ++ "..."
  case gen (CppSource :: (CppSource Target)) m of
    Left err -> throwError err
    Right doc -> return $ show doc

getPythonIncludePaths :: IO [String]
getPythonIncludePaths = do
  o <- readProcess "python" ["-V"] ""
  let version = join $ intersperse "." $ init $ splitOn "." $ last $ splitOn " " o
  return ["-I/usr/include/python" ++ version]

compileCppToLib :: [FilePath] -> String -> FilePath -> CompileEnv String
compileCppToLib paths outputFile input = do
  pythonHeaderPaths <- liftIO getPythonIncludePaths
  userDataDir <- liftIO $ coneUserDataDir
  let cc = "g++"
      args =
        ["-fstack-usage", "-lstdc++", "-O3", "-std=c++14", "-shared", "-fPIC", "-I" ++ userDataDir </> "python"]
          ++ pythonHeaderPaths
          ++ map (\p -> "-I" ++ (p </> "include")) paths
          ++ ["-o", outputFile, "-xc++", "-"]
  -- liftIO $ putStrLn $ "compiling..."
  liftIO $ readProcess cc args input

-- | Compile a file
compile :: [FilePath] -> FilePath -> String -> CompileEnv String
compile paths f target = do
  (env, id, m, imports) <- loadModule paths f
  case target of
    "cone" -> do
      case gen (Cone :: (Cone Target)) m of
        Left err -> throwError err
        Right doc -> return $ show doc
    "python" -> do
      forM_ (nub $ reverse $ (dropExtension f) : imports) $ \p ->
        checkAndCompile paths p target
      return ""
    _ -> throwError $ "unknown target: " ++ target
