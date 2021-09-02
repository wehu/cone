module Cone.ModuleLoader (loadModule) where

import Cone.Parser.AST
import Cone.Parser.Parser
import Cone.TypeChecker
import Control.Lens
import Control.Monad
import Control.Monad.Except
import Data.IORef
import Data.List (elemIndex)
import Data.List.Split
import qualified Data.Map as M
import Data.Map.Merge.Strict
import System.Directory
import System.FilePath
import System.IO

type Loaded = M.Map FilePath Bool

type LoadEnv = ExceptT String IO (Env, Int, Module)

type Cache = M.Map FilePath (Env, Int, Module)

searchFile :: [FilePath] -> FilePath -> ExceptT String IO String
searchFile (p : paths) f = do
  if isAbsolute f
    then do
      found <- liftIO $ doesFileExist f
      if found
        then return f
        else throwError $ "cannot find file: " ++ f
    else do
      let ff = p </> f
      found <- liftIO $ doesFileExist ff
      if found
        then return ff
        else searchFile paths f
searchFile [] f = throwError $ "cannot find file: " ++ f

loadModule' :: IORef Cache -> [FilePath] -> FilePath -> Loaded -> LoadEnv
loadModule' cache paths f' loaded = do
  f <- searchFile paths f'
  cached <- liftIO $ (\c -> c ^. at f) <$> readIORef cache
  case cached of
    Just e -> return e
    Nothing ->
      case loaded ^. at f of
        Just _ -> throwError $ "cyclar loading: " ++ f'
        Nothing -> do
          let newLoaded = loaded & at f ?~ True
          handle <- liftIO $ openFile f ReadMode
          contents <- liftIO $ hGetContents handle
          let result = parse f contents
          case result of
            Left e -> throwError $ show e
            Right m -> do
              (env, id, _) <- importModules cache paths m newLoaded
              case initModule m env id of
                Left e -> throwError e
                Right (env, (id, m)) -> do
                  let res = (env, id, m)
                  liftIO $ modifyIORef cache $ at f ?~ res
                  return res

coneEx = "cone"

preloadedModules = ["core" </> "prelude"]

importModules :: IORef Cache -> [FilePath] -> Module -> Loaded -> LoadEnv
importModules cache paths m loaded = do
  let is = m ^.. imports . traverse
  foldM
    ( \(oldEnv, oldId, oldM) i ->
        case (m ^. moduleName) `elemIndex` preloadedModules of
          Just _ -> return (oldEnv, oldId, oldM)
          Nothing -> do
            let fn = (addExtension (joinPath $ splitOn "/" $ i ^. importPath) coneEx)
            (env, id, m) <- loadModule' cache paths fn loaded
            let g1' = mapMaybeMissing $ \k v -> Nothing
                g2' = mapMaybeMissing $ \k v -> Nothing
                f' = zipWithMaybeMatched $ \k v1 v2 -> Just v1
                typeConflicts = merge g1' g2' f' (oldEnv ^. types) (env ^. types)
                effConflicts = merge g1' g2' f' (oldEnv ^. effs) (env ^. effs)
                funcConflicts = merge g1' g2' f' (oldEnv ^. funcs) (env ^. funcs)
            if typeConflicts /= M.empty
              then throwError $ "there are type conflicts: " ++ show typeConflicts
              else return ()
            if effConflicts /= M.empty
              then throwError $ "there are eff conflicts: " ++ show effConflicts
              else return ()
            if funcConflicts /= M.empty
              then throwError $ "there are function conflicts: " ++ show funcConflicts
              else return ()
            let g1 = mapMaybeMissing $ \k v -> Just v
                g2 = mapMaybeMissing $ \k v -> Just v
                f = zipWithMaybeMatched $ \k v1 v2 -> Just v1
            return
              ( oldEnv
                  { _types = (merge g1 g2 f (oldEnv ^. types) (env ^. types)),
                    _effs = (merge g1 g2 f (oldEnv ^. effs) (env ^. effs)),
                    _funcs = (merge g1 g2 f (oldEnv ^. funcs) (env ^. funcs))
                  },
                id,
                m
              )
    )
    (initialEnv, 0, m)
    ((map (\f -> ImportStmt f Nothing [] (m ^. moduleLoc)) preloadedModules) ++ is)

loadModule :: [FilePath] -> FilePath -> LoadEnv
loadModule paths f = do
  cache <- liftIO $ newIORef M.empty
  (env, id, m) <- loadModule' cache paths f M.empty
  case checkType m env id of
    Left e -> throwError e
    Right (env, (id, m)) -> return (env, id, m)
