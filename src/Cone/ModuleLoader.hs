module Cone.ModuleLoader (loadModule, coneEx, preloadedModules, searchFile, getImports, getImportsRecursively) where

import Cone.Parser.AST
import Cone.Parser.Parser
import Cone.Env
import Cone.TypeChecker
import Control.Lens
import Control.Monad
import Control.Monad.Except
import Data.IORef
import Data.List (elemIndex, nubBy)
import Data.List.Split
import qualified Data.Map as M
import Data.Map.Merge.Strict
import System.Directory
import System.FilePath
import System.IO
import Unbound.Generics.LocallyNameless

type Loaded = M.Map FilePath Bool

type LoadEnv = ExceptT String IO (Env, Int, Module, [String])

type Cache = M.Map FilePath (Env, Int, Module, [String])

-- | Search a file in path list
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

getImports :: [FilePath] -> FilePath -> ExceptT String IO [String]
getImports paths f' = do
  f <- searchFile paths f'
  handle <- liftIO $ openFile f ReadMode
  contents <- liftIO $ hGetContents handle
  let result = parse f contents
  case result of
    Left err -> throwError $ show err
    Right m -> return $ (m ^.. imports . traverse . importPath) ++ preloadedModules

getImportsRecursively :: [FilePath] -> FilePath -> ExceptT String IO [String]
getImportsRecursively paths f = do
  imports <- getImports paths f
  ims <-
    join
      <$> mapM
        ( \i ->
            if i `elem` preloadedModules
              then return []
              else getImportsRecursively paths (addExtension i coneEx)
        )
        imports
  return $ imports ++ ims

-- | Load a module
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
          relF <- liftIO $ makeRelativeToCurrentDirectory f
          let result = parse relF contents
          case result of
            Left e -> throwError $ show e
            Right m -> do
              (env, id, _, imports) <- importModules cache paths m newLoaded
              case initModule m env id of
                Left e -> throwError e
                Right (env, (id, m)) -> do
                  case checkType m env id of
                    Left err -> throwError err
                    Right (env, (id, m)) -> do
                      let res = (env, id, m, imports)
                      liftIO $ modifyIORef cache $ at f ?~ res
                      return res

coneEx = "cone"

preloadedModules = ["core" </> "prelude"]

-- | Import a list of module into current env
importModules :: IORef Cache -> [FilePath] -> Module -> Loaded -> LoadEnv
importModules cache paths m loaded = do
  let is = m ^.. imports . traverse
  foldM
    ( \(oldEnv, oldId, oldM, imports) i ->
        case (m ^. moduleName) `elemIndex` preloadedModules of
          Just _ -> return (oldEnv, oldId, oldM, imports)
          Nothing -> do
            let fn = addExtension (joinPath $ splitOn "/" (i ^. importPath)) coneEx
            (env, id, m, is) <- loadModule' cache paths fn loaded
            let g1' = mapMaybeMissing $ \k v -> Nothing
                g2' = mapMaybeMissing $ \k v -> Nothing
                f' = zipWithMaybeMatched $ \k v1 v2 -> Just (v1, v2)
                typeConflicts = merge g1' g2' f' (oldEnv ^. types) (env ^. types)
                typeAliasConflicts = merge g1' g2' f' (oldEnv ^. typeAliases) (env ^. typeAliases)
                effConflicts = merge g1' g2' f' (oldEnv ^. effs) (env ^. effs)
                effIntfConflicts = merge g1' g2' f' (oldEnv ^. effIntfs) (env ^. effIntfs)
                funcConflicts = merge g1' g2' f' (oldEnv ^. funcs) (env ^. funcs)
                diffAdjConflicts = merge g1' g2' f' (oldEnv ^. diffAdjs) (env ^. diffAdjs)
            unless (all (uncurry aeq) typeConflicts) $ throwError $ "there are type conflicts: " ++ show typeConflicts
            unless (all (uncurry aeq) typeAliasConflicts) $ throwError $ "there are type alias conflicts: " ++ show typeAliasConflicts
            unless (all (uncurry aeq) effConflicts) $ throwError $ "there are eff conflicts: " ++ show effConflicts
            unless (all (uncurry aeq) effIntfConflicts) $ throwError $ "there are eff inteface conflicts: " ++ show effIntfConflicts
            unless (all (uncurry aeq) funcConflicts) $ throwError $ "there are function conflicts: " ++ show funcConflicts
            unless (all (uncurry aeq) diffAdjConflicts) $ throwError $ "there are diff rule conflicts: " ++ show diffAdjConflicts
            let g1 = mapMaybeMissing $ \k v -> Just v
                g2 = mapMaybeMissing $ \k v -> Just v
                f = zipWithMaybeMatched $ \k v1 v2 -> Just v1
                mergeImpls = zipWithMaybeMatched $ \k v1 v2 -> Just $ nubBy aeq $ v1 ++ v2
            return
              ( oldEnv
                  { _types = merge g1 g2 f (oldEnv ^. types) (env ^. types),
                    _typeAliases = merge g1 g2 f (oldEnv ^. typeAliases) (env ^. typeAliases),
                    _effs = merge g1 g2 f (oldEnv ^. effs) (env ^. effs),
                    _effIntfs = merge g1 g2 f (oldEnv ^. effIntfs) (env ^. effIntfs),
                    _funcs = merge g1 g2 f (oldEnv ^. funcs) (env ^. funcs),
                    _funcImpls = merge g1 g2 mergeImpls (oldEnv ^. funcImpls) (env ^. funcImpls),
                    _diffAdjs  = merge g1 g2 f (oldEnv ^. diffAdjs) (env ^. diffAdjs)
                  },
                id,
                m,
                imports ++ is
              )
    )
    (initialEnv, 0, m, preloadedModules ++ (is ^.. traverse . importPath))
    (map (\f -> ImportStmt f Nothing [] (m ^. moduleLoc)) preloadedModules ++ is)

-- | Load a module
loadModule :: [FilePath] -> FilePath -> LoadEnv
loadModule paths f = do
  cache <- liftIO $ newIORef M.empty
  loadModule' cache paths f M.empty
