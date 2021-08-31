module Cone.CodeGen.ModuleLoader (loadModule) where

import Cone.Parser.AST
import Cone.Parser.Parser
import Cone.Passes.TypeChecker
import Control.Lens
import Control.Monad
import Control.Monad.Except
import Data.List.Split
import qualified Data.Map as M
import Data.Map.Merge.Strict
import System.Directory
import System.FilePath
import System.IO

type Loaded = M.Map String Bool

type LoadEnv = ExceptT String IO (Env, Int, Module)

loadModule' :: String -> Loaded -> LoadEnv
loadModule' f loaded = do
  found <- liftIO $ doesFileExist f
  if not found
    then throwError $ "cannot find file: " ++ f
    else case loaded ^. at f of
      Just _ -> throwError $ "cyclar loading: " ++ f
      Nothing -> do
        let newLoaded = loaded & at f ?~ True
        handle <- liftIO $ openFile f ReadMode
        contents <- liftIO $ hGetContents handle
        let result = parse f contents
        case result of
          Left e -> throwError $ show e
          Right m -> do
            (env, id, _) <- importModules m newLoaded
            case initModule m env id of
              Left e -> throwError e
              Right (env, (id, m)) -> return (env, id, m)

coneEx = "cone"

importModules :: Module -> Loaded -> LoadEnv
importModules m loaded = do
  let is = m ^.. imports . traverse
  foldM
    ( \(oldEnv, _, _) i -> do
        (env, id, m) <- loadModule' (addExtension (concat $ splitOn "\\" $ i ^. importPath) coneEx) loaded
        let g1' = mapMaybeMissing $ \k v -> Nothing
            g2' = mapMaybeMissing $ \k v -> Nothing
            f' = zipWithMaybeMatched $ \k v1 v2 -> Just v1
            typeConflicts = merge g1' g2' f' (oldEnv ^. types) (env ^. types)
            effConflicts = merge g1' g2' f' (oldEnv ^. effs) (env ^. effs)
            effIntfConflicts = merge g1' g2' f' (oldEnv ^. effIntfs) (env ^. effIntfs)
            funcConflicts = merge g1' g2' f' (oldEnv ^. funcs) (env ^. funcs)
        if typeConflicts /= M.empty
          then throwError $ "there are type conflicts: " ++ show typeConflicts
          else return ()
        if effConflicts /= M.empty
          then throwError $ "there are eff conflicts: " ++ show effConflicts
          else return ()
        if effIntfConflicts /= M.empty
          then throwError $ "there are eff interface conflicts: " ++ show effIntfConflicts
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
                _effIntfs = (merge g1 g2 f (oldEnv ^. effIntfs) (env ^. effIntfs)),
                _funcs = (merge g1 g2 f (oldEnv ^. funcs) (env ^. funcs))
              },
            id,
            m
          )
    )
    (initialEnv, 0, m)
    is

loadModule :: String -> LoadEnv
loadModule f = do
  (env, id, m) <- loadModule' f M.empty
  case checkType m env id of
    Left e -> throwError e
    Right (env, (id, m)) -> return (env, id, m)
