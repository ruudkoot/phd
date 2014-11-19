module Paths_prototype (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [0,1,0,0], versionTags = []}
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/ruud/.cabal/bin"
libdir     = "/home/ruud/.cabal/lib/x86_64-linux-ghc-7.8.3/prototype-0.1.0.0"
datadir    = "/home/ruud/.cabal/share/x86_64-linux-ghc-7.8.3/prototype-0.1.0.0"
libexecdir = "/home/ruud/.cabal/libexec"
sysconfdir = "/home/ruud/.cabal/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "prototype_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "prototype_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "prototype_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "prototype_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "prototype_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
