module URL (
    HostPath,
    ResourcePath,
    Parameters,
    URL(..),
    parseURL
) where

import Data.List
import Data.List.Split

type HostPath     = [String]
type ResourcePath = [String]
type Parameters   = [(String, String)]

data URL = URL HostPath ResourcePath Parameters

instance Show URL where
    show (URL hostPath resourcePath [])
        = intercalate "." (reverse hostPath)
          ++ "/" ++ intercalate "/" resourcePath
    show (URL hostPath resourcePath parameters)
        = intercalate "." (reverse hostPath)
          ++ "/" ++ intercalate "/" resourcePath
          ++ "?" ++ intercalate "&" (map (\(key, val) -> key ++ "=" ++ val) parameters)

splitOn' :: Eq a => a -> [a] -> ([a], [a])
splitOn' sep []     = ([], [])
splitOn' sep (x:xs) | x == sep  = ([], xs)
                    | otherwise = let (key, val) = splitOn' sep xs in (x:key, val)
          
parseParameters :: String -> [(String, String)]
parseParameters [] = []
parseParameters xs = map (splitOn' '=') (splitOn "&" xs)

parseResource :: String -> (ResourcePath, Parameters)
parseResource xs = let (resource, parameters) = splitOn' '?' xs
                    in ( splitOn "/" (tail resource)
                       , parseParameters parameters  )

parseHost :: String -> HostPath
parseHost = reverse . splitOn "."

parseURL :: String -> String -> URL
parseURL host path =
    let (resourcePath, parameters) = parseResource path
     in URL (parseHost host) resourcePath parameters
