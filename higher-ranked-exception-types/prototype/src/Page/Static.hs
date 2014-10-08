module Page.Static (
    render
) where

import Data.List
import System.IO

import URL

render :: ResourcePath -> IO String
render path = do
    let filePath = "static/" ++ intercalate "/" path
    handle <- openFile filePath ReadMode
    hSetEncoding handle char8
    contents <- hGetContents handle
    return contents
