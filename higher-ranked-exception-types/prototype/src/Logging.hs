module Logging (
    module LogClass,
    message,
    message',
    messageProcess
) where

import Control.Concurrent
import Control.Monad
import Control.Monad.Reader
import Data.Time
import System.Console.ANSI

import Handler
import LogClass

logColor :: LogClass -> Color
logColor Info    = Blue
logColor Warning = Red

message :: LogClass -> String -> Handler ()
message logClass msg = do
    chan <- ask
    liftIO $ writeChan chan (logClass, msg)

message' :: Show a => LogClass -> a -> Handler ()
message' logClass msg = do
    chan <- ask
    liftIO $ writeChan chan (logClass, show msg)

printMessage :: LogClass -> String -> IO ()
printMessage logClass msg = do
    currentTime <- getCurrentTime
    setSGR [SetColor Foreground Vivid Black]
    putStr ("[" ++ show currentTime ++ "] ")
    setSGR [SetColor Foreground Dull (logColor logClass)]
    putStrLn msg
    
messageProcess :: Chan (LogClass, String) -> IO ()
messageProcess chan = do
    contents <- getChanContents chan
    mapM (uncurry printMessage) contents
    return ()
