module Main where

import Control.Concurrent
import Control.Exception hiding (Handler)
import Control.Monad
import Control.Monad.Reader
import Data.Maybe
import System.IO
import Network

import Handler
import Logging
import HTTP
import URL

import qualified Page.Main
import qualified Page.Static

-- | Configuration

port :: PortID
port = PortNumber 8666

-- | Main

main :: IO ()
main = withSocketsDo $ do
    chan <- newChan
    forkIO (messageProcess chan)
    socket <- listenOn port
    runReaderT (handleConnections socket) chan

-- | Connection handling

handleConnections :: Socket -> Handler ()
handleConnections socket = do

    (handle, hostName, portNumber) <- liftIO $ accept socket

    handleRequest'   <- runHandler  (handleRequest handle)
    handleException' <- runHandler1 (handleException handle)
    threadId         <- liftIO $ forkFinally handleRequest' handleException'

    handleConnections socket
    
handleRequest :: Handle -> Handler ()
handleRequest handle = do
    contents <- liftIO $ hGetContents handle
    let request@(Request _ url' _ headers) = parseRequest contents
    -- message' Info request
    let url@(URL _ resourcePath _) = parseURL (fromJust $ lookup "Host" headers) url'
    message' Info url

    -- Routing
    let renderer = case resourcePath of
            [""]            -> Just Page.Main.render
            ["favicon.ico"] -> Just (Page.Static.render
                                        ["html5-boilerplate-4.3.0","favicon.ico"])
            ("static":path) -> Just (Page.Static.render path)
            _               -> Nothing

    -- Rendering
    liftIO $ do
        response <- case renderer of
            Just k -> do
                messageBody <- k
                return (respond200 messageBody)
            Nothing -> do
                return respond404
        hPutStr handle (show response)
        hClose handle

handleException :: Show a => Handle -> Either SomeException a -> Handler ()
handleException handle (Left someException) = do
    message Warning $
        "A thread terminated with the exception: " ++ show someException
    liftIO $ do
        hPutStr handle (show respond500)
        hClose handle
handleException handle (Right x) = do
    liftIO $ hClose handle
    return ()
