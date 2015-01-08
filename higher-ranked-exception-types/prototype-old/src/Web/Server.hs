{-# LANGUAGE NamedFieldPuns #-}

module Web.Server (
    run
) where

import Control.Applicative
import Control.Concurrent
import Control.Exception hiding (Handler)
import Control.Monad
import Control.Monad.Reader
import Data.IORef
import Data.Map (fromList)
import Data.Maybe
import System.IO
import Network

import Network.Wai (responseLBS, Application)
import Network.Wai.Handler.Warp (run)
import Network.HTTP.Types (status200)
import Network.HTTP.Types.Header (hContentType)

import Web.Encoding
import Web.Handler
import Web.HTTP
import Web.Logging
import Web.URL
import Web.Page as Page

import qualified State

import qualified Page.Main
import qualified Page.Static
import qualified Page.Completion


run :: PortNumber -> IO ()
run port = withSocketsDo $ do

    state <- newIORef State.initial

    let handleConnections :: Socket -> Handler ()
        handleConnections socket = do

            (handle, hostName, portNumber) <- liftIO $ accept socket

            handleRequest'   <- runHandler  (handleRequest handle)
            handleException' <- runHandler1 (handleException handle)
            threadId         <- liftIO $ forkFinally handleRequest' handleException'

            handleConnections socket
            
        handleRequest :: Handle -> Handler ()
        handleRequest handle = do
            threadId <- liftIO myThreadId
            message' Info $ "handleRequest" ++ show handle ++ "{threadId = " ++ show threadId ++ "}"
            contents <- liftIO $ hGetContents handle
            let request@(Request reqType url' _ headers messageBody)
                    = parseRequest contents
            message' Info $ "--- handleRequest"
            message' Info request
            let url@(URL _ resourcePath _)
                    = parseURL (fromJust $ lookup "Host" headers) url'
            message' Info url

            -- Routing
            let renderer = case resourcePath of {
                -- []              -> return $ Page.Main.render;
                -- ["favicon.ico"] -> return $ Page.Static.render
                --                     ["html5-boilerplate-4.3.0","favicon.ico"];
                -- ("static":path) -> return $ Page.Static.render path;
                ["completion"]  -> return $ Page.Completion.page;
                _               -> Nothing;
            }

            -- Rendering
            liftIO $ do
                response <- mkResponse state renderer reqType
                                (fromList headers)
                                (fromList . decode . WWWFormURLEncoded $ messageBody)
                hPutStr handle (show response)
                hClose handle
                
            message' Info $ ">>> handleRequest:" ++ show handle

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

    chan <- newChan
    forkIO (messageProcess chan)
    socket <- listenOn (PortNumber port)
    runReaderT (handleConnections socket) chan
    
  where

-- | Renderers

mkResponse :: IORef state
           -> Maybe (Page state)
           -> RequestType
           -> Page.Parameters
           -> Page.Parameters
           -> IO Response
mkResponse state
           (Just (Page {getRequest, postRequest, stateLens}))
           reqType
           getParam
           postParam
  = do st <- readIORef state
       (response, st') <- case reqType of {
         GET  -> pureRequest getRequest (Page.get stateLens st) getParam;
         POST -> postRequest            (Page.get stateLens st) postParam;
       }
       writeIORef state (Page.set stateLens st st')
       return response
mkResponse _ Nothing _ _ _
    = return respond404
    
parseGet :: String -> Page.Parameters
parseGet = undefined

parsePost :: String -> Page.Parameters
parsePost = undefined
