module Handler where

import Control.Concurrent
import Control.Monad.Reader

import LogClass

type Handler a = ReaderT (Chan (LogClass, String)) IO a

runHandler :: Handler a -> Handler (IO a)
runHandler handler = do
    state <- ask
    return (runReaderT handler state)
    
runHandler1 :: (a -> Handler b) -> Handler (a -> IO b)
runHandler1 handler = do
    state <- ask
    return (\x -> runReaderT (handler x) state)    
