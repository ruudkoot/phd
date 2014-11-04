{-# LANGUAGE ExistentialQuantification, TupleSections, OverloadedStrings #-}

module Web.Page (
    Page(..),
    Parameters,
    GetRequest,
    PostRequest,
    Lens(..),
    pureRequest,
    noGet,
    noPut,
    stateless
) where

import Control.Applicative
import Data.Map

import Control.Lens

import Network.Wai        (Response, responseLBS)
import Network.HTTP.Types (status200)

-- | Page

data Page a = forall b. Page {
    getRequest  :: GetRequest b,
    postRequest :: PostRequest b,
    stateLens   :: Lens a b
}

-- | Parameters

type Parameters = Map String String

-- | GET and POST requests

type GetRequest  state = state -> Parameters -> IO Response
type PostRequest state = state -> Parameters -> IO (Response, state)

pureRequest :: GetRequest s -> PostRequest s
pureRequest getRequest state param = (,state) <$> getRequest state param

-- | Bottoms

noGet :: GetRequest state
noGet _ _ = return $ responseLBS status200 [] "OK"

noPut :: PostRequest state
noPut     = pureRequest noGet

stateless :: Lens a ()
stateless = Lens { get = const (), set = const }
