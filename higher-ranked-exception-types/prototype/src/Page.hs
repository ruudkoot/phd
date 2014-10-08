{-# LANGUAGE ExistentialQuantification, TupleSections #-}

module Page (
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

import HTTP
import Lens

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
noGet _ _ = return respond404

noPut :: PostRequest state
noPut     = pureRequest noGet

stateless :: Lens a ()
stateless = Lens { get = const (), set = const }
