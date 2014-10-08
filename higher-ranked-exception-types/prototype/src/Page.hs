{-# LANGUAGE ExistentialQuantification #-}

module Page (
    Page(..),
    Parameters,
    GetRequest,
    PostRequest,
    Lens(..),
    stateless
) where

import Data.Map

import HTTP

-- | Page

data Page a = forall b. Page {
    getRequest  :: GetRequest b,
    postRequest :: PostRequest b,
    stateLens   :: Lens a b
}

-- | GET and POST requests

type Parameters = Map String String

type GetRequest  state = state -> Parameters -> IO Response
type PostRequest state = state -> Parameters -> IO (Response, state)

-- | Lenses

data Lens a b = Lens { get :: a -> b, set :: a -> b -> a }

-- * Stateless requests

stateless :: Lens a ()
stateless = Lens { get = const (), set = const }
