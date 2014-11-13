{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}

------------------------------------------------------------------------------
-- | This module is where all the routes and handlers are defined for your
-- site. The 'app' function is the initializer that combines everything
-- together and is exported by this module.
module Handler.LambdaUnion
  ( handleRoot
  ) where

------------------------------------------------------------------------------
import           Control.Applicative
import           Control.Lens
import           Data.ByteString (ByteString)
import qualified Data.Text as T
import           Snap.Core
import           Snap.Snaplet
import           Snap.Snaplet.Auth
import           Snap.Snaplet.Auth.Backends.JsonFile
import           Snap.Snaplet.Heist
import           Snap.Snaplet.Session.Backends.CookieSession
import           Snap.Util.FileServe
import           Heist
import qualified Heist.Interpreted as I
------------------------------------------------------------------------------
import Application

------------------------------------------------------------------------------
-- | Handle new user form submit
handleRoot :: Handler App App ()
handleRoot = method GET handleGet <|> method POST handlePost
  where
    handleGet  = render "lambda-union"
    handlePost = undefined >> redirect "/"

