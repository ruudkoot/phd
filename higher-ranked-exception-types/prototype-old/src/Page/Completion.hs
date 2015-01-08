{-# LANGUAGE OverloadedStrings #-}

module Page.Completion (
    page
) where

import Data.ByteString.Lazy
import Data.Map

import Control.Lens
import Web.HTTP
import Web.Page
import State

page :: Page State
page = Page { getRequest  = getR,
              postRequest = postR,
              stateLens   = Lens { get = State.expr,
                                   set = \s x -> s { expr = x }
                                 }
            }

getR :: GetRequest String
getR state _ = return $ responseLBS status200 [] $ pack $ unlines [

    "<html lang=\"en\">",
        "<body>",
            "<form action=\"/completion/\" method=post>",
                "<textarea rows=10 cols=80 name=\"expr\">",
                "</textarea>",
                "<input type=submit>",
            "</form>",
            "<h1>Current expression</h1>",
            "<pre>" ++ state ++ "</pre>",
        "</body>",
    "</html>"

  ]

postR :: PostRequest String
postR state param = do
    return (status303 "/completion", findWithDefault "" "expr" param)
