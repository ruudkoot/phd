module Page.Completion (
    page
) where

import Data.Map

import Web.HTTP
import Web.Page
import Lens
import State

page :: Page State
page = Page { getRequest  = getR,
              postRequest = postR,
              stateLens   = Lens { get = State.expr,
                                   set = \s x -> s { expr = x }
                                 }
            }

getR :: GetRequest String
getR state _ = return $ respond200 $ unlines [

    "<html lang=\"en\">",
        "<body>",
            "<form action=\"/completion/\" method=post>",
                "<textarea rows=10 cols=80 name=\"expr\">",
                "</textarea>",
                "<input type=submit>",
            "</form>",
            "<h1>Current expression</h1>",
            "<p>" ++ state ++ "</p>",
        "</body>",
    "</html>"

  ]

postR :: PostRequest String
postR state param = do
    return (respond303 "/completion", findWithDefault "" "eval" param)
