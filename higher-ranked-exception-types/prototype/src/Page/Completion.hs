module Page.Completion (
    page
) where

import HTTP
import Page

page :: Page a
page = Page { getRequest = getR, postRequest = postR, stateLens = stateless }

getR :: GetRequest ()
getR _ _ = return $ respond200 $ unlines [

    "<html lang=\"en\">",
        "<body>",
            "<form action=\"/completion/\" method=post>",
                "<textarea rows=10 cols=80 name=\"expr\">",
                "</textarea>",
                "<input type=submit>",
            "</form>",
        "</body>",
    "</html>"

  ]
  
postR :: PostRequest ()
postR state param = do
    error "Page.Completion.post"
    
