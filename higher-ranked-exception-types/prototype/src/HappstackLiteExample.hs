{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}

module Main where

import Control.Applicative ((<$>), optional)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text.Lazy (unpack)
import Happstack.Lite
import Text.Blaze.Html5 (Html, (!), a, form, input, p, toHtml, label)
import Text.Blaze.Html5.Attributes (action, enctype, href, name, size, type_, value)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

main :: IO ()
main = serve Nothing myApp

myApp :: ServerPart Response
myApp = msum
    [ dir "echo" $ echo
    , dir "query" $ queryParams
    , dir "form" $ formPage
    , dir "fortune" $ fortune
    , dir "files" $ fileServing
    , dir "upload" $ upload
    , homePage
    ]

template :: Text -> Html -> Response
template title body = toResponse $
    H.html $ do
        H.head $ do
            H.title (toHtml title)
        H.body $ do
            body
            p $ a ! href "/" $ "back home"

homePage :: ServerPart Response
homePage = ok $ template "home page" $ do 
    H.h1 "Hello!"
    H.p "Writing applications with happstack-lite is fast and simple!"
    H.p "Check out these killer apps."
    H.p $ a ! href "/echo/secret%20message" $ "echo"
    H.p $ a ! href "/query?foo=bar"         $ "query parameters"
    H.p $ a ! href "/form"                  $ "form processing"
    H.p $ a ! href "/fortune"               $ "(fortune) cookies"
    H.p $ a ! href "/files"                 $ "file serving"
    H.p $ a ! href "/upload"                $ "file uploads"

echo :: ServerPart Response
echo = path $ \(msg :: String) -> ok $ template "echo" $ do
    p $ "echo says: " >> toHtml msg
    p $ "Change the url to echo something else."

queryParams :: ServerPart Response
queryParams = do
    mFoo <- optional $ lookText "foo"
    ok $ template "query params" $ do
        p $ "foo is set to: " >> toHtml (show mFoo)
        p $ "change the url to set it to something else."

formPage :: ServerPart Response
formPage = msum [ viewForm, processForm ] where

    viewForm :: ServerPart Response
    viewForm = do
        method GET
        ok $ template "form" $
            form ! action "/form"
                 ! enctype "multipart/form-data" ! A.method "POST" $ do
                label ! A.for "msg" $ "Say something clever"
                input ! type_ "text" ! A.id "msg" ! name "msg"
                input ! type_ "submit" ! value "Say it!"
       
    processForm :: ServerPart Response
    processForm = do
        method POST
        msg <- lookText "msg"
        ok $ template "form" $ do
            H.p "You said:"
            H.p (toHtml msg)

fortune :: ServerPart Response
fortune = msum [ viewFortune, updateFortune ] where

    viewFortune :: ServerPart Response
    viewFortune = do
        method GET
        memory <- fromMaybe "Your future will be filled with web programming."
            <$> optional (lookCookieValue "fortune")
        ok $ template "fortune" $ do
            H.p "The message in your (fortune) cookie says:"
            H.p (toHtml memory)
            form ! action "/fortune"
                 ! enctype "multipart/form-data" ! A.method "POST" $ do
                label ! A.for "fortune" $ "Change your fortune: "
                input ! type_ "text" ! A.id "fortune" ! name "new_fortune"
                input ! type_ "submit" ! value "Say it!"

    updateFortune :: ServerPart Response
    updateFortune = do
        method POST
        fortune <- lookText "new_fortune"
        addCookies [(Session, mkCookie "fortune" (unpack fortune))]
        seeOther ("/fortune" :: String) (toResponse ())

fileServing :: ServerPart Response
fileServing =
    serveDirectory EnableBrowsing ["index.html"] "."

upload :: ServerPart Response
upload = msum [ uploadForm, handleUpload ] where

    uploadForm :: ServerPart Response
    uploadForm = do
        method GET
        ok $ template "upload form" $ do
            form ! enctype "multipart/form-data"
                 ! A.method "POST" ! action "/upload" $ do
                input ! type_ "file" ! name "file_upload" ! size "40"
                input ! type_ "submit" ! value "upload"

    handleUpload :: ServerPart Response
    handleUpload = do
        (tmpFile, uploadName, contentType) <- lookFile "file_upload"
        ok $ template "file uploaded" $ do
            p $ toHtml $ "temporary file: " ++ tmpFile
            p $ toHtml $ "uploaded name:  " ++ uploadName
            p $ toHtml $ "content-type:   " ++ show contentType
