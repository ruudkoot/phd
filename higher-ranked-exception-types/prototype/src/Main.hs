{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, ViewPatterns #-}

module Main where

import Control.Applicative ((<$>), optional)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text.Lazy (unpack)
import Happstack.Lite
import Text.Blaze.Html5 (Html, (!), a, form, input, p, toHtml, label, textarea)
import Text.Blaze.Html5.Attributes (action, enctype, href, name, size, type_, value)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

main :: IO ()
main = serve Nothing myApp

myApp :: ServerPart Response
myApp = msum
    [ dir "lambda-union" $ lambdaUnion
    , homePage
    ]

template :: Text -> Html -> Response
template (toHtml -> title) body = toResponse $
    H.docTypeHtml $ do
        H.head $ do
            H.title title
        H.body $ do
            H.h1 title
            body
            p $ a ! href "/" $ "back home"

homePage :: ServerPart Response
homePage = ok $ template "Higher-Ranked Exception Types" $ do
    H.p $ a ! href "/lambda-union" $ "lambda-union"

lambdaUnion :: ServerPart Response
lambdaUnion = msum [ viewForm, processForm ] where

    viewForm :: ServerPart Response
    viewForm = do
        method GET
        ok $ template "lambda-union" $
            form ! action "/lambda-union"
                 ! enctype "multipart/form-data" ! A.method "POST" $ do
                textarea ! name "expr" ! A.cols "80" $ ""
                input ! type_ "submit"

    processForm :: ServerPart Response
    processForm = do
        method POST
        expr <- lookText "expr"
        
        
        
        ok $ template "lambda-union" $ do
            H.h2 "Expression"
            H.p (toHtml expr)
