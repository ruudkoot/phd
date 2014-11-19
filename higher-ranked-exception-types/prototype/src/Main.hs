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

import qualified Analysis.LambdaUnion as LU
import           Analysis.Latex

main :: IO ()
main = serve Nothing myApp

myApp :: ServerPart Response
myApp = msum
    [ dir "static"       $ fileServing
    , dir "lambda-union" $ lambdaUnion
    , homePage
    ]

template :: Text -> Html -> Response
template (toHtml -> title) body = toResponse $
    H.docTypeHtml $ do
        H.head $ do
            H.title title
            H.script ! type_ "text/javascript"
                     ! A.src "/static/jquery/jquery-2.1.1.min.js" $ ""
            H.script ! type_ "text/x-mathjax-config" $ toHtml $ unlines [
                  "MathJax.Hub.Config({",
                  "  extensions: [\"tex2jax.js\"],",
                  "  jax: [\"input/TeX\",\"output/HTML-CSS\"],",
                  "  tex2jax: {inlineMath: [[\"$\",\"$\"],[\"\\\\(\",\"\\\\)\"]]}",
                  "});"
              ]
            H.script ! type_ "text/javascript"
                     ! A.src "/static/mathjax/MathJax.js" $ ""
            H.script ! type_ "text/javascript"
                     ! A.src "/static/d3/3.4.13/d3.min.js" $ ""
        H.body $ do
            H.h1 title
            body
            p $ a ! href "/" $ "back home"

homePage :: ServerPart Response
homePage = ok $ template "Higher-Ranked Exception Types" $ do
    H.p $ a ! href "/lambda-union" $ "lambda-union"
    
fileServing :: ServerPart Response
fileServing =
    serveDirectory DisableBrowsing [] "static"

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
        expr :: LU.Tm () <- read . unpack <$> lookText "expr"
        ok $ template "lambda-union" $ do
            H.h2 "Expression"
            H.p $ toHtml $ "\\[" ++ latex expr ++ "\\]"

            H.h2 "Reduction"
            
