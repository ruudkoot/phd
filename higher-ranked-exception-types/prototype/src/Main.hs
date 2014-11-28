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

import qualified Analysis.Names       as An
import qualified Analysis.Common      as An
import qualified Analysis.Completion  as An
import qualified Analysis.Infer       as An
import qualified Analysis.LambdaUnion as LU
import           Analysis.Print

main :: IO ()
main = serve Nothing myApp

myApp :: ServerPart Response
myApp = msum $ reverse
    [ homePage
    , dir "lambda-union"            $ lambdaUnion
    , dir "hret"                    $ hretPage
    , dir "hret" $ dir "completion" $ completionPage
    , dir "hret" $ dir "inference"  $ inferencePage
    , dir "static"                  $ fileServing
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
                  "  tex2jax: {inlineMath: [[\"$\",\"$\"],[\"\\\\(\",\"\\\\)\"]]},",
                  "  \"HTML-CSS\": { styles: { '.MathJax_Display': { \"margin\": 0 }}}",
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

fileServing :: ServerPart Response
fileServing =
    serveDirectory DisableBrowsing [] "static"

homePage :: ServerPart Response
homePage = ok $ template "Higher-Ranked Exception Types" $ do
    H.p $ a ! href "/lambda-union" $ "lambda-union"
    H.p $ a ! href "/hret"         $ "higher-ranked exception types"

expressionForm :: Text -> H.AttributeValue -> ServerPart Response
expressionForm title url = do
    method GET
    ok $ template title $
        form ! action url
             ! enctype "multipart/form-data" ! A.method "POST" $ do
            textarea ! name "expr" ! A.cols "80" $ ""
            input ! type_ "submit"

lambdaUnion :: ServerPart Response
lambdaUnion = msum [ viewForm, processForm ] where

    viewForm :: ServerPart Response
    viewForm = expressionForm "lambda-union" "/lambda-union"

    processForm :: ServerPart Response
    processForm = do
        method POST

        expr :: LU.Tm () <- read . unpack <$> lookText "expr"

        let (normalizationTree, _) = LU.normalize' expr

        ok $ template "lambda-union" $ do
            H.h2 "Expression"
            H.p $ toHtml $ "\\[" ++ latex expr ++ "\\]"

            H.h2 "Reduction"
            H.p $ toHtml normalizationTree

hretPage :: ServerPart Response
hretPage = ok $ template "Higher-Ranked Exception Types" $ do
    H.p $ a ! href "/hret/completion" $ "completion"
    H.p $ a ! href "/hret/inference"  $ "inference"
    H.p $ a ! href "/hret/join"       $ "join"
    H.p $ a ! href "/hret/match"      $ "match"

completionPage :: ServerPart Response
completionPage = msum [ viewForm, processForm ] where

    title = "Higher-Ranked Exception Types: Completion"

    viewForm :: ServerPart Response
    viewForm = expressionForm title "/hret/completion"

    processForm :: ServerPart Response
    processForm = do
        method POST

        ty :: An.Ty <- read . unpack <$> lookText "expr"
        
        let (dExnTy, exnTy, exn, env) = An.complete' [] ty
        
        ok $ template title $ do
            H.h2 "Underlying type"
            H.p $ mathjax ty
            
            H.h2 "Completed type"
            H.p $ toHtml $
                "\\[" ++ latex exnTy ++ "\\ \\&\\ " ++ latex exn ++ "\\]"            
            H.h3 "Environment"
            H.p $ envAsTable env
            
            H.h2 "Derivation tree"
            H.p $ toHtml dExnTy
            
inferencePage :: ServerPart Response
inferencePage = msum [ viewForm, processForm ] where

    title = "Higher-Ranked Exception Types: Inference"

    viewForm :: ServerPart Response
    viewForm = expressionForm title "/hret/inference"

    processForm :: ServerPart Response
    processForm = do
        method POST

        expr :: An.Expr <- read . unpack <$> lookText "expr"

        let (re, exnTy, exn, cs, kenv) = An.evalFresh (An.reconstruct [] [] expr) 1

        ok $ template title $ do
            H.p "Need to solve once more at top-level."
        
            H.h2 "Expression"
            H.p $ mathjax expr

            H.h2 "Exception Type"
            H.p $ toHtml $
                "\\[" ++ latex exnTy ++ "\\ \\&\\ " ++ show exn ++ "\\]"  
            H.h3 "Constraints"
            H.p $ mathjax cs
            H.h3 "Kind environment"
            H.p $ envAsTable kenv

            H.h2 "Derivation Tree"
            H.p $ toHtml re
            
            H.h2 "Algorithm"
            mapM_ H.p (An.reconstructHtml re)
