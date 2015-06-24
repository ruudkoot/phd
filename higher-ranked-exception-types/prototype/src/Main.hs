{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, ViewPatterns #-}

module Main where

import Control.Applicative ((<$>), optional)
import Control.Monad (forM_, replicateM_, when)
import Data.Maybe (fromJust, fromMaybe)
import Data.Text (Text)
import Data.Text.Lazy (unpack)
import Happstack.Lite
import Text.Blaze.Html5 (Html, (!), a, form, input, p, toHtml, label, textarea, br)
import Text.Blaze.Html5.Attributes (action, enctype, href, name, size, type_, value)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import qualified Analysis.Names       as An
import qualified Analysis.Common      as An
import qualified Analysis.Completion  as An
import qualified Analysis.Infer       as An
import qualified Analysis.Infer.Print as An
import qualified Analysis.Infer.Match as An
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
    , dir "hret" $ dir "match"      $ matchPage
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
                  "  \"HTML-CSS\": { styles: { '.MathJax_Display': { \"margin\": 0 }}},",
                  "  TeX: {extensions: [\"AMSmath.js\", \"AMSsymbols.js\", \"color.js\"]}",
                  "});"
              ]
            H.script ! type_ "text/javascript"
                     ! A.src "/static/mathjax/MathJax.js" $ ""
            H.script ! type_ "text/javascript"
                     ! A.src "/static/d3/3.4.13/d3.min.js" $ ""
        H.body $ do
            H.h1 title
            body
            replicateM_ 10 br
            p $ a ! href "/" $ "back home"

fileServing :: ServerPart Response
fileServing =
    serveDirectory DisableBrowsing [] "static"

homePage :: ServerPart Response
homePage = ok $ template "Higher-Ranked Exception Types" $ do
    H.p $ a ! href "/lambda-union" $ "lambda-union"
    H.p $ a ! href "/hret"         $ "higher-ranked exception types"

expressionForm :: Text -> [Text] -> H.AttributeValue -> [(String,String,Html)] -> ServerPart Response
expressionForm title notes url examples = do
    method GET
    ok $ template title $ do
        form ! action url
             ! enctype "multipart/form-data" ! A.method "POST" $ do
            textarea ! A.id "expr" ! name "expr" ! A.cols "80" $ ""
            input ! type_ "submit"
        when (not (null examples)) $ do
            H.h2 "Examples"
            H.ol $ forM_ examples $ \(label,code,pretty) -> do
                H.li $ H.a ! A.href "javascript:void(0);" ! A.onclick (H.toValue $ "$('#expr').val('" ++ code ++ "');") $ do
                    toHtml $ label ++ " = "
                    pretty

expressionForm3 :: Text -> H.AttributeValue -> ServerPart Response
expressionForm3 title url = do
    method GET
    ok $ template title $ do
        form ! action url
             ! enctype "multipart/form-data" ! A.method "POST" $ do
            textarea ! A.id "env" ! name "env" ! A.cols "80" $ "[]"
            textarea ! A.id "ty1" ! name "ty1" ! A.cols "80" $ "ExnBool"
            textarea ! A.id "ty2" ! name "ty2" ! A.cols "80" $ "ExnBool"
            input ! type_ "submit"

lambdaUnion :: ServerPart Response
lambdaUnion = msum [ viewForm, processForm ] where

    viewForm :: ServerPart Response
    viewForm = expressionForm "lambda-union" [] "/lambda-union" []

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
    H.p $ a ! href "/hret/solve"      $ "solve"
    H.p $ a ! href "/hret/match"      $ "match"
    H.p $ a ! href "/hret/join"       $ "join"

completionPage :: ServerPart Response
completionPage = msum [ viewForm, processForm ] where

    title = "Higher-Ranked Exception Types: Completion"

    viewForm :: ServerPart Response
    viewForm = expressionForm title [] "/hret/completion" []

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

    notes = ["pretty print the examples"
            ,"check 'hcompose compose'"
            ]

    viewForm :: ServerPart Response
    viewForm = expressionForm title notes "/hret/inference" An.inferenceExamples

    processForm :: ServerPart Response
    processForm = do
        method POST

        expr :: An.Expr <- read . unpack <$> lookText "expr"

        let ((dt,de,re), elabTm, exnTy, exn)
                = An.evalFresh (An.reconstruct [] [] expr) 1
        let elabTy
                = An.evalFresh (An.checkElabTm' [] [] elabTm) 666

        ok $ template title $ do

            H.h2 "Expression"
            H.p $ mathjax expr
            H.h3 $ "Type"
            H.p $ mathjax $ fromJust $ An.checkExpr [] expr

            H.h2 "Elaborated expression"
            H.p $ mathjax elabTm
            --H.p $ "DISABLED!"
            
            H.h3 "Exception type"
            H.p $ toHtml $
                case elabTy of
                    Just (ty, ann) -> if An.exnTyEq [] ty exnTy && An.exnEq [] ann exn then "\\[\\color{green}" ++ latex ty ++ "\\ \\&\\ " ++ latex ann ++ "\\color{black}\\]" else error "inferred type does not match type of elaborated expression"
            
            H.h2 $ "Inferred exception type"
            H.p $ toHtml $
                "\\[" ++ An.latexCheck [] exnTy ++ "\\ \\&\\ "
                ++ latex exn ++ "\\]"

            H.h2 "Derivation tree"
            H.h3 "Declarative type system"
            H.p $ toHtml dt
            H.h3 "Syntax-directed elaboration"
            H.p $ toHtml de
            
            H.h2 "Algorithm"
            mapM_ H.p (An.reconstructHtml re)

matchPage :: ServerPart Response
matchPage = msum [ viewForm, processForm ] where

    title = "Higher-Ranked Exception Types: Matching"

    viewForm :: ServerPart Response
    viewForm = expressionForm3 title "/hret/match"

    processForm :: ServerPart Response
    processForm = do
        method POST

        env :: An.Env   <- read . unpack <$> lookText "env"
        ty1 :: An.ExnTy <- read . unpack <$> lookText "ty1"
        ty2 :: An.ExnTy <- read . unpack <$> lookText "ty2"

        let ({-ma, -}subst) = An.evalFresh (An.match env ty1 ty2) 1

        ok $ template title $ do
            H.h2 "Expression"
            H.p $ mathjax env
            H.p $ mathjax ty1
            H.p $ mathjax ty2

            H.h2 "Substitution"
            H.p $ mathjax subst
{-
            H.h2 "Derivation Tree"
            H.p $ toHtml ma
-}
