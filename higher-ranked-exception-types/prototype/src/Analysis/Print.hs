{-# LANGUAGE OverloadedStrings #-}

module Analysis.Print (
    Latex(..),
    Color(..),
    ColorEnv,
    color,
    colorByNumber,
    mathjax,
    mathjax',
    envAsTable,
    derive
) where

import Control.Monad
import Data.List

import Data.Text (Text)
import Text.Blaze.Html5 (ToMarkup, Html, (!), toHtml)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import Analysis.Names

-- | LaTeX

class Latex a where
    latex      ::             a -> String
    latexColor :: ColorEnv -> a -> String

instance Latex () where
    latex () = "\\diamond"

instance Latex a => Latex [a] where
    latex           env = "[" ++ intercalate "," (map  latex            env) ++ "]"
    latexColor cenv env = "[" ++ intercalate "," (map (latexColor cenv) env) ++ "]"

-- * Colored LaTeX

data Color = Red | Green | Blue | Purple | Orange

color :: Color -> String -> String
color c xs = "\\color{" ++ f c ++ "}" ++ xs ++ "\\color{black}"
    where f Red    = "red"
          f Green  = "green"
          f Blue   = "blue"
          f Purple = "purple"
          f Orange = "orange"
          
type ColorEnv = [(Name, Color)]

colorByNumber :: ColorEnv -> Name -> String -> String
colorByNumber cenv x
    | Just c <- lookup x cenv = color c
    | otherwise = error "colorByNumber"

-- | HTML

mathjax, mathjax' :: Latex a => a -> Html
mathjax  x = toHtml $ "\\[" ++ latex x ++ "\\]"
mathjax' x = toHtml $ "$"   ++ latex x ++ "$"

envAsTable :: (Show a, Latex b) => [(a,b)] -> H.Html
envAsTable env = do
    H.table $ do
        forM_ env $ \(k,v) -> do
            H.tr $ do
                H.td $ toHtml $ show k
                H.td $ mathjax v

derive :: Text -> [H.Html] -> H.Html -> H.Html
derive rule premises conclusion
    = let colSpan = H.toValue (show (length premises `max` 1)) in
        H.table ! A.style "margin-left: auto; margin-right: auto;" $ do
            H.tr $ do
                if null premises then
                    H.td ""
                else
                    mapM_ (H.td ! A.style "vertical-align: bottom") premises
                H.td ""
            H.tr $ do
                H.td ! A.colspan colSpan $ H.hr
                H.td $ H.toHtml rule
            H.tr $ do
                H.td ! A.colspan colSpan ! A.style "padding: 0em; text-align: center;" $ do
                    conclusion
