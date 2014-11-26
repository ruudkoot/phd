{-# LANGUAGE OverloadedStrings #-}

module Analysis.Print (
    Latex(..),
    derive
) where

import Data.List

import Data.Text (Text)
import Text.Blaze.Html5 (ToMarkup, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

-- | LaTeX

class Latex a where
    latex :: a -> String

instance Latex () where
    latex () = "\\diamond"

instance Latex a => Latex [a] where
    latex env = "[" ++ intercalate "," (map latex env) ++ "]"
    
-- | HTML

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
                H.td ! A.colspan colSpan ! A.style "padding: 0px" $ do
                    conclusion
