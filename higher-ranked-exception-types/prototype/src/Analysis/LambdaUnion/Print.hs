{-# LANGUAGE OverloadedStrings #-}

module Analysis.LambdaUnion.Print where

import Text.Blaze.Html5 (ToMarkup)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import Analysis.Print

import Analysis.LambdaUnion.Syntax
import Analysis.LambdaUnion.Reduce

instance Latex Sort where
    latex C           = "C"
    latex (s1 :=> s2) = "(" ++ latex s1 ++ "\\Rightarrow " ++ latex s2 ++ ")"

instance Latex a => Latex (Tm a) where
    latex (Var   x    )
        = "x_{" ++ show x ++ "}"
    latex (Con   c    )
        = "\\{" ++ latex c ++ "\\}"
    latex (Abs   x s e)
        = "(\\lambda x_{" ++ show x ++ "}:" ++ latex s ++ "." ++ latex e ++ ")"
    latex (App   e1 e2) 
        = "(" ++ latex e1 ++ "\\ " ++ latex e2 ++ ")"
    latex (Union e1 e2)
        = "(" ++ latex e1 ++ "\\cup" ++ latex e2 ++ ")"
    latex (Empty      )
        = "\\emptyset"

ltxNormalize :: Latex a => Tm a -> Tm a -> H.Html
ltxNormalize tm tm'
    = H.toHtml $ "\\[" ++ latex tm ++ " \\longrightarrow " ++ latex tm' ++ "\\]"

instance Latex a => ToMarkup (NormalizeTm a) where
    toMarkup (NormalizeVar tm tm')
        = derive Black "Var" [] (ltxNormalize tm tm')
    toMarkup (NormalizeCon tm tm')
        = derive Black "Con" [] (ltxNormalize tm tm')
    toMarkup (NormalizeAbs dtm tm tm')
        = derive Black "Abs" [H.toMarkup dtm] (ltxNormalize tm tm')
    toMarkup (NormalizeApp1 dtm1 dtm2 tm tm')
        = derive Black "App1" (map H.toMarkup [dtm1, dtm2]) (ltxNormalize tm tm')
    toMarkup (NormalizeApp2 dtm1 dtm2 dtm3 tm tm')
        = derive Black "App2" (map H.toMarkup [dtm1, dtm2, dtm3]) (ltxNormalize tm tm')
    toMarkup (NormalizeUnion1 dtm1 dtm2 tm tm')
        = derive Black "Union1" (map H.toMarkup [dtm1, dtm2]) (ltxNormalize tm tm')
    toMarkup (NormalizeUnion2 dtm1 dtm2 dtm3 tm tm')
        = derive Black "Union2" (map H.toMarkup [dtm1, dtm2, dtm3]) (ltxNormalize tm tm')
    toMarkup (NormalizeEmpty tm tm')
        = derive Black "Empty" [] (ltxNormalize tm tm')
