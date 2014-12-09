{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

module Analysis.Infer.Print (
    reconstructHtml
) where

import Text.Blaze.Html5 (ToMarkup)
import Text.Blaze.Html5 ((!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import Analysis.Names
import Analysis.Common
import Analysis.Print

import Analysis.Infer.Types

-- | Types

instance Latex (Name, (ExnTy, Exn)) where
    latex (show -> e, (latex -> ty, latex -> exn))
        = "e_{" ++ e ++ "} : " ++ ty ++ "\\ \\&\\ " ++ exn

instance Latex Constr where
    latex (exn :<: e) = latex exn ++ " \\sqsubseteq e_{" ++ show e ++ "}"

instance Latex (Name, Exn) where
    latex (show -> e, latex -> exn)
        = "e_{" ++ e ++ "} \\mapsto " ++ exn

-- | Reconstruction

instance ToMarkup Reconstruct where
    toMarkup (ReconstructVar   env kenv tm _ _ _ _)
        = derive "R-Var" [] ""
    toMarkup (ReconstructAbs   env kenv tm _ _ (re,_,_,_,_) _ _ _ _ _)
        = derive "R-Abs" (map H.toMarkup [re]) ""
    toMarkup (ReconstructApp   env kenv tm (re1,_,_,_,_) (re2,_,_,_,_) _ _ _ _ _)
        = derive "R-App" (map H.toMarkup [re1, re2]) ""
    toMarkup (ReconstructCon   env kenv tm _ _)
        = derive "R-Con" [] ""
    toMarkup (ReconstructCrash env kenv tm _ _)
        = derive "R-Crash" [] ""
    toMarkup (ReconstructSeq   env kenv tm (re1,_,_,_,_) (re2,_,_,_,_) _ _)
        = derive "R-Seq" (map H.toMarkup [re1, re2]) ""
    toMarkup (ReconstructFix   env kenv tm (re,_,_,_,_) _ _ _ _ _ _)
        = derive "R-Fix" (map H.toMarkup [re]) ""
    toMarkup (ReconstructNil   env kenv tm _ _ _)
        = derive "R-Nil" [] ""
    toMarkup (ReconstructCons  env kenv tm _ _ _ _ _ _)
        = derive "R-Cons" [] ""
    toMarkup (ReconstructCase  env kenv tm 
                    (re1,_,_,_,_) (re2,_,_,_,_) _  (re3,_,_,_,_) _ _ _ _)
        = derive "R-Case" (map H.toMarkup [re1, re2, re3]) ""

reconstructHtml :: Reconstruct -> [H.Html]
reconstructHtml (ReconstructVar env kenv tm t exn e result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "lookup x env"
        trAssign "t"   (latex t)
        trAssign "exn" (latex exn)
        htmlFresh e
        htmlResult result
      )
reconstructHtml (ReconstructAbs env kenv tm@(Abs x ty tm') co@(_, t1', exn1, kenv1) env' re@(_, t2', exn2, c1, kenv2) v exn2' t' e result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "complete [] ty"
        htmlComplete t1' exn1 kenv1
        H.tr $ do
            H.td $ ""
            H.td $ "env'"
            H.td ! A.colspan "3" $ H.toHtml $ "$\\leftarrow " ++ latex env' ++ "$"
        htmlDo "reconstruct env' (kenv1 ++ kenv) tm'"
        htmlReconstruct re "XXX"                -- FIXME: (t2', exn2, c1, kenv2)
        trAssign "v" (show v)
        htmlDo "solve (kenv1 ++ [(exn1,EXN)] ++ kenv) c1 v exn2"
        trAssign "exn2'" (show exn2')
        htmlDo "C.forallFromEnv kenv1 (ExnArr t1' (ExnVar exn1) t2' exn2')"
        trAssign "t'" (latex t')
        htmlFresh e
        htmlResult result
      ) ++ recurse [re]
reconstructHtml (ReconstructApp env kenv tm re1 re2 ins subst e c result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct re1 "1"
        htmlDo "reconstruct env kenv e2"
        htmlReconstruct re2 "2"
        htmlDo "instantiate t1"
        htmlInstantiate ins
        H.tr $ do
            H.td $ ""
            H.td $ "subst"
            H.td ! A.colspan "3" $ "= [(exn2', ExnVar exn2)] <.> match [] t2 t2'"
        rowRes $ mathjax' subst
        htmlFresh e
        H.tr $ do
            H.td $ ""
            H.td $ "c"
            H.td ! A.colspan "3" $ "[substExn' subst exn' :<: e, ExnVar exn1 :<: e] ++ c1 ++ c2"
        htmlResult result
      ) ++ recurse [re1, re2]
reconstructHtml _ = ["reconstruct"]


recurse :: [Reconstruct'] -> [H.Html]
recurse = concatMap (\(re,_,_,_,_) -> reconstructHtml re)

rowRes html = H.tr $ do
                H.td $ ""
                H.td $ ""
                H.td ! A.colspan "3" $ html

trAssign :: String -> String -> H.Html
trAssign name expr = do
    H.tr $ do
        H.td $ ""
        H.td $ ""
        H.td $ H.toHtml $ "$" ++ name ++ "$"
        H.td $ "$\\leftarrow$"
        H.td $ H.toHtml $ "$" ++ expr ++ "$"

htmlHeader env kenv tm
    = H.tr $ H.td ! A.colspan "5" $ H.toHtml $
        "reconstruct $\\Gamma=" ++ latex env ++ "$ $\\Delta=" ++ latex kenv
            ++ "$ $" ++ latex tm ++ "$"

htmlFresh name
    = H.tr $ do
        H.td $ ""
        H.td $ H.toHtml $ "$e_{" ++ show name ++ "}$"
        H.td ! A.colspan "3" $ H.b $ "fresh"

htmlReconstruct :: Reconstruct' -> String -> H.Html
htmlReconstruct (re, t, exn, c, kenv) n
    = do trAssign ("t_{" ++ n ++ "}")    (latex t)
         trAssign ("exn_{" ++ n ++ "}")  ("e_{" ++ show exn ++ "}")
         trAssign ("c_{" ++ n ++ "}")    (latex c)
         trAssign ("kenv_{" ++ n ++ "}") (latex kenv)

htmlComplete exnTy exn kenv
    = do trAssign "t_1'"   (latex exnTy)
         trAssign "exn_1"  (latex exn)
         trAssign "kenv_1" (latex kenv)

htmlInstantiate (exnTy, kenv)
    = do trAssign "t_2'\\{\\chi_2'\\} \\to t'\\{\\chi'\\}" (latex exnTy)
         trAssign "kenv'"                                  (latex kenv)

htmlDo thing = H.tr $ do
            H.td $ H.b "do"
            H.td ! A.colspan "4" $ thing

htmlResult (exnTy, exn, c, kenv)
    = do H.tr $ do
            H.td $ H.b "in"
            H.td $ "$t$"
            H.td $ "="
            H.td ! A.colspan "3" $ mathjax' exnTy
         H.tr $ do
            H.td $ ""
            H.td $ "$e$"
            H.td $ "="
            H.td ! A.colspan "3" $ H.toHtml $ "$e_{" ++ show exn ++ "}$"
         H.tr $ do
            H.td $ ""
            H.td $ "$C$"
            H.td $ "="
            H.td ! A.colspan "3" $ mathjax' c
         H.tr $ do
            H.td $ ""
            H.td $ "$\\Delta$"
            H.td $ "="
            H.td ! A.colspan "3" $ mathjax' kenv
