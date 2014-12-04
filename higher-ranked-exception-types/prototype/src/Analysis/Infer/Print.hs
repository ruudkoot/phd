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
reconstructHtml (ReconstructAbs env kenv tm@(Abs x ty tm') co@(_, t1', exn1, kenv1) env' re@(_, t2', exn2, c1, kenv2) v exn2' t' e result)
    = (return $ H.table $ do
        H.tr $ H.td ! A.colspan "3" $ H.toHtml $
            htmlHeader env kenv tm
        H.tr $ do
            H.td $ H.b $ "let"
            H.td $ "(t1', exn1, kenv1)"
            H.td $ "$\\leftarrow$ complete [] ty"
        rowRes $ htmlComplete t1' exn1 kenv1
        H.tr $ do
            H.td $ ""
            H.td $ "env'"
            H.td $ H.toHtml $ "$\\leftarrow " ++ latex env' ++ "$"
        H.tr $ do
            H.td $ ""
            H.td $ "(t2', exn2, c1, kenv2)"
            H.td $ "$\\leftarrow$ reconstruct env' (kenv1 ++ kenv) tm'"
        rowRes $ htmlReconstruct re
        H.tr $ do
            H.td $ ""
            H.td $ "v"
            H.td $ H.toHtml $ "$\\leftarrow " ++ show v ++ "$"
        H.tr $ do
            H.td $ ""
            H.td $ "exn2'"
            H.td $ "$\\leftarrow$ solve (kenv1 ++ [(exn1,EXN)] ++ kenv) c1 v exn2"
        H.tr $ do
            H.td $ ""
            H.td $ ""
            H.td $ mathjax' exn2'
        H.tr $ do
            H.td $ ""
            H.td $ "t'"
            H.td $ "$\\leftarrow$ C.forallFromEnv kenv1 (ExnArr t1' (ExnVar exn1) t2' exn2')"
        H.tr $ do
            H.td $ ""
            H.td $ ""
            H.td $ mathjax' t'
        htmlFresh "e"
        H.tr $ do
            H.td $ H.b $ "in"
            H.td ! A.colspan "2" $ htmlResult result
      ) ++ recurse [re]
reconstructHtml (ReconstructApp env kenv tm re1 re2 ins subst e c result)
    = (return $ H.table $ do
        H.tr $ H.td ! A.colspan "3" $ H.toHtml $
            htmlHeader env kenv tm
        H.tr $ do
            H.td $ H.b $ "let"
            H.td $ "(t1, exn1, c1, kenv1)"
            H.td $ "$\\leftarrow$ reconstruct env kenv e1"
        rowRes $ htmlReconstruct re1
        H.tr $ do
            H.td $ ""
            H.td $ "(t2, exn2, c2, kenv2)"
            H.td $ "$\\leftarrow$ reconstruct env kenv e2"
        rowRes $ htmlReconstruct re2
        H.tr $ do
            H.td $ ""
            H.td $ "(ExnArr t2' (ExnVar exn2') t' exn', kenv')"
            H.td $ "<- instantiate t1"
        rowRes $ htmlInstantiate ins
        H.tr $ do
            H.td $ ""
            H.td $ "subst"
            H.td $ "= [(exn2', ExnVar exn2)] <.> match [] t2 t2'"
        rowRes $ mathjax' subst
        htmlFresh "e"
        H.tr $ do
            H.td $ ""
            H.td $ "c"
            H.td $ "[substExn' subst exn' :<: e, ExnVar exn1 :<: e] ++ c1 ++ c2"
        H.tr $ do
            H.td $ H.b $ "in"
            H.td ! A.colspan "2" $ htmlResult result
      ) ++ recurse [re1, re2]
reconstructHtml _ = ["reconstruct"]


recurse :: [Reconstruct'] -> [H.Html]
recurse = concatMap (\(re,_,_,_,_) -> reconstructHtml re)

rowRes html = H.tr $ do
                H.td $ ""
                H.td $ ""
                H.td $ html

htmlHeader env kenv tm
    = "reconstruct $\\Gamma=" ++ latex env ++ "$ $\\Delta=" ++ latex kenv
            ++ "$ $" ++ latex tm ++ "$"

htmlFresh name
    = H.tr $ do
        H.td $ ""
        H.td $ name
        H.td $ H.b $ "fresh"

htmlReconstruct (re, t, exn, c, kenv)
    = H.toHtml $ "$(" ++ latex t ++ ", e_{" ++ show exn ++ "}," ++ latex c
                    ++ "," ++ latex kenv ++ ")$"

htmlComplete exnTy exn kenv
    = H.toHtml $ "$(" ++ latex exnTy ++ ", " ++ latex exn ++ ", "
                    ++ latex kenv ++ ")$"

htmlInstantiate (exnTy, kenv)
    = H.toHtml $ "$(" ++ latex exnTy ++ "," ++ latex kenv ++ ")$"

htmlResult (exnTy, exn, c, kenv)
    = H.toHtml $ "$(" ++ latex exnTy ++ ", e_{" ++ show exn ++ "}, " ++ latex c
                    ++ ", " ++ latex kenv ++ ")$"
