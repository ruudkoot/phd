{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

module Analysis.Infer.Print (
    reconstructHtml,
    latexCheck
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
    toMarkup (ReconstructAbs   env kenv tm _ _ (re,_,_,_,_) _ _ _ _ _ _)
        = derive "R-Abs" (map H.toMarkup [re]) ""
    toMarkup (ReconstructApp   env kenv tm (re1,_,_,_,_) (re2,_,_,_,_) _ _ _ _ _ _)
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
    toMarkup (ReconstructCons  env kenv tm (re1,_,_,_,_) (re2,_,_,_,_) _ _ _ _)
        = derive "R-Cons" (map H.toMarkup [re1, re2]) ""
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
        htmlResult kenv result
      )
reconstructHtml (ReconstructAbs env kenv tm@(Abs x ty tm') co@(_, t1', exn1, kenv1) env' re@(_, t2', exn2, c1, kenv2) v kenv' exn2' t' e result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "complete [] ty"
        htmlComplete t1' exn1 kenv1
        H.tr $ do
            H.td $ ""
            H.td $ "env'"
            H.td ! A.colspan "3" $ H.toHtml $ "$\\leftarrow " ++ latex env' ++ "$"
        htmlDo "reconstruct env' (kenv1 ++ kenv) tm'"
        htmlReconstruct (kenv' ++ kenv2 ++ kenv) re "XXX"  -- FIXME: (t2', exn2, c1, kenv2)
        trAssign "v" (show v)
        H.tr $ do
            H.td $ ""
            H.td $ "kenv'"
            H.td ! A.colspan "3" $ H.toHtml $ "$\\leftarrow " ++ latex kenv' ++ "$"
        htmlDo "solve (kenv1 ++ [(exn1,EXN)] ++ kenv) c1 v exn2"
        trAssign "exn2'" (latex exn2')
        htmlDo "forallFromEnv kenv1 (ExnArr t1' (ExnVar exn1) t2' exn2')"
        trAssign "t'" (latex t')
        htmlFresh e
        htmlResult kenv result
      ) ++ recurse [re]
reconstructHtml (ReconstructApp env kenv tm re1@(_,_,_,_,kenv1) re2@(_, t2, exn2, c2, kenv2) ins@(ExnArr t2' (ExnVar exn2') t' exn', kenv') subst' subst e c result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct (kenv1 ++ kenv) re1 "1"
        htmlDo "reconstruct env kenv e2"
        htmlReconstruct (kenv2 ++ kenv) re2 "2"
        htmlDo "instantiate t1"
        htmlInstantiate ins
        H.tr $ do
            H.td $ ""
            H.td $ "subst"
            H.td ! A.colspan "3" $ H.toHtml $ "= [(exn2', ExnVar exn2)] <.> match [] $" ++ latex t2 ++ "$ $" ++ latex t2' ++ "$"
        -- rowRes $ mathjax' subst'
        rowRes $ mathjax' subst
        htmlFresh e
        H.tr $ do
            H.td $ ""
            H.td $ "c"
            H.td ! A.colspan "3" $ "[substExn' subst exn' :<: e, ExnVar exn1 :<: e] ++ c1 ++ c2"
        htmlResult kenv result
      ) ++ recurse [re1, re2]
reconstructHtml (ReconstructCon env kenv tm e result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlFresh e
        htmlResult kenv result
      )
reconstructHtml (ReconstructCrash env kenv tm co@(_, t1', exn1, kenv1) result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "complete [] ty"
        htmlComplete t1' exn1 kenv1
        htmlResult kenv result
      )
reconstructHtml (ReconstructSeq env kenv tm re1@(_,_,_,_,kenv1) re2@(_,_,_,_,kenv2) e result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct (kenv1 ++ kenv) re1 "1"
        htmlDo "reconstruct env kenv e2"
        htmlReconstruct (kenv2 ++ kenv) re2 "2"
        htmlFresh e
        htmlResult kenv result
      ) ++ recurse [re1, re2]
reconstructHtml (ReconstructFix env kenv tm re@(_,_,_,_,kenv1) ins subst1 subst2 e c result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct (kenv1 ++ kenv) re "1"
        htmlDo "instantiate t1"
        htmlInstantiate ins
        H.tr $ do
            H.td $ ""
            H.td $ "subst1"
            H.td ! A.colspan "3" $ "= match [] t'' t'"
        rowRes $ mathjax' subst1
        H.tr $ do
            H.td $ ""
            H.td $ "subst2"
            H.td ! A.colspan "3" $ "= [(exn', substExn' subst1 exn'')]"
        rowRes $ mathjax' subst2
        htmlFresh e
        H.tr $ do
            H.td $ ""
            H.td $ "c"
            H.td ! A.colspan "3" $ "[substExn' (subst2 <.> subst1) exn'' :<: e] ++ c1"
        rowRes $ mathjax' c
        htmlResult kenv result
      ) ++ recurse [re]
reconstructHtml (ReconstructNil env kenv tm co@(_, ty', exn1, kenv1) exn2 result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "complete [] ty"
        htmlComplete ty' exn1 kenv1
        htmlFresh exn2
        htmlResult kenv result
      )
reconstructHtml (ReconstructCons env kenv tm re1@(_,_,_,_,kenv1) re2@(_,_,_,_,kenv2) t ex1 ex2 result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct (kenv1 ++ kenv) re1 "1"
        htmlDo "reconstruct env kenv e2"
        htmlReconstruct (kenv2 ++ kenv) re2 "2"
        H.tr $ do
            H.td $ ""
            H.td $ "t"
            H.td ! A.colspan "3" $ "= join t1 t2"
        rowRes $ mathjax' t
        htmlFresh ex1
        htmlFresh ex2
        htmlResult kenv result
      ) ++ recurse [re1, re2]
reconstructHtml (ReconstructCase env kenv tm re1@(_,_,_,_,kenv1) re2@(_,_,_,_,kenv2) env' re3@(_,_,_,_,kenv3) t exn c result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct (kenv1 ++ kenv) re1 "1"
        htmlDo "reconstruct env kenv e2"
        htmlReconstruct (kenv2 ++ kenv) re2 "2"
        H.tr $ do
            H.td $ ""
            H.td $ "env'"
            H.td ! A.colspan "3" $ "= (x1, (t1, exn1')) : (x2, (ExnList t1 exn1', ExnVar exn1)) : env"
        htmlDo "reconstruct env (kenv1 ++ kenv) e3"
        htmlReconstruct (kenv3 ++ kenv2 ++ kenv1 ++ kenv) re3 "3"
        rowRes $ mathjax' env'
        H.tr $ do
            H.td $ ""
            H.td $ "t"
            H.td ! A.colspan "3" $ "= join t1 t2"
        rowRes $ mathjax' t
        htmlFresh exn
        H.tr $ do
            H.td $ ""
            H.td $ "c"
            H.td ! A.colspan "3" $ "[ExnVar exn1 :<: exn, ExnVar exn2 :<: exn, ExnVar exn3 :<: exn] ++ c1 ++ c2 ++ c3"
        htmlResult kenv result
      ) ++ recurse [re1, re2, re3]


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

trCode :: String -> H.Html
trCode expr = do
    H.tr $ do
        H.td $ ""
        H.td $ ""
        H.td $ ""
        H.td $ "$\\leftarrow$"
        H.td $ H.code $ H.toHtml $ expr


htmlHeader env kenv tm
    = H.tr $ H.td ! A.colspan "5" $ H.toHtml $
        "reconstruct $\\Gamma=" ++ latex env ++ "$ $\\Delta=" ++ latex kenv
            ++ "$ $" ++ latex tm ++ "$"

htmlFresh name
    = H.tr $ do
        H.td $ ""
        H.td $ H.toHtml $ "$e_{" ++ show name ++ "}$"
        H.td ! A.colspan "3" $ H.b $ "fresh"

htmlReconstruct :: KindEnv -> Reconstruct' -> String -> H.Html
htmlReconstruct delta (re, t, exn, c, kenv) n
    = do trAssign ("t_{" ++ n ++ "}")    (latexCheck delta t)
         trAssign ("exn_{" ++ n ++ "}")  ("e_{" ++ show exn ++ "}")
         trAssign ("c_{" ++ n ++ "}")    (latex c)
         trAssign ("kenv_{" ++ n ++ "}") (latex kenv)

htmlComplete exnTy exn kenv
    = do trAssign "t_1'"   (latex exnTy)
         trAssign "exn_1"  (latex exn)
         trAssign "kenv_1" (latex kenv)

htmlInstantiate (exnTy@(ExnArr t2' (ExnVar exn2') t' exn'), kenv)   -- FIXME: local variable naming...
    = do trAssign "t_2'\\{\\chi_2'\\} \\to t'\\{\\chi'\\}" (latex exnTy)
         trAssign "t_2'"     (latex t2')
         trCode              (show t2')
         trAssign "t'"       (latex t')
         trCode              (show  t')
         trAssign "\\chi_2'" (show exn2')
         trAssign "\\chi'"   (latex exn')
         trAssign "kenv'"                                  (latex kenv)

htmlDo thing = H.tr $ do
            H.td $ H.b "do"
            H.td ! A.colspan "4" $ thing

htmlResult kenv0 (exnTy, exn, c, kenv)
    = do H.tr $ do
            H.td $ H.b "in"
            H.td $ "$\\tau$"
            H.td $ "="
            H.td ! A.colspan "3" $ H.toHtml $
                "$" ++ (latexCheck (kenv ++ kenv0) exnTy) ++ "$"
         H.tr $ do
            H.td $ H.b ""
            H.td $ ""
            H.td $ "="
            H.td ! A.colspan "3" $ H.toHtml $
                "$" ++ (latexCheck (kenv ++ kenv0) (simplifyExnTy (kenv ++ kenv0) exnTy)) ++ "$"
         H.tr $ do
            H.td $ ""
            H.td $ "$\\chi$"
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
            
latexCheck :: KindEnv -> ExnTy -> String
latexCheck kenv t
    | checkExnTy kenv t = "\\color{green}" ++ latex t
    | otherwise         = "\\color{red}"   ++ latex t
