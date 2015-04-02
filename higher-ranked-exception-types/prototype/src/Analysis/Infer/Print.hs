{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

module Analysis.Infer.Print (
    reconstructHtml,
    latexCheck
) where

import Control.Monad (forM)

import           Text.Blaze.Html5 (ToMarkup)
import           Text.Blaze.Html5 ((!))
import qualified Text.Blaze.Html5            as H
import qualified Text.Blaze.Html5.Attributes as A

import Analysis.Names
import Analysis.Common
import Analysis.Print

import Analysis.Infer.Types

-- | Types

instance Latex (Name, (ExnTy, Exn)) where
    latex (show -> e, (latex -> ty, latex -> exn))
        = "e_{" ++ e ++ "} : " ++ ty ++ "\\ \\&\\ " ++ exn

instance Latex (Name, Exn) where
    latex (show -> e, latex -> exn)
        = "e_{" ++ e ++ "} \\mapsto " ++ exn

-- | Elaboration

instance ToMarkup DerivType where
    toMarkup (TypeVar jt)
        = derive "T-Var" [] (judgeType jt)
    toMarkup (TypeCon jt)
        = derive "T-Con" [] (judgeType jt)
    toMarkup (TypeCrash jt)
        = derive "T-Crash" [] (judgeType jt)
    toMarkup (TypeAbs dt jt)
        = derive "T-Abs" [H.toMarkup dt] (judgeType jt)
    toMarkup (TypeAnnAbs dt jt)
        = derive "T-AnnAbs" [H.toMarkup dt] (judgeType jt)
    toMarkup (TypeApp dt1 dt2 jt)
        = derive "T-App" (map H.toMarkup [dt1, dt2]) (judgeType jt)
    toMarkup (TypeAnnApp jk dt jt)
        = derive "T-AnnApp" [H.toMarkup dt, judgeKind jk] (judgeType jt)
    toMarkup (TypeFix dt jt)
        = derive "T-Fix" [H.toMarkup dt] (judgeType jt)
    toMarkup (TypeOp dt1 dt2 jt)
        = derive "T-Op" (map H.toMarkup [dt1, dt2]) (judgeType jt)
    toMarkup (TypeSeq dt1 dt2 jt)
        = derive "T-Seq" (map H.toMarkup [dt1, dt2]) (judgeType jt)
    toMarkup (TypeIf dt1 dt2 dt3 jt)
        = derive "T-If" (map H.toMarkup [dt1, dt2, dt3]) (judgeType jt)
    toMarkup (TypeNil jt)
        = derive "T-Nil" [] (judgeType jt)
    toMarkup (TypeCons dt1 dt2 jt)
        = derive "T-Cons" (map H.toMarkup [dt1, dt2]) (judgeType jt)
    toMarkup (TypeCase jse dt1 dt2 dt3 jt)
        = derive "T-Case" (map H.toMarkup [dt1, dt2, dt3] ++ [judgeSubEff jse])
            (judgeType jt)
    toMarkup (TypeSub jst jse dt jt)
        = derive "T-Sub" [H.toMarkup dt, judgeSubTy jst, judgeSubEff jse]
            (judgeType jt)

instance ToMarkup DerivElab where
    toMarkup (ElabVar je)
        = derive "TE-Var" [] (judgeElab je)
    toMarkup (ElabCon je)
        = derive "TE-Con" [] (judgeElab je)
    toMarkup (ElabCrash je)
        = derive "TE-Crash" [] (judgeElab je)
    toMarkup (ElabAbs jt jk de je)
        = derive "TE-Abs" (map H.toMarkup [de] ++ [judgeKind jk] ++ [judgeTyWff jt])
            (judgeElab je)
    toMarkup (ElabApp jst jse jks de1 de2 je)
        = derive "TE-App" (map H.toMarkup [de1, de2] ++ map judgeKind jks
            ++ [judgeSubTy jst, judgeSubEff jse]) (judgeElab je)
    toMarkup (ElabFix jst jse jks de je)
        = derive "TE-Fix" (map H.toMarkup [de] ++ map judgeKind jks
            ++ [judgeSubTy jst, judgeSubEff jse]) (judgeElab je)
    toMarkup (ElabOp de1 de2 je)
        = derive "TE-Op" (map H.toMarkup [de1, de2]) (judgeElab je)
    toMarkup (ElabSeq de1 de2 je)
        = derive "TE-Seq" (map H.toMarkup [de1, de2]) (judgeElab je)
    toMarkup (ElabIf de1 de2 de3 je)
        = derive "TE-If" (map H.toMarkup [de1, de2, de3]) (judgeElab je)
    toMarkup (ElabNil je)
        = derive "TE-Nil" [] (judgeElab je)
    toMarkup (ElabCons de1 de2  je)
        = derive "TE-Cons" (map H.toMarkup [de1, de2]) (judgeElab je)
    toMarkup (ElabCase de1 de2 de3 je)
        = derive "TE-Case" (map H.toMarkup [de1, de2, de3]) (judgeElab je)

judgeType :: JudgeType -> H.Html
judgeType (tyEnv, kiEnv, elabTm, exnTy, exn)
--    = H.toHtml $ "$" ++ latex tyEnv ++ " ; " ++ latex kiEnv ++ " \\vdash " ++ latex tm ++ " \\leadsto " ++ latex elabTm ++ " : " ++ latex exnTy ++ " \\ \\&\\  " ++ latex exn ++ "$"
    = H.toHtml $ "$" ++ "\\Gamma" ++ " ; " ++ "\\Delta" ++ " \\vdash "
        ++ latex elabTm ++ " : " ++ latex exnTy ++ " \\ \\&\\  " ++ latex exn ++ "$"

judgeElab :: JudgeElab -> H.Html
judgeElab (tyEnv, kiEnv, tm, elabTm, exnTy, exn)
--    = H.toHtml $ "$" ++ latex tyEnv ++ " ; " ++ latex kiEnv ++ " \\vdash " ++ latex tm ++ " \\leadsto " ++ latex elabTm ++ " : " ++ latex exnTy ++ " \\ \\&\\  " ++ latex exn ++ "$"
    = H.toHtml $ "$" ++ "\\Gamma" ++ " ; " ++ "\\Delta" ++ " \\vdash "
        ++ latex tm ++ " \\leadsto " ++ latex elabTm ++ " : " ++ latex exnTy
        ++ " \\ \\&\\  " ++ latex exn ++ "$"

judgeKind :: JudgeKind -> H.Html
judgeKind (kiEnv, exn, kind)
    = H.toHtml $ "$" ++ "\\Delta" ++ " \\vdash " ++ latex exn ++ " : "
        ++ latex kind ++ "$"

judgeSubTy :: JudgeSubTy -> H.Html
judgeSubTy (kiEnv, exnTy1, exnTy2)
    = H.toHtml $ "$" ++ "\\Delta" ++ " \\vdash " ++ latex exnTy1 ++ " \\leq "
        ++ latex exnTy2 ++ "$"

judgeSubEff :: JudgeSubEff -> H.Html
judgeSubEff (kiEnv, exn1, exn2)
    = H.toHtml $ "$" ++ "\\Delta" ++ " \\vdash " ++ latex exn1 ++ " \\leq "
        ++ latex exn2 ++ "$"

judgeTyWff :: JudgeTyWff -> H.Html
judgeTyWff (kiEnv, exnTy, ty)
    = H.toHtml $ "$" ++ "\\Delta" ++ " \\vdash " ++ latex exnTy
        ++ " \\triangleright " ++ latex ty ++ "$"

-- | Reconstruction

reconstructHtml :: Reconstruct -> [H.Html]
reconstructHtml (ReconstructVar env kenv tm t exn result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "lookup x env"
        trAssign "t"   (latex t)
        trAssign "exn" (latex exn)
        htmlResult kenv result
      )
reconstructHtml (ReconstructAbs env kenv tm@(Abs x ty tm') co@(_, t1', exn1, kenv1) env' re@(_, _, t2', exn2) t' result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "complete [] ty"
        htmlComplete t1' exn1 kenv1
        H.tr $ do
            H.td $ ""
            H.td $ "env'"
            H.td ! A.colspan "3" $ H.toHtml $ "$\\leftarrow " ++ latex env' ++ "$"
        htmlDo "reconstruct env' (kenv1 ++ kenv) tm'"
        htmlReconstruct (kenv1 ++ kenv) re "XXX"  -- FIXME: (t2', exn2, c1, kenv2)
        htmlDo "forallFromEnv kenv1 (ExnArr t1' (ExnVar exn1) t2' exn2')"
        trAssign "t'" (latex t')
        htmlResult kenv result
      ) ++ recurse [re]
reconstructHtml (ReconstructApp env kenv tm re1 re2@(_, _, t2, exn2) ins@(ExnArr t2' (ExnVar exn2') t' exn', kenv') subst' subst result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct kenv re1 "1"
        htmlDo "reconstruct env kenv e2"
        htmlReconstruct kenv re2 "2"
        htmlDo "instantiate t1"
        htmlInstantiate ins
        H.tr $ do
            H.td $ ""
            H.td $ "subst"
            H.td ! A.colspan "3" $ H.toHtml $ "= [(exn2', ExnVar exn2)] <.> match [] $" ++ latex t2 ++ "$ $" ++ latex t2' ++ "$"
        -- rowRes $ mathjax' subst'
        rowRes $ mathjax' subst
        H.tr $ do
            H.td $ ""
            H.td $ "c"
            H.td ! A.colspan "3" $ "[substExn' subst exn' :<: e, ExnVar exn1 :<: e] ++ c1 ++ c2"
        htmlResult kenv result
      ) ++ recurse [re1, re2]
reconstructHtml (ReconstructCon env kenv tm result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlResult kenv result
      )
reconstructHtml (ReconstructBinOp env kenv tm re1 re2 result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct kenv re1 "1"
        htmlDo "reconstruct env kenv e2"
        htmlReconstruct kenv re2 "2"
        htmlResult kenv result
      ) ++ recurse [re1, re2]
reconstructHtml (ReconstructIf env kenv tm re1 re2 re3 t result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct kenv re1 "1"
        htmlDo "reconstruct env kenv e2"
        htmlReconstruct kenv re2 "2"
        H.tr $ do
            H.td $ ""
            H.td $ "env'"
            H.td ! A.colspan "3" $ "= (x1, (t1, exn1')) : (x2, (ExnList t1 exn1', ExnVar exn1)) : env"
        htmlDo "reconstruct env (kenv1 ++ kenv) e3"
        htmlReconstruct kenv re3 "3"
        H.tr $ do
            H.td $ ""
            H.td $ "t"
            H.td ! A.colspan "3" $ "= join t1 t2"
        rowRes $ mathjax' t
        H.tr $ do
            H.td $ ""
            H.td $ "c"
            H.td ! A.colspan "3" $ "[ExnVar exn1 :<: exn, ExnVar exn2 :<: exn, ExnVar exn3 :<: exn] ++ c1 ++ c2 ++ c3"
        htmlResult kenv result
      ) ++ recurse [re1, re2, re3]
reconstructHtml (ReconstructCrash env kenv tm result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlResult kenv result
      )
reconstructHtml (ReconstructSeq env kenv tm re1 re2 result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct kenv re1 "1"
        htmlDo "reconstruct env kenv e2"
        htmlReconstruct kenv re2 "2"
        htmlResult kenv result
      ) ++ recurse [re1, re2]
reconstructHtml (ReconstructFix env kenv tm re ins t_0 exn_0 km@(trace, t_w, exn_w, subst_w) result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct kenv re "1"
        htmlDo "instantiate t1"
        htmlInstantiate ins
        -- Kleene-Mycroft iteration
        H.tr $ do
            H.td $ ""
            H.td ! A.colspan "4" $ "--- METHOD 2"
        H.tr $ do
            H.td $ ""
            H.td $ ""
            H.td ! A.colspan "3" $ "-- initialization"
        rowRes $ mathjax' t_0
        rowRes $ mathjax' exn_0
        forM trace $ \(t_i, exn_i, t', exn', t'', exn'', kenv',
                       subst', subst, t_j, t_j', exn_j, exn_j') -> do
            H.tr $ do
                H.td $ ""
                H.td $ ""
                H.td ! A.colspan "3" $ "-- iteration"
            trEquals "\\widehat\\tau_i" (latex t_i)
            trEquals "\\psi_i" (latex exn_i)
            trAssign "\\widehat\\tau^\\prime\\langle\\beta^\\prime\\rangle\\rightarrow\\widehat\\tau^{\\prime\\prime}\\langle\\psi^{\\prime\\prime}\\rangle;\\Delta^\\prime" "\\mathrm{instantiate}(t_1)"
            trEquals "\\widehat\\tau^\\prime" (latex t')
            trEquals "\\beta^\\prime" ("e_{" ++ show exn' ++ "}")
            trEquals "\\widehat\\tau^{\\prime\\prime}" (latex t'')
            trEquals "\\psi^{\\prime\\prime}" (latex exn'')
            trEquals "\\Delta^\\prime" (latex kenv')
            trAssign "\\theta^\\prime" ("match(\\epsilon; \\widehat\\tau_i; \\widehat\\tau^\\prime)")
            trReduce (latex subst')
            trAssign "\\theta" ("\\left[\\beta^\\prime\\mapsto\\psi_i\\right]\\circ match(\\epsilon; \\widehat\\tau_i; \\widehat\\tau^\\prime)")
            trReduce (latex subst)
            trAssign "\\widehat\\tau_{i+1}" "\\theta\\widehat\\tau^{\\prime\\prime}"
            trReduce    (latex t_j)
            trNormalize (latex t_j')
        -- RESULT
        htmlResult kenv result
      ) ++ recurse [re]
reconstructHtml (ReconstructNil env kenv tm result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlResult kenv result
      )
reconstructHtml (ReconstructCons env kenv tm re1 re2 t result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct kenv re1 "1"
        htmlDo "reconstruct env kenv e2"
        htmlReconstruct kenv re2 "2"
        H.tr $ do
            H.td $ ""
            H.td $ "t"
            H.td ! A.colspan "3" $ "= join t1 t2"
        rowRes $ mathjax' t
        htmlResult kenv result
      ) ++ recurse [re1, re2]
reconstructHtml (ReconstructCase env kenv tm re1 re2 env' re3 t result)
    = (return $ H.table $ do
        htmlHeader env kenv tm
        htmlDo "reconstruct env kenv e1"
        htmlReconstruct kenv re1 "1"
        htmlDo "reconstruct env kenv e2"
        htmlReconstruct kenv re2 "2"
        H.tr $ do
            H.td $ ""
            H.td $ "env'"
            H.td ! A.colspan "3" $ "= (x1, (t1, exn1')) : (x2, (ExnList t1 exn1', ExnVar exn1)) : env"
        htmlDo "reconstruct env (kenv1 ++ kenv) e3"
        htmlReconstruct kenv re3 "3"
        rowRes $ mathjax' env'
        H.tr $ do
            H.td $ ""
            H.td $ "t"
            H.td ! A.colspan "3" $ "= join t1 t2"
        rowRes $ mathjax' t
        H.tr $ do
            H.td $ ""
            H.td $ "c"
            H.td ! A.colspan "3" $ "[ExnVar exn1 :<: exn, ExnVar exn2 :<: exn, ExnVar exn3 :<: exn] ++ c1 ++ c2 ++ c3"
        htmlResult kenv result
      ) ++ recurse [re1, re2, re3]


recurse :: [Reconstruct'] -> [H.Html]
recurse = concatMap (\((_,_,re),_,_,_) -> reconstructHtml re)

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

trEquals :: String -> String -> H.Html
trEquals name expr = do
    H.tr $ do
        H.td $ ""
        H.td $ ""
        H.td $ H.toHtml $ "$" ++ name ++ "$"
        H.td $ "$=$"
        H.td $ H.toHtml $ "$" ++ expr ++ "$"
        
trReduce :: String -> H.Html
trReduce expr = do
    H.tr $ do
        H.td $ ""
        H.td $ ""
        H.td $ ""
        H.td $ "$\\leadsto$"
        H.td $ H.toHtml $ "$" ++ expr ++ "$"

trNormalize :: String -> H.Html
trNormalize expr = do
    H.tr $ do
        H.td $ ""
        H.td $ ""
        H.td $ ""
        H.td $ "$\\Downarrow$"
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
htmlReconstruct delta (re, _, t, exn) n
    = do trAssign ("t_{" ++ n ++ "}")    (latexCheck delta t)
         trAssign ("exn_{" ++ n ++ "}")  (latex exn)

htmlComplete exnTy exn kenv
    = do trAssign "t_1'"   (latex exnTy)
         trAssign "exn_1"  (latex exn)
         trAssign "kenv_1" (latex kenv)

htmlInstantiate (exnTy@(ExnArr t2' (ExnVar exn2') t' exn'), kenv)   -- FIXME: local variable naming...
    = do trAssign "t_2'\\{\\chi_2'\\} \\to t'\\{\\chi'\\}" (latex exnTy)
         trAssign "t_2'"     (latex t2')
         trAssign "t'"       (latex t')
         trAssign "\\chi_2'" (show exn2')
         trAssign "\\chi'"   (latex exn')
         trAssign "kenv'"                                  (latex kenv)

htmlDo thing = H.tr $ do
            H.td $ H.b "do"
            H.td ! A.colspan "4" $ thing

htmlResult kenv (_, exnTy, exn)
    = do H.tr $ do
            H.td $ H.b "in"
            H.td $ "$\\tau$"
            H.td $ "="
            H.td ! A.colspan "3" $ H.toHtml $
                "$" ++ (latexCheck kenv exnTy) ++ "$"
         H.tr $ do
            H.td $ H.b ""
            H.td $ ""
            H.td $ "="
            H.td ! A.colspan "3" $ H.toHtml $
                "$" ++ (latexCheck kenv (simplifyExnTy kenv exnTy)) ++ "$"
         H.tr $ do
            H.td $ ""
            H.td $ "$\\chi$"
            H.td $ "="
            H.td ! A.colspan "3" $ H.toHtml $ mathjax' exn
            
latexCheck :: KindEnv -> ExnTy -> String
latexCheck kenv t
    | checkExnTy kenv t = "\\color{green}" ++ latex t ++ "\\color{black}"
    | otherwise         = "\\color{red}"   ++ latex t ++ "\\color{black}"
