{-# LANGUAGE ViewPatterns #-}

module Analysis.Infer.Reconstruct (
    reconstruct, reconstructTop
) where

import qualified Data.Map    as M
import           Data.Maybe (fromJust)

import           Analysis.Names
import           Analysis.Common
import qualified Analysis.Completion as C

import           Analysis.Infer.Types
import           Analysis.Infer.Join
import           Analysis.Infer.Match
import           Analysis.Infer.Solve

-- | Top-level solving

reconstructTop :: Expr -> Fresh (ExnTy, Exn)
reconstructTop expr = do
    re@(_, t, e, c, kenv) <- reconstruct [] [] expr
    let t'    = simplifyExnTy kenv t
    let subst = M.toList $ solveAll kenv c
    return (simplifyExnTy kenv (substExnTy' subst t'), fromJust $ lookup e subst)

-- | Reconstruction

(#) :: ((a, b, c, d) -> e) -> (a, b, c, d) -> (e, a, b, c, d)
x # y@(y1,y2,y3,y4) = (x y, y1, y2, y3, y4)

-- TODO: store KindEnv, Env in the monad
reconstruct :: Env -> KindEnv -> Expr
                        -> Fresh (Reconstruct, ExnTy, Name, [Constr], KindEnv)

reconstruct env kenv tm@(Var x)
    = do let Just (t, exn) = lookup x env
         e <- fresh
         return $ ReconstructVar env kenv tm t exn e #
            (t, e, [exn :<: e], [(e, kindOf kenv exn)])

reconstruct env kenv tm@(Abs x ty tm')
    = do co@(dt1', t1', ExnVar exn1, kenv1) <- C.complete [] ty
         let env' = (x, (t1', ExnVar exn1)) : env
         re@(_, t2', exn2, c1, kenv2) <- reconstruct env' (kenv1 ++ kenv) tm'
         let v = [exn1] ++ map fst kenv1 ++ fev env
         -- FIXME: is this the correct environment we are passing here?
         let kenv' = kenv1 ++ [(exn1,EXN)] ++ kenv
         let exn2' = solve kenv' c1 v exn2
         let t' = C.forallFromEnv kenv1 (ExnArr t1' (ExnVar exn1) t2' exn2')
         e <- fresh
         return $ ReconstructAbs env kenv tm co env' re v kenv' exn2' t' e #
            (t', e, [] {-c1-} {- FIXME: Stefan claims this should be empty!
                We would at least need to solve more agressively then, but
                can this even be done if C contains variables free in the
                environment??? -}
            ,[(e,EXN)] ++ kenv2 {- FIXME: might not need all of this -})

reconstruct env kenv tm@(App e1 e2)
    = do re1@(_, t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         re2@(_, t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         ins@(ExnArr t2' (ExnVar exn2') t' exn', kenv') <- instantiate t1
         subst' <- match [] t2 t2'
         let subst = [(exn2', ExnVar exn2)] <.> subst'
         e <- fresh
         let c = [substExn' subst exn' :<: e, ExnVar exn1 :<: e] ++ c1 ++ c2
         return $ ReconstructApp env kenv tm re1 re2 ins subst' subst e c #
            (substExnTy' subst  t', e, c
            ,[(e, kindOf (kenv1 ++ kenv) (ExnVar exn1))] ++ kenv' ++ kenv2 ++ kenv1)
            -- FIXME: can e ever be anything but of kind EXN?

reconstruct env kenv tm@(Con b)
    = do e <- fresh
         return $ ReconstructCon env kenv tm e #
            (ExnBool, e, [], [(e,EXN)])

reconstruct env kenv tm@(If e1 e2 e3)
    = do re1@(_, ExnBool, exn1, c1, kenv1) <- reconstruct env kenv e1
         re2@(_, t2,      exn2, c2, kenv2) <- reconstruct env kenv e2
         re3@(_, t3,      exn3, c3, kenv3) <- reconstruct env kenv e3
         let t = join t2 t3
         e <- fresh
         let c = [ExnVar exn1 :<: e, ExnVar exn2 :<: e, ExnVar exn3 :<: e ]
                    ++ c1 ++ c2 ++ c3
         return $ ReconstructIf env kenv tm re1 re2 re3 t e c #
            (t, e, c, kenv3 ++ kenv2 ++ kenv1)

reconstruct env kenv tm@(Crash lbl ty)
    = do co@(dty', ty', ExnVar exn1, kenv1) <- C.complete [] ty
         return $ ReconstructCrash env kenv tm co #
            (ty', exn1, [ExnCon lbl :<: exn1], kenv1)

reconstruct env kenv tm@(Seq e1 e2)
    = do re1@(_, t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         re2@(_, t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         e <- fresh
         return $ ReconstructSeq env kenv tm re1 re2 e #
            (t2, e, [ExnVar exn1 :<: e, ExnVar exn2 :<: e] ++ c1 ++ c2
            ,[(e,kindOf (kenv1 ++ kenv) (ExnVar exn1))] ++ kenv2 ++ kenv1)

reconstruct env kenv tm@(Fix e1)   -- FIXME: unknown to be sound (see notes)
    = do re@(_, t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         ins@(ExnArr t' (ExnVar exn') t'' exn'', kenv') <- instantiate t1
         subst1 <- match [] t'' t'
         let subst2 = [(exn', substExn' subst1 exn'')]
         e <- fresh
         let c = [substExn' (subst2 <.> subst1) exn'' :<: e] ++ c1
         return $ ReconstructFix env kenv tm re ins subst1 subst2 e c # 
            (substExnTy' (subst2 <.> subst1) t', e, c
            ,[(e,EXN)] ++ kenv' ++ kenv1)

reconstruct env kenv tm@(Nil ty)
    = do co@(dty', ty', ExnVar exn1, kenv1) <- C.complete [] ty
         exn2 <- fresh
         -- FIXME: not completely sure about the kind of exn2 (should be ∅)
         return $ ReconstructNil env kenv tm co exn2 # 
            (ExnList ty' (ExnVar exn1), exn2, [], [(exn2, EXN)] ++ kenv1)

reconstruct env kenv tm@(Cons e1 e2)
    = do re1@(_, t1              , exn1, c1, kenv1) <- reconstruct env kenv e1
         re2@(_, ExnList t2 exn2', exn2, c2, kenv2) <- reconstruct env kenv e2
         let t = join t1 t2
         ex1 <- fresh
         ex2 <- fresh

         let c' = [ExnVar exn1 :<: ex1, exn2' :<: ex1, ExnVar exn2 :<: ex2] ++ c1 ++ c2

         -- FIXME: solving pass from R-Abs (see comments there)
         let v = [ex2] ++ fev env
         let kenv' = [(ex2,EXN)] ++ kenv2 ++ kenv1 ++ kenv
         let ex1'  = solve kenv' c' v ex1

         -- FIXME: not completely sure about the kind of ex1 and ex2 (should be ∅)
         return $ ReconstructCons env kenv tm re1 re2 t ex1 ex2 # 
            (ExnList t ex1', ex2, c'
            ,[(ex1, kindOf (kenv1 ++ kenv) (ExnVar exn1))
             ,(ex2, kindOf (kenv2 ++ kenv) (ExnVar exn2))] ++ kenv2 ++ kenv1)

reconstruct env kenv tm@(Case e1 e2 x1 x2 e3)
    = do re1@(_, ExnList t1 exn1', exn1, c1, kenv1) <- reconstruct env kenv e1
         re2@(_, t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         let env' = (x1, (t1, exn1')) : (x2, (ExnList t1 exn1', ExnVar exn1)) : env
         re3@(_, t3, exn3, c3, kenv3) <- reconstruct env' (kenv1 ++ kenv) e3
         let t = join t2 t3
         exn <- fresh
         let c = [ExnVar exn1 :<: exn, ExnVar exn2 :<: exn, ExnVar exn3 :<: exn]
                    ++ c1 ++ c2 ++ c3
         return $ ReconstructCase env kenv tm re1 re2 env' re3 t exn c # 
            (t, exn, c
            ,[(exn, kindOf (kenv1 ++ kenv) (ExnVar exn1))] ++ kenv3 ++ kenv2 ++ kenv1)
         
-- | Kind reconstruction

kindOf :: KindEnv -> Exn -> Kind
kindOf kenv (ExnVar e)
    | Just k <- lookup e kenv = k
    | otherwise               = error "kindOf: not in scope"
kindOf kenv _
    = error "kindOf: not a variable"

-- | Instantiation

instantiate :: ExnTy -> Fresh (ExnTy, KindEnv)
instantiate (ExnForall e k t)
    = do e' <- fresh
         (t', kenv) <- instantiate t
         return (substExnTy e e' t', [(e', k)] ++ kenv)
instantiate t
    = do return (t, [])
