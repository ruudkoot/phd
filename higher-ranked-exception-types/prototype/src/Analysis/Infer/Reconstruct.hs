{-# LANGUAGE ViewPatterns #-}

module Analysis.Infer.Reconstruct (
    reconstruct
) where

import qualified Data.Map    as M
import           Data.Maybe (fromJust)

import           Analysis.Names
import           Analysis.Common
import qualified Analysis.Completion as C

import           Analysis.Infer.Types
import           Analysis.Infer.Join
import           Analysis.Infer.Match

-- TODO: move forallFromEnv here?
-- TODO: move simplifyExnTy here?

-- | Reconstruction

(#) :: ((a, b, c) -> e) -> (a, b, c) -> (e, a, b, c)
x # y@(y1,y2,y3) = (x y, y1, y2, y3)

-- TODO: store KindEnv, Env in the monad
reconstruct :: Env -> KindEnv -> Expr -> Fresh (Reconstruct, ElabTm, ExnTy, Exn)

reconstruct env kenv tm@(Var x)
    = do let Just (t, exn) = lookup x env
         return $ ReconstructVar env kenv tm t exn #
            (Var' x, t, exn)

reconstruct env kenv tm@(Con b)       {- TODO: generalize to arbitrary types -}
    = do return $ ReconstructCon env kenv tm #
            (Con' b, ExnBool, ExnEmpty)

reconstruct env kenv tm@(Crash lbl ty)
    = do ty' <- C.bottomExnTy ty
         return $ ReconstructCrash env kenv tm #
            (Crash' lbl ty, ty', ExnCon lbl)

reconstruct env kenv tm@(Abs x ty tm')
    = do co@(dt1', t1', ExnVar exn1, kenv1) <- C.complete [] ty
         let env' = (x, (t1', ExnVar exn1)) : env
         re@(_, etm', t2', exn2) <- reconstruct env' (kenv1 ++ kenv) tm'
         let t' = C.forallFromEnv kenv1 (ExnArr t1' (ExnVar exn1) t2' exn2)
         return $ ReconstructAbs env kenv tm co env' re t' #
            (annAbsFromEnv kenv1 $ Abs' x t1' (ExnVar exn1) etm', t', ExnEmpty)

reconstruct env kenv tm@(App e1 e2)
    = do re1@(_, etm1, t1, exn1) <- reconstruct env kenv e1
         re2@(_, etm2, t2, exn2) <- reconstruct env kenv e2
         ins@(ExnArr t2' (ExnVar exn2') t' exn', kenv') <- instantiate t1
         subst' <- match [] t2 t2'             -- ^ FIXME: unused!
         let subst = [(exn2', exn2)] <.> subst'
         let exn = ExnUnion (substExn' subst exn') exn1
         return $ ReconstructApp env kenv tm re1 re2 ins subst' subst #
            ( App' (annAppFromEnv ((exn2',EXN):kenv') subst etm1) etm2
            , simplifyExnTy kenv $ substExnTy' subst  t'
            , simplifyExn   kenv $                    exn)

reconstruct env kenv tm@(Fix e1)
    = do re@(_, ee1, t1, exn1) <- reconstruct env kenv e1
         ins@(ExnArr t' (ExnVar exn') t'' exn'', kenv') <- instantiate t1
                                                -- ^ FIXME: unused!

         let f t_i exn_i = do
                -- ins@(ExnArr t' (ExnVar exn') t'' exn'', kenv') <- instantiate t1
                subst' <- match [] t_i t'
                let subst = [(exn', exn_i)] <.> subst'
                return (t_i
                       ,exn_i
                       ,t'      -- not constant if I inside the loop
                       ,exn'    -- not constant if I inside the loop
                       ,t''     -- not constant if I inside the loop
                       ,exn''   -- not constant if I inside the loop
                       ,kenv'   -- not constant if I inside the loop
                       ,subst'
                       ,subst
                       ,substExnTy' subst t''
                       ,simplifyExnTy kenv $ substExnTy' subst t''
                       ,substExn' subst exn''
                       ,simplifyExn   kenv $ substExn' subst exn''
                       )

         let kleeneMycroft trace t_i exn_i = do    -- TODO: abstract to fixpointM
                tr@(_,_,_,_,_,_,_,_,_,_,t_j,_,exn_j) <- f t_i exn_i
                if exnTyEq kenv t_i t_j && exnEq kenv exn_i exn_j
                then return (trace, t_i, exn_i)
                else kleeneMycroft (trace ++ [tr]) t_j exn_j

         t0 <- C.bottomExnTy (underlying t')
         let exn0 = ExnEmpty
         km@(_, t_w, exn_w) <- kleeneMycroft [] t0 exn0

         return $ ReconstructFix env kenv tm re ins t0 exn0 km #
            (Fix' ee1, simplifyExnTy kenv t_w, simplifyExn kenv (ExnUnion exn_w exn1))

reconstruct env kenv tm@(BinOp e1 e2) {- TODO: comparisons only; add AOp, BOp -}
    = do re1@(_, ee1, ExnInt, exn1) <- reconstruct env kenv e1
         re2@(_, ee2, ExnInt, exn2) <- reconstruct env kenv e2
         return $ ReconstructBinOp env kenv tm re1 re2 #
            (BinOp' ee1 ee2, ExnBool, simplifyExn kenv $ ExnUnion exn1 exn2)

reconstruct env kenv tm@(Seq e1 e2)
    = do re1@(_, ee1, t1, exn1) <- reconstruct env kenv e1
         re2@(_, ee2, t2, exn2) <- reconstruct env kenv e2
         return $ ReconstructSeq env kenv tm re1 re2 #
            (Seq' ee1 ee2, t2, simplifyExn kenv $ ExnUnion exn1 exn2)

reconstruct env kenv tm@(If e1 e2 e3)
    = do re1@(_, ee1, ExnBool, exn1) <- reconstruct env kenv e1
         re2@(_, ee2, t2,      exn2) <- reconstruct env kenv e2
         re3@(_, ee3, t3,      exn3) <- reconstruct env kenv e3
         let t = join t2 t3
         let exn = ExnUnion exn1 (ExnUnion exn2 exn3)
         return $ ReconstructIf env kenv tm re1 re2 re3 t #
            (If' ee1 ee2 ee3, simplifyExnTy kenv $ t, simplifyExn kenv $ exn)

reconstruct env kenv tm@(Nil ty)
    = do ty' <- C.bottomExnTy ty
         return $ ReconstructNil env kenv tm # 
            (Nil' ty, ExnList ty' ExnEmpty, ExnEmpty)

reconstruct env kenv tm@(Cons e1 e2)
    = do re1@(_, ee1, t1              , exn1) <- reconstruct env kenv e1
         re2@(_, ee2, ExnList t2 exn2', exn2) <- reconstruct env kenv e2
         let t = join t1 t2
         let t' = ExnList t (ExnUnion exn1 exn2')
         return $ ReconstructCons env kenv tm re1 re2 t # 
            (Cons' ee1 ee2, simplifyExnTy kenv t', exn2)

reconstruct env kenv tm@(Case e1 e2 x1 x2 e3)
    = do re1@(_, ee1, ExnList t1 exn1', exn1) <- reconstruct env  kenv e1
         re2@(_, ee2, t2,               exn2) <- reconstruct env  kenv e2
         let env'  = [(x1, (t1, exn1')), (x2, (ExnList t1 exn1', exn1))] ++ env
         re3@(_, ee3, t3,               exn3) <- reconstruct env' kenv e3
         let t = join t2 t3
         let exn = ExnUnion exn1 (ExnUnion exn2 exn3)
         return $ ReconstructCase env kenv tm re1 re2 env' re3 t # 
            (Case' ee1 ee2 x1 x2 ee3, simplifyExnTy kenv $ t, simplifyExn kenv $ exn)

-- | Instantiation

-- TODO: move to separate module

instantiate :: ExnTy -> Fresh (ExnTy, KindEnv)
instantiate (ExnForall e k t)
    = do e' <- fresh
         (t', kenv) <- instantiate t
         return (substExnTy e e' t', [(e', k)] ++ kenv)
instantiate t
    = do return (t, [])
    
-- | Helper functions

-- TODO: move forallFromEnv here

annAbsFromEnv :: KindEnv -> ElabTm -> ElabTm
annAbsFromEnv [] tm
    = tm
annAbsFromEnv ((e,k):kenv) tm
    = AnnAbs e k (annAbsFromEnv kenv tm)

annAppFromEnv :: KindEnv -> Subst -> ElabTm -> ElabTm
annAppFromEnv []        _     tm
    = tm
annAppFromEnv ((e, _):kenv) subst tm
    = annAppFromEnv kenv subst (AnnApp tm (substExn' subst (ExnVar e)))
