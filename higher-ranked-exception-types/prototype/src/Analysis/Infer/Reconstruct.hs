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
reconstruct :: Env -> KindEnv -> Expr
                        -> Fresh (Reconstruct, ExnTy, Exn, KindEnv)
                                                        -- ^ only from instantiate?
                                                        --   (or also complete?
                                                        --    probably quantify there)

reconstruct env kenv tm@(Var x)
    = do let Just (t, exn) = lookup x env
         return $ ReconstructVar env kenv tm t exn #
            (t, exn, [])

reconstruct env kenv tm@(Abs x ty tm')
    = do co@(dt1', t1', ExnVar exn1, kenv1) <- C.complete [] ty
         let env' = (x, (t1', ExnVar exn1)) : env
         re@(_, t2', exn2, kenv2) <- reconstruct env' (kenv1 ++ kenv) tm'
         let t' = C.forallFromEnv kenv1 (ExnArr t1' (ExnVar exn1) t2' exn2)
         return $ ReconstructAbs env kenv tm co env' re t' #
            (simplifyExnTy (kenv ++ kenv2) t', ExnEmpty, kenv2 {- FIXME: might not need all/any of this -})

reconstruct env kenv tm@(App e1 e2)
    = do re1@(_, t1, exn1, kenv1) <- reconstruct env kenv e1
         re2@(_, t2, exn2, kenv2) <- reconstruct env kenv e2
         ins@(ExnArr t2' (ExnVar exn2') t' exn', kenv') <- instantiate t1
         subst' <- match [] t2 t2'
         let subst = [(exn2', exn2)] <.> subst'
         let exn = ExnUnion (substExn' subst exn') exn1
         return $ ReconstructApp env kenv tm re1 re2 ins subst' subst #
            (substExnTy' subst  t', exn, kenv' ++ kenv2 ++ kenv1)

reconstruct env kenv tm@(Con b)
    = do return $ ReconstructCon env kenv tm #
            (ExnBool, ExnEmpty, [])

reconstruct env kenv tm@(BinOp e1 e2)
    = do re1@(_, ExnInt, exn1, kenv1) <- reconstruct env kenv e1
         re2@(_, ExnInt, exn2, kenv2) <- reconstruct env kenv e2
         return $ ReconstructBinOp env kenv tm re1 re2 #
            (ExnBool, ExnUnion exn1 exn2, kenv1 ++ kenv2)

reconstruct env kenv tm@(If e1 e2 e3)
    = do re1@(_, ExnBool, exn1, kenv1) <- reconstruct env kenv e1
         re2@(_, t2,      exn2, kenv2) <- reconstruct env kenv e2
         re3@(_, t3,      exn3, kenv3) <- reconstruct env kenv e3
         let t = join t2 t3
         let exn = ExnUnion exn1 (ExnUnion exn2 exn3)
         return $ ReconstructIf env kenv tm re1 re2 re3 t #
            (t, exn, kenv3 ++ kenv2 ++ kenv1)

reconstruct env kenv tm@(Crash lbl ty)
    = do ty' <- C.bottomExnTy ty
         return $ ReconstructCrash env kenv tm #
            (ty', ExnCon lbl, [])

reconstruct env kenv tm@(Seq e1 e2)
    = do re1@(_, t1, exn1, kenv1) <- reconstruct env kenv e1
         re2@(_, t2, exn2, kenv2) <- reconstruct env kenv e2
         return $ ReconstructSeq env kenv tm re1 re2 #
            (t2, ExnUnion exn1 exn2, kenv2 ++ kenv1)

reconstruct env kenv tm@(Fix e1)   -- FIXME: not known to be sound (see notes)
    = do re@(_, t1, exn1, kenv1) <- reconstruct env kenv e1
         ins@(ExnArr t' (ExnVar exn') t'' exn'', kenv') <- instantiate t1

         -- METHOD 1 ("unification")
         subst1 <- match [] t'' t'
         let subst2 = [(exn', substExn' subst1 exn'')]
         let subst3 = map (\(x,k) -> (x, C.kindedEmpty k)) kenv' -- FIXME: "masking"
         let t_   = substExnTy' subst3 $ simplifyExnTy (kenv' ++ kenv1 ++ kenv) $
                        substExnTy' (subst2 <.> subst1) t'
         let exn_ = substExn' subst3 $ simplifyExn (kenv' ++ kenv1 ++ kenv) $
                        substExn' (subst2 <.> subst1) exn''
            -- FIXME: ^ substitution composition seems broken...

         -- METHOD 2 (fixpoint iteration)
         let f t_i exn_i = do
                subst' <- match [] t_i t'
                let subst = [(exn', exn_i)] <.> subst'
                return (t_i
                       ,exn_i
                       ,t'      -- constant
                       ,exn'    -- constant
                       ,subst'
                       ,subst
                       ,substExnTy' subst t''
                       ,simplifyExnTy kenv $ substExnTy' subst t''
                       ,substExn' subst exn''
                       ,simplifyExn   kenv $ substExn' subst exn''
                       )
         let kleeneMycroft trace t_i exn_i = do    -- TODO: abstract to fixpointM
                tr@(_,_,_,_,_,_,_,t_j,_,exn_j) <- f t_i exn_i
                if exnTyEq kenv t_i t_j && exnEq kenv exn_i exn_j
                then return (trace, t_i, exn_i)
                else kleeneMycroft (trace ++ [tr]) t_j exn_j
         t0 <- C.bottomExnTy (underlying t')
         let exn0 = ExnEmpty        -- FIXME: exn1?
         km@(_, t_w, exn_w) <- kleeneMycroft [] t0 exn0

         return $ ReconstructFix env kenv tm re ins
                                 subst1 subst2 subst3 t_ exn_
                                 t0 exn0 km
                # (simplifyExnTy kenv t_, simplifyExn kenv exn_, kenv' ++ kenv1)

reconstruct env kenv tm@(Nil ty)
    = do ty' <- C.bottomExnTy ty
         return $ ReconstructNil env kenv tm # 
            (ExnList ty' ExnEmpty, ExnEmpty, [])

reconstruct env kenv tm@(Cons e1 e2)
    = do re1@(_, t1              , exn1, kenv1) <- reconstruct env kenv e1
         re2@(_, ExnList t2 exn2', exn2, kenv2) <- reconstruct env kenv e2
         let t = join t1 t2
         let t' = ExnList t (ExnUnion exn1 exn2')
         return $ ReconstructCons env kenv tm re1 re2 t # 
            (simplifyExnTy (kenv2 ++ kenv1 ++ kenv) t', exn2', kenv2 ++ kenv1)

reconstruct env kenv tm@(Case e1 e2 x1 x2 e3)
    = do re1@(_, ExnList t1 exn1', exn1, kenv1) <- reconstruct env  kenv  e1
         re2@(_, t2,               exn2, kenv2) <- reconstruct env  kenv  e2
         let env'  = [(x1, (t1, exn1')), (x2, (ExnList t1 exn1', exn1))] ++ env
         let kenv' = kenv1 ++ kenv
         re3@(_, t3,               exn3, kenv3) <- reconstruct env' kenv' e3
         let t = join t2 t3
         let exn = ExnUnion exn1 (ExnUnion exn2 exn3)
         return $ ReconstructCase env kenv tm re1 re2 env' re3 t # 
            (t, exn, kenv3 ++ kenv2 ++ kenv1)

-- | Kind reconstruction

-- FIXME: do we need the missing cases? (or why not?)
-- FIXME: dead code?

kindOf :: KindEnv -> Exn -> Kind
kindOf kenv (ExnVar e)
    | Just k <- lookup e kenv = k
    | otherwise               = error "kindOf: not in scope"
kindOf kenv (ExnApp e1 e2)
    | (k1 :=> k2) <- kindOf kenv e1, k1' <- kindOf kenv e2, k1 == k1' = k2
    | otherwise = error "kindOf: application"
kindOf kenv x
    = error $ "kindOf: not a variable or application (x=" ++ show x ++ "; kenv=" ++ show kenv ++ ")"

-- | Instantiation

instantiate :: ExnTy -> Fresh (ExnTy, KindEnv)
instantiate (ExnForall e k t)
    = do e' <- fresh
         (t', kenv) <- instantiate t
         return (substExnTy e e' t', [(e', k)] ++ kenv)
instantiate t
    = do return (t, [])
