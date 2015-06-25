{-# LANGUAGE ViewPatterns #-}

module Analysis.Infer.Reconstruct (
    reconstruct,
    checkElabTm'     -- FIXME: move to other module
) where

import qualified Data.Map    as M
import           Data.Maybe (fromJust)

import           Analysis.Names
import           Analysis.Common
import qualified Analysis.Completion as C

import           Analysis.Infer.Common
import           Analysis.Infer.Types
import           Analysis.Infer.Join
import           Analysis.Infer.Match

-- TODO: move forallFromEnv here?
-- TODO: move simplifyExnTy here?

-- | Reconstruction

(#) :: (a -> b -> c -> f, a -> b -> c -> g, (a,b,c) -> h) -> (a,b,c) -> ((f,g,h),a,b,c)
(f,g,h) # x@(x1,x2,x3) = ((f x1 x2 x3, g x1 x2 x3, h x), x1, x2, x3)

c ## (tyEnv, kiEnv, tm) = \elabTm exnTy exn -> c (tyEnv, kiEnv, tm, elabTm, exnTy, exn)
c #= (tyEnv, kiEnv)     = \elabTm exnTy exn -> c (tyEnv, kiEnv,     elabTm, exnTy, exn)

reconstruct :: Env -> KindEnv -> Expr
    -> Fresh ((DerivType, DerivElab, Reconstruct), ElabTm, ExnTy, Exn)

reconstruct env kenv tm@(Var x)
    = do let Just (t, exn) = lookup x env
         return $ ( TypeVar #= (env, kenv)
                  , ElabVar ## (env, kenv, tm)
                  , ReconstructVar env kenv tm t exn) #
            (Var' x, t, exn)

reconstruct env kenv tm@(Con b)       {- TODO: generalize to arbitrary types -}
    = do return $ ( TypeCon #= (env, kenv)
                  , ElabCon ## (env, kenv, tm)
                  , ReconstructCon env kenv tm) #
            (Con' b, ExnBool, ExnEmpty)

reconstruct env kenv tm@(Crash lbl ty)
    = do ty' <- C.bottomExnTy ty
         return $ ( TypeCrash #= (env, kenv)
                  , ElabCrash ## (env, kenv, tm)
                  , ReconstructCrash env kenv tm) #
            (Crash' lbl ty, ty', ExnCon lbl)

reconstruct env kenv tm@(Abs x ty tm') -- TODO: common subexpression elimination
    = do co@(dt1', t1', ExnVar exn1, kenv1) <- C.complete [] ty
         let env' = (x, (t1', ExnVar exn1)) : env
         re@((dt,de,_), etm', t2', exn2) <- reconstruct env' (kenv1 ++ kenv) tm'
         let t' = C.forallFromEnv kenv1 (ExnArr t1' (ExnVar exn1) t2' exn2)
         return $ (\_ _ _ -> typeAnnAbsFromEnv env kenv (reverse kenv1) $
                        TypeAbs dt (env, kenv1++kenv, Abs' x t1' (ExnVar exn1) etm'
                                   ,ExnArr t1' (ExnVar exn1) t2' exn2, ExnEmpty)
                  ,ElabAbs (kenv1++kenv, t1', ty) (kenv1++kenv, ExnVar exn1, EXN) de ##
                        (env,kenv,tm)
                  ,ReconstructAbs env kenv tm co env' re t') #
            ( annAbsFromEnv (reverse kenv1) $ Abs' x t1' (ExnVar exn1) etm'
            , t', ExnEmpty                                                 )

reconstruct env kenv tm@(App e1 e2)
    = do re1@((dt1,de1,_), etm1, t1, exn1) <- reconstruct env kenv e1
         re2@((dt2,de2,_), etm2, t2, exn2) <- reconstruct env kenv e2
         ins@(ExnArr t2' (ExnVar exn2') t' exn', kenv') <- instantiate t1
         subst' <- match [] t2 t2'             -- ^ only used for elaboration
         let subst = [(exn2', exn2)] <.> subst'
         let exn = ExnUnion (substExn' subst exn') exn1
         return $ (TypeApp (
                        let exnC = simplifyExn   kenv $ exn
                            tyC  = simplifyExnTy kenv $
                                        ExnArr t2 exn2 (substExnTy' subst t') exnC
                            tyD  = simplifyExnTy kenv $ substExnTy' subst (fst ins)
                        in TypeSub
                            (kenv,tyD,tyC)
                            (kenv,exn1,exnC)
                            (typeAnnAppFromEnv kenv' subst dt1)
                            (env,kenv,annAppFromEnv kenv' subst etm1,tyC,exnC)
                    ) dt2 #= (env, kenv)
                  ,ElabApp (kenv, t2,   simplifyExnTy kenv $ substExnTy' subst t'  )
                           (kenv, exn2, simplifyExn   kenv $ substExn'   subst exn')
                           (map (judgeKindFromEnv kenv) kenv') de1 de2 ##
                                (env, kenv, tm)
                  ,ReconstructApp env kenv tm re1 re2 ins subst' subst) #
            ( App' (annAppFromEnv kenv' subst etm1) etm2
            , simplifyExnTy kenv $ substExnTy' subst t'
            , simplifyExn   kenv $                   exn)

reconstruct env kenv tm@(Fix e1)
    = do re@((dt,de,_), ee1, t1, exn1) <- reconstruct env kenv e1
         ins@(ExnArr t' (ExnVar exn') t'' exn'', kenv') <- instantiate t1
                                                -- ^    only used for elaboration
         let f t_i exn_i = do
                -- ins@(ExnArr t' (ExnVar exn') t'' exn'', kenv') <- instantiate t1
                subst' <- match [] t_i t'
                let subst = [(exn', exn_i)] <.> subst'
                return ( t_i
                       , exn_i
                       , t'      -- not constant if I inside the loop
                       , exn'    -- not constant if I inside the loop
                       , t''     -- not constant if I inside the loop
                       , exn''   -- not constant if I inside the loop
                       , kenv'   -- not constant if I inside the loop
                       , subst'
                       , subst
                       , substExnTy' subst t''
                       , simplifyExnTy kenv $ substExnTy' subst t''
                       , substExn' subst exn''
                       , simplifyExn   kenv $ substExn' subst exn''
                       )

         let kleeneMycroft trace t_i exn_i = do    -- TODO: abstract to fixpointM
                tr@(_,_,_,_,_,_,_,_,subst_i,_,t_j,_,exn_j) <- f t_i exn_i
                if exnTyEq kenv t_i t_j && exnEq kenv exn_i exn_j
                then return (trace, t_i, exn_i, subst_i)
                else kleeneMycroft (trace ++ [tr]) t_j exn_j

         t0 <- C.bottomExnTy (underlying t')
         let exn0 = ExnEmpty
         km@(_, t_w, exn_w, subst_w) <- kleeneMycroft [] t0 exn0

         return $ (TypeFix
                    (kenv, exn_w,simplifyExn kenv (ExnUnion exn_w exn1))
                    (kenv, exn1, simplifyExn kenv (ExnUnion exn_w exn1))
                    (typeAnnAppFromEnv kenv' subst_w dt)
                     #= (env,kenv)
                  ,ElabFix (kenv
                           , simplifyExnTy kenv $ substExnTy' subst_w t''
                           , simplifyExnTy kenv $ substExnTy' subst_w t'           )
                           (kenv
                           , simplifyExn   kenv $ substExn'   subst_w         exn''
                           , simplifyExn   kenv $ substExn'   subst_w (ExnVar exn' ) )
                           (map (judgeKindFromEnv kenv) kenv') de ## (env, kenv, tm)
                  ,ReconstructFix env kenv tm re ins t0 exn0 km) #
            ( Fix' (annAppFromEnv kenv' subst_w ee1)
            , simplifyExnTy kenv t_w
            , simplifyExn kenv (ExnUnion exn_w exn1)
            )

-- TODO: try alternative method that uses completion+matching instead of
--       calling reconstruct recursively.
reconstruct env kenv tm@(FIX x ty e)
    = do -- METHOD 1 ("bottom-up", unaccelerated)
         let f t_i exn_i = do
                let env' = (x, (t_i, exn_i)) : env
                re@((dt,de,_), ee, ty', exn') <- reconstruct env' kenv e
                return (env', re)

         let kleeneMycroft trace t_i exn_i = do
                tr@(env_j, re_j@(_, _, t_j, exn_j)) <- f t_i exn_i
                if exnTyEq kenv t_i t_j && exnEq kenv exn_i exn_j
                then return (trace, re_j)
                else kleeneMycroft (trace ++ [tr]) t_j exn_j

         t0 <- C.bottomExnTy ty
         let exn0 = ExnEmpty
         km@(tr,re_w@((dt_w,de_w,_),ee_w,t_w,exn_w)) <- kleeneMycroft [] t0 exn0
         
         let res = (TypeFIX dt_w #= (env, kenv)
                   ,ElabFIX de_w ## (env, kenv, tm)
                   ,ReconstructFIX env kenv tm re_w t0 exn0 km) #
                        (FIX' x t_w exn_w ee_w, t_w, exn_w)
         
         -- METHOD 1' ("bottom-up", accelerated)
         -- TODO
         
         -- METHOD 2 ("top-down", unaccelerated)  -- freshness/non-termination issues?
         {-
         co@(dt2_0, t2_0, exn2_0, kenv2_0) <- C.complete [] ty

         let f t_i exn_i = do
                let env' = (x, (t_i, exn_i)) : env
                re@((dt,de,_), ee, ty', exn') <- reconstruct env' (kenv2_0 ++ kenv) e
                return (env', re)

         let kleeneMycroft trace t_i exn_i = do
                tr@(env_j, re_j@(_, _, t_j, exn_j)) <- f t_i exn_i
                if exnTyEq (kenv2_0 ++ kenv) t_i t_j && exnEq (kenv2_0 ++ kenv) exn_i exn_j
                then return (trace, re_j)
                else kleeneMycroft (trace ++ [tr]) t_j exn_j

         km2@(tr2,re2_w@((dt2_w,de2_w,_),ee2_w,t2_w,exn2_w)) <- kleeneMycroft [] t2_0 exn2_0
         () <- error $ show t2_w 
         -}
         
         -- METHOD 3 ("top-down", accelerated)
         co@(dt1', t0, ExnVar exn0, kenv1) <- C.complete [] ty
         let env'  = (x, (t0, ExnVar exn0)) : env
         let kenv' = kenv1 ++ kenv
         re@((dt,de,_), ee1, t1, exn1) <- reconstruct env' kenv' e

         let f t_i exn_i = do
                subst' <- match [] t_i t0
                let subst = [(exn0, exn_i)] <.> subst'
                return ( t_i
                       , exn_i
                       , subst'
                       , subst
                       , substExnTy' subst t1
                       , simplifyExnTy kenv' $ substExnTy' subst t1
                       , substExn' subst exn1
                       , simplifyExn   kenv' $ substExn' subst exn1
                       )

         let kleeneMycroft trace t_i exn_i = do
                tr@(_,_,_,subst_i,_,t_j,_,exn_j) <- f t_i exn_i
                if exnTyEq kenv' t_i t_j && exnEq kenv' exn_i exn_j
                then return (trace, t_i, exn_i, subst_i)
                else kleeneMycroft (trace ++ [tr]) t_j exn_j

         km@(_, t_w3, exn_w, subst_w) <- kleeneMycroft [] t0 (ExnVar exn0)

         return $ res
         if exnTyEq kenv' t_w t_w3 then
            return $ res
         else
            error $
                "reconstruct_FIX: METHOD 1 and 3 did not give the same result!\n"
                ++ "METHOD 1: " ++ show t_w ++ "\n"
                ++ "METHOD 3: " ++ show t_w3 ++ " / " ++ show subst_w
                

reconstruct env kenv tm@(BinOp e1 e2) {- TODO: comparisons only; add AOp, BOp -}
    = do re1@((dt1,de1,_), ee1, ExnInt, exn1) <- reconstruct env kenv e1
         re2@((dt2,de2,_), ee2, ExnInt, exn2) <- reconstruct env kenv e2
         let exn = simplifyExn kenv $ ExnUnion exn1 exn2
         return $ ( TypeOp
                        (TypeSub
                            (kenv,ExnInt,ExnInt)
                            (kenv,exn1,exn)
                            dt1
                            (env,kenv,ee1,ExnInt,exn)
                        )
                        (TypeSub
                            (kenv,ExnInt,ExnInt)
                            (kenv,exn2,exn)
                            dt2
                            (env,kenv,ee2,ExnInt,exn)
                        ) #= (env,kenv)
                  , ElabOp de1 de2 ## (env,kenv,tm)
                  , ReconstructBinOp env kenv tm re1 re2) #
            (BinOp' ee1 ee2, ExnBool, exn)

reconstruct env kenv tm@(Seq e1 e2)
    = do re1@((dt1,de1,_), ee1, t1, exn1) <- reconstruct env kenv e1
         re2@((dt2,de2,_), ee2, t2, exn2) <- reconstruct env kenv e2
         let exn = simplifyExn kenv $ ExnUnion exn1 exn2
         return $ ( TypeSeq
                        (TypeSub
                            (kenv,t1,t1)
                            (kenv,exn1,exn)
                            dt1
                            (env,kenv,ee1,t1,exn)
                        )
                        (TypeSub
                            (kenv,t2,t2)
                            (kenv,exn2,exn)
                            dt2
                            (env,kenv,ee2,t2,exn)
                        ) #= (env,kenv)
                  , ElabSeq de1 de2 ## (env,kenv,tm)
                  , ReconstructSeq env kenv tm re1 re2) #
            (Seq' ee1 ee2, t2, exn)

reconstruct env kenv tm@(If e1 e2 e3)
    = do re1@((dt1,de1,_), ee1, ExnBool, exn1) <- reconstruct env kenv e1
         re2@((dt2,de2,_), ee2, t2,      exn2) <- reconstruct env kenv e2
         re3@((dt3,de3,_), ee3, t3,      exn3) <- reconstruct env kenv e3
         let t   = simplifyExnTy kenv $ join t2 t3
         let exn = simplifyExn   kenv $ ExnUnion exn1 (ExnUnion exn2 exn3)
         return $ ( TypeIf
                        (TypeSub
                            (kenv,ExnBool,ExnBool)
                            (kenv,exn1,   exn    )
                            dt1
                            (env,kenv,ee1,ExnBool,exn)
                        )
                        (TypeSub
                            (kenv,t2,  t  )
                            (kenv,exn2,exn)
                            dt2
                            (env,kenv,ee2,t,exn)
                        )
                        (TypeSub
                            (kenv,t3,  t  )
                            (kenv,exn3,exn)
                            dt3
                            (env,kenv,ee3,t,exn)
                        ) #= (env,kenv)
                  , ElabIf de1 de2 de3 ## (env,kenv,tm)
                  , ReconstructIf env kenv tm re1 re2 re3 t ) #
            (If' ee1 ee2 ee3, t, exn)

reconstruct env kenv tm@(Nil ty)
    = do ty' <- C.bottomExnTy ty
         return $ ( TypeNil #= (env,kenv)
                  , ElabNil ## (env,kenv,tm)
                  , ReconstructNil env kenv tm ) #
            (Nil' ty, ExnList ty' ExnEmpty, ExnEmpty)

reconstruct env kenv tm@(Cons e1 e2)
    = do re1@((dt1,de1,_), ee1, t1              , exn1) <- reconstruct env kenv e1
         re2@((dt2,de2,_), ee2, ExnList t2 exn2', exn2) <- reconstruct env kenv e2
         let exn = simplifyExn kenv $ ExnUnion exn1 exn2'
         let t   = simplifyExnTy kenv $ join t1 t2
         let t'  = simplifyExnTy kenv $ ExnList t (ExnUnion exn1 exn2')
         return $ ( TypeCons
                        (TypeSub
                            (kenv, t1, t)
                            (kenv, exn1, exn)
                            dt1
                            (env, kenv, ee1, t, exn)
                        )
                        (TypeSub
                            (kenv, ExnList t2 exn2', t')
                            (kenv, exn2, exn2)
                            dt2
                            (env, kenv, ee2, t', exn2)
                        ) #= (env,kenv)
                  , ElabCons de1 de2 ## (env,kenv,tm)
                  , ReconstructCons env kenv tm re1 re2 t) #
            (Cons' ee1 ee2, t', exn2)

reconstruct env kenv tm@(Case e1 e2 x1 x2 e3)
    = do re1@((dt1,de1,_), ee1, ExnList t1 exn1', exn1) <- reconstruct env  kenv e1
         re2@((dt2,de2,_), ee2, t2,               exn2) <- reconstruct env  kenv e2
         let env'  = [(x1, (t1, exn1')), (x2, (ExnList t1 exn1', exn1))] ++ env
         re3@((dt3,de3,_), ee3, t3,               exn3) <- reconstruct env' kenv e3
         let t   = simplifyExnTy kenv $ join t2 t3
         let exn = simplifyExn   kenv $ ExnUnion exn1 (ExnUnion exn2 exn3)
         return $ ( TypeCase
                        (kenv, exn1, exn)
                        (TypeSub
                            (kenv,ExnList t1 exn1',ExnList t1 exn1')
                            (kenv,exn1,exn1)
                            dt1
                            (env,kenv,ee1,ExnList t1 exn1',exn1)
                        )
                        (TypeSub
                            (kenv,t2,t)
                            (kenv,exn2,exn)
                            dt2
                            (env,kenv,ee2,t,exn)
                        )
                        (TypeSub
                            (kenv,t3,t)
                            (kenv,exn3,exn)
                            dt3
                            (env',kenv,ee3,t,exn)
                        ) #= (env, kenv)
                  , ElabCase de1 de2 de3 ## (env,kenv,tm)
                  , ReconstructCase env kenv tm re1 re2 env' re3 t ) #
            (Case' ee1 ee2 x1 x2 ee3, t, exn)

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
annAbsFromEnv []           tm =                                tm
annAbsFromEnv ((e,k):kenv) tm = AnnAbs e k (annAbsFromEnv kenv tm)

typeAnnAbsFromEnv :: Env -> KindEnv -> KindEnv -> DerivType -> DerivType
typeAnnAbsFromEnv env kenv [] dt' = dt'
typeAnnAbsFromEnv env kenv ((e,k):kenv') dt'
    = let (dt, jt@(_,_,tm,ty,exn)) =
            case typeAnnAbsFromEnv env ((e,k):kenv) kenv' dt' of
                    dt@(TypeAbs    _ jt) -> (dt, jt)
                    dt@(TypeAnnAbs _ jt) -> (dt, jt)
       in TypeAnnAbs dt (env, kenv, AnnAbs e k tm, ExnForall e k ty, exn)

annAppFromEnv :: KindEnv -> Subst -> ElabTm -> ElabTm
annAppFromEnv []            _     tm = tm
annAppFromEnv ((e, _):kenv) subst tm
    = annAppFromEnv kenv subst (AnnApp tm (substExn' subst (ExnVar e)))

typeAnnAppFromEnv :: KindEnv -> Subst -> DerivType -> DerivType
typeAnnAppFromEnv []            _     dt = dt
typeAnnAppFromEnv ((e,k):kenv') subst dt
    = let (env, kenv, tm, ExnForall e' k' exnTy, exn) = getJT dt
          -- FIXME: e /= e' ?!
          ann    = substExn' subst (ExnVar e)
          exnTy' = simplifyExnTy kenv' $ substExnTy' [(e',ann)] exnTy
       in typeAnnAppFromEnv kenv' subst
            (TypeAnnApp (kenv, ann, k) dt (env, kenv, AnnApp tm ann, exnTy', exn))

judgeKindFromEnv :: KindEnv -> (Name, Kind) -> JudgeKind
judgeKindFromEnv kenv (exn, kind) = (kenv, ExnVar exn, kind)

-- | Type checking of elaborated terms

-- TODO: move to Common? (only here because we need bottomExnTy...)

-- * With subtyping coercions (resembles declarative type system)

-- * Ignore subtyping coercions (resembles elaboration system)

checkElabTm' :: Env -> KindEnv -> ElabTm -> Fresh (Maybe (ExnTy, Exn))
checkElabTm' tyEnv kiEnv (Var' x)
    = return $ lookup x tyEnv
checkElabTm' tyEnv kiEnv (Con' c)
    = return $ Just (ExnBool, ExnEmpty)
checkElabTm' tyEnv kiEnv (Crash' lbl ty)
    = do exnTy <- C.bottomExnTy ty
         return $ Just (exnTy, ExnCon lbl)
checkElabTm' tyEnv kiEnv (Abs' x ty1 ann1 tm)
    = do () <- case lookup x tyEnv of
                 Nothing -> return ()
                 _       -> error "shadowing (Abs')"
         mty2 <- checkElabTm' ((x,(ty1,ann1)):tyEnv) kiEnv tm
         case mty2 of
            Just (ty2, ann2) -> return $ Just (ExnArr ty1 ann1 ty2 ann2, ExnEmpty)
            _ -> error "type (Abs')"
checkElabTm' tyEnv kiEnv (AnnAbs e k tm)
    = do () <- case lookup e kiEnv of
                Nothing -> return ()
                _       -> error "shadowing (AnnAbs)"
         mty <- checkElabTm' tyEnv ((e,k):kiEnv) tm
         case mty of
            Just (ty, ann) -> return $ Just (ExnForall e k ty, ann)
            _ -> error "type (AnnAbs)"
checkElabTm' tyEnv kiEnv tm@(App' tm1 tm2)
    = do mty1 <- checkElabTm' tyEnv kiEnv tm1
         case mty1 of
            Just (ExnArr ty1 ann1 ty ann, ann') -> do
                mty2 <- checkElabTm' tyEnv kiEnv tm2
                case mty2 of
                    Just (ty2, ann2) -> do
                        if isSubtype kiEnv ty2 ty1 && isSubeffect kiEnv ann2 ann1 then
                            return $ Just (ty, simplifyExn kiEnv $ ExnUnion ann ann')
                        else
                            error $ "subtype (App'): "
                                    ++ "tm = "    ++ show tm    ++ "; "
                                    ++ "ty1 = "   ++ show ty1   ++ "; "
                                    ++ "ty2 = "   ++ show ty2   ++ "; "
                                    ++ "ann1 = "  ++ show ann1  ++ "; "
                                    ++ "ann2 = "  ++ show ann2  ++ "; "
                                    ++ "tyEnv = " ++ show tyEnv ++ "; "
                                    ++ "kiEnv = " ++ show kiEnv
                    _ -> error "type (App', 2)"
            _ -> error "type (App', 1)"
checkElabTm' tyEnv kiEnv (AnnApp tm ann2)
    = do mty <- checkElabTm' tyEnv kiEnv tm
         case mty of
            Just (ExnForall e k ty, ann) -> do
                case checkKind kiEnv ann2 of
                    Just k' | k == k' -> do
                        return $ Just (simplifyExnTy kiEnv $ substExnTy' [(e,ann2)] ty, ann)
                    _ -> error $ "kind (AnnApp)"
            _ -> error "type (AnnApp)"
checkElabTm' tyEnv kiEnv (Fix' tm)
    = do mty <- checkElabTm' tyEnv kiEnv tm
         case mty of
            Just (ExnArr ty1 ann1 ty2 ann2, ann) -> do
                if isSubtype kiEnv ty2 ty1 && isSubeffect kiEnv ann2 ann1 then
                    return $ Just (ty2, simplifyExn kiEnv $ ExnUnion ann ann2)
                else
                    error "fixpoint (Fix')"
            _ -> error "type (Fix')"
checkElabTm' tyEnv kiEnv (FIX' x ty ann tm)
    = do () <- case lookup x tyEnv of
                 Nothing -> return ()
                 _       -> error "shadowing (FIX')"
         mty <- checkElabTm' ((x,(ty,ann)):tyEnv) kiEnv tm
         case mty of
            Just (ty', ann') -> do
                if isSubtype kiEnv ty' ty && isSubeffect kiEnv ann' ann then
                    return $ Just (ty, ann)
                else
                    error "fixpoint (FIX')"
            _ -> error "type (FIX')"
checkElabTm' tyEnv kiEnv (BinOp' tm1 tm2)
    = do mty1 <- checkElabTm' tyEnv kiEnv tm1
         case mty1 of
            Just (ExnInt, ann1) -> do
                mty2 <- checkElabTm' tyEnv kiEnv tm2
                case mty2 of
                    Just (ExnInt, ann2) -> return $ Just (ExnBool, simplifyExn kiEnv $ ExnUnion ann1 ann2)
                    _ -> error "type (BinOp', tm2)"
            _ -> error "type (BinOp', tm1)"
checkElabTm' tyEnv kiEnv (Seq' tm1 tm2)
    = do mty1 <- checkElabTm' tyEnv kiEnv tm1
         case mty1 of
            Just (ty1, ann1) -> do
                mty2 <- checkElabTm' tyEnv kiEnv tm2
                case mty2 of
                    Just (ty2, ann2) -> return $ Just (ty2, simplifyExn kiEnv $ ExnUnion ann1 ann2)
                    _ -> error "type (Seq', tm2)"
            _ -> error "type (Seq', tm1)"
checkElabTm' tyEnv kiEnv (If' tm1 tm2 tm3)
    = do mty1 <- checkElabTm' tyEnv kiEnv tm1
         case mty1 of
            Just (ExnBool, ann1) -> do
                mty2 <- checkElabTm' tyEnv kiEnv tm2
                case mty2 of
                    Just (ty2, ann2) -> do
                        mty3 <- checkElabTm' tyEnv kiEnv tm3
                        case mty3 of
                            Just (ty3, ann3) -> return $ Just (simplifyExnTy kiEnv $ join ty2 ty3, simplifyExn kiEnv $ ExnUnion ann1 (ExnUnion ann2 ann3))
                            _ -> error "type (If', tm3)"
                    _ -> error "type (If', tm2)"
            _ -> error "type (If', tm1)"
checkElabTm' tyEnv kiEnv (Nil' ty)
    = do exnTy <- C.bottomExnTy ty
         return $ Just (ExnList exnTy ExnEmpty, ExnEmpty)
checkElabTm' tyEnv kiEnv (Cons' tm1 tm2)
    = do mty1 <- checkElabTm' tyEnv kiEnv tm1
         case mty1 of
            Just (ty1, ann1) -> do
                mty2 <- checkElabTm' tyEnv kiEnv tm2
                case mty2 of
                    Just (ExnList ty2 ann2', ann2) -> do
                        return $ Just (simplifyExnTy kiEnv $ ExnList (join ty1 ty2) (ExnUnion ann1 ann2'), ann2)
                    _ -> error "type (Case', tm2)"
            _ -> error "type (Case', tm1)"
checkElabTm' tyEnv kiEnv (Case' tm1 tm2 x1 x2 tm3)
    = do () <- if x1 == x2 then error "non-linearity (Case')" else return ()
         () <- case lookup x1 tyEnv of
                 Nothing -> return ()
                 _       -> error "shadowing (Case', 1)"
         () <- case lookup x2 tyEnv of
                 Nothing -> return ()
                 _       -> error "shadowing (Case', 2)"
         mty1 <- checkElabTm' tyEnv kiEnv tm1
         case mty1 of
            Just annTy1@(ExnList ty1 ann1, ann1') -> do
                mty2 <- checkElabTm' tyEnv kiEnv tm2
                case mty2 of
                    Just (ty2, ann2) -> do
                        mty3 <- checkElabTm' ((x2,annTy1):(x1,(ty1,ann1)):tyEnv) kiEnv tm3
                        case mty3 of
                            Just (ty3, ann3) -> return $ Just (simplifyExnTy kiEnv $ join ty2 ty3, simplifyExn kiEnv $ ExnUnion ann1' (ExnUnion ann2 ann3))
                            _ -> error "type (Case', 3)"
                    _ -> error "type (Case', 2)"
            _ -> error "type (Case', 1)"
