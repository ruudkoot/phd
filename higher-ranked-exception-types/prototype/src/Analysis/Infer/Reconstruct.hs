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
            ( annAbsFromEnv (reverse kenv1) $ Abs' x t1' (ExnVar exn1) etm'
            , t', ExnEmpty                                                 )

reconstruct env kenv tm@(App e1 e2)
    = do re1@(_, etm1, t1, exn1) <- reconstruct env kenv e1
         re2@(_, etm2, t2, exn2) <- reconstruct env kenv e2
         ins@(ExnArr t2' (ExnVar exn2') t' exn', kenv') <- instantiate t1
         subst' <- match [] t2 t2'             -- ^ FIXME: only used for elaboration
         let subst = [(exn2', exn2)] <.> subst'
         let exn = ExnUnion (substExn' subst exn') exn1
         return $ ReconstructApp env kenv tm re1 re2 ins subst' subst #
            ( App' (annAppFromEnv kenv' subst etm1) etm2
            , simplifyExnTy kenv $ substExnTy' subst  t'
            , simplifyExn   kenv $                    exn)

reconstruct env kenv tm@(Fix e1)
    = do re@(_, ee1, t1, exn1) <- reconstruct env kenv e1
         ins@(ExnArr t' (ExnVar exn') t'' exn'', kenv') <- instantiate t1
                                                -- ^ FIXME: only used for elaboration

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
                tr@(_,_,_,_,_,_,_,_,subst_i,_,t_j,_,exn_j) <- f t_i exn_i
                if exnTyEq kenv t_i t_j && exnEq kenv exn_i exn_j
                then return (trace, t_i, exn_i, subst_i)
                else kleeneMycroft (trace ++ [tr]) t_j exn_j

         t0 <- C.bottomExnTy (underlying t')
         let exn0 = ExnEmpty
         km@(_, t_w, exn_w, subst_w) <- kleeneMycroft [] t0 exn0

         return $ ReconstructFix env kenv tm re ins t0 exn0 km #
            ( Fix' (annAppFromEnv kenv' subst_w ee1)
            , simplifyExnTy kenv t_w
            , simplifyExn kenv (ExnUnion exn_w exn1)
            )

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
    
-- | Type checking of elaborated terms

-- TODO: move to Common? (only here because we need bottomExnTy...)

-- * With subtyping coercions (resembles decalrative type system)

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
checkElabTm' tyEnv kiEnv (App' tm1 tm2)
    = do mty1 <- checkElabTm' tyEnv kiEnv tm1
         case mty1 of
            Just (ExnArr ty1 ann1 ty ann, ann') -> do
                mty2 <- checkElabTm' tyEnv kiEnv tm2
                case mty2 of
                    Just (ty2, ann2) -> do
                        if isSubtype kiEnv ty2 ty1 && isSubeffect kiEnv ann2 ann1 then
                            return $ Just (ty, simplifyExn kiEnv $ ExnUnion ann ann')
                        else
                            error "subtype (App')"
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
                    return $ Just (ty2, ann2)
                else
                    error "fixpoint (Fix')"
            _ -> error "type (Fix')"
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
            
-- * Checking of subtyping and subeffecting

-- TODO: "merge" with exnEq and exnTyEq?

isSubeffect :: KindEnv -> Exn -> Exn -> Bool
isSubeffect env ann1 ann2 = exnEq env (ExnUnion ann1 ann2) ann2

isSubtype :: KindEnv -> ExnTy -> ExnTy -> Bool
isSubtype env ExnBool ExnBool = True
isSubtype env ExnInt  ExnInt  = True
isSubtype env (ExnArr ty1 ann1 ty2 ann2) (ExnArr ty1' ann1' ty2' ann2')
    = isSubtype env ty1' ty1 && isSubeffect env ann1' ann1
        && isSubtype env ty2 ty2' && isSubeffect env ann2 ann2'
isSubtype env (ExnList ty ann) (ExnList ty' ann')
    = isSubtype env ty ty' && isSubeffect env ann ann'
isSubtype env (ExnForall e k ty) (ExnForall e' k' ty')
    = k == k' && isSubtype ((e,k):env) ty (substExnTy e' e ty')
    
-- * Kind checking of annotation

-- TODO: move somewhere else

checkKind :: KindEnv -> Exn -> Maybe Kind
checkKind env ExnEmpty
    = return EXN
checkKind env (ExnUnion exn1 exn2)
    = do k1 <- checkKind env exn1
         k2 <- checkKind env exn2
         if k1 == k2 then
            return k1
         else
            error "kind (ExnUnion)"
checkKind env (ExnCon _)
    = return EXN
checkKind env (ExnVar e)
    = case lookup e env of
        Just k -> return k
        _      -> error "unbound (ExnVar)"
checkKind env (ExnApp exn1 exn2)
    = do (k2' :=> k1) <- checkKind env exn1
         k2           <- checkKind env exn2
         if k2 == k2' then
            return k1
         else
            error "kind (ExnApp)"
checkKind env (ExnAbs e k exn)
    = do () <- case lookup e env of
                 Nothing -> return ()
                 _       -> error "shadowing (ExnAbs)"
         k2 <- checkKind ((e,k):env) exn
         return (k :=> k2)
