{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns      #-}

module Infer where

-- TODO: reconstruct derivation tree

import           Names
import           Common
import qualified LambdaUnion as LU
import qualified Completion  as C
import           Latex

import qualified Data.Map    as M

-- | Exception type reconstruction

-- * Environments

type Env = [(Name, (ExnTy, Exn))]

instance Latex (Name, (ExnTy, Exn)) where
    lhs2tex (show -> e, (lhs2tex -> ty, lhs2tex -> exn))
        = "e_" ++ e ++ " : " ++ ty ++ " & " ++ exn

fev :: Env -> [Name]
fev = concatMap (\(_, (ty, exn)) -> fevExnTy ty ++ fevExn exn)

-- * Constraints

data Constr = Exn :<: Name
    deriving Show

-- * Reconstruction

debug cs fs = msg [ unlines (map f fs ++ ["\\begin{code}"] ++ cs ++ ["\\end{code}"])
    ] where f x = "%format " ++ x

-- TODO: store KindEnv, Env in the monad
reconstruct :: Env -> KindEnv -> Expr -> FreshLog Log (ExnTy, Name, [Constr], KindEnv)

reconstruct env kenv (Var x)
    = do let Just (t, exn) = lookup x env
         e <- fresh
         
         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             e_" ++ show x,
            "    =  let  ty & exn = env x ~> " ++ lhs2tex t ++ " & " ++ lhs2tex exn,
            "            e_" ++ show e ++ " be fresh",
            "       in   (ty, e_" ++ show e ++ ", Set (exn :<: e_" ++ show e ++ "),"
                ++ "[e_" ++ show e ++ " : DenoteEnv exn kenv])",
            "            ~> (" ++ lhs2tex t ++ ", " ++ "e_" ++ show e
                ++ ", Set (" ++ lhs2tex exn ++ " :<: e_" ++ show e ++ "), "
                ++ lhs2tex [(e, kindOf kenv exn)] ++ ")"
          ] ["e_" ++ show e]

         return (t, e, [exn :<: e], [(e, kindOf kenv exn)])

reconstruct env kenv (Abs x ty tm)
    = do (t1', ExnVar exn1, kenv1) <- C.complete [] ty
         let env' = (x, (t1', ExnVar exn1)) : env
         (t2', exn2, c1, kenv2) <- reconstruct env' (kenv1 ++ kenv) tm
         let v = [exn1] ++ map fst kenv1 ++ fev env
         -- FIXME: is this the correct environment we are passing here?
         let exn2' = solve (kenv1 ++ [(exn1,EXN)] ++ kenv) c1 v exn2
         let t' = C.forallFromEnv kenv1 (ExnArr t1' (ExnVar exn1) t2' exn2')
         e <- fresh

         debug [ -- FIXME
            "reconstruct env kenv (Abs x ty tm) =",
            "    let  (ty'_1, exn_1, kenv_1)  = complete [] ty",
            "                                 = (" ++ lhs2tex t1' ++ ", " ++ show exn1
                ++ ", " ++ show kenv1 ++ ")",
            "         (ty'_2, exn_2, C_1, kenv_2)  = reconstruct (env, " ++ show x
                ++ " : " ++ lhs2tex t1' ++ " & " ++ show exn1
                ++ ") (kenv1 ++ kenv) (tm)",
            "                                      = (" ++ lhs2tex t2' ++ ", "
                ++ show exn2 ++ ", " ++ show c1 ++ ", " ++ show kenv2 ++ ")",
            "         v  = [exn1] ++ map fst kenv1 ++ fev env",
            "         exn'_2  = solve (kenv1 ++ [(exn1,EXN)] ++ kenv) c1 v exn2",
            "                 = ...",
            "         ty'     = ...",
            "         e be fresh",
            "    in (,,,)"
          ] ["ty'_1", "exn_1", "kenv_1"
            ,"ty'_2", "exn_2", "C_1", "kenv_2"
            , "exn'_2"
            ]

         return (t', e, [], [(e,EXN)])

reconstruct env kenv (App e1 e2)
    = do (t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         (t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         (ExnArr t2' (ExnVar exn2') t' exn', kenv') <- instantiate t1
         let subst = [(exn2', ExnVar exn2)] <.> merge [] t2 t2'
         e <- fresh
         let c = [substExn' subst exn' :<: e, ExnVar exn1 :<: e] ++ c1 ++ c2

         debug [ -- FIXME
            "R-App"
            ] []

         return (substExnTy' subst  t', e, c
                ,[(e, kindOf (kenv1 ++ kenv) (ExnVar exn1))] ++ kenv' ++ kenv2 ++ kenv1)

reconstruct env kenv (Con b)
    = do e <- fresh
    
         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             " ++ show b,
            "    =  let  e_" ++ show e ++ " be fresh",
            "       in   (ExnBool, e_" ++ show e ++ ", EmptySet, "
                ++ lhs2tex [(e,EXN)] ++ ")"
          ] ["e_" ++ show e]
    
         return (ExnBool, e, [], [(e,EXN)])

reconstruct env kenv (Crash lbl ty)
    = do (ty', ExnVar exn1, kenv1) <- C.complete [] ty

         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             bottom_" ++ lbl ++ " : " ++ lhs2tex ty,
            "    =  let  (ty, e, kenv_1) = complete [] (" ++ lhs2tex ty ++ ")"
                ++ " ~> (" ++ lhs2tex ty' ++ ", e_" ++ show exn1 ++ ", "
                ++ lhs2tex kenv1 ++ ")",
            "       in   (ty, e, Set (Set " ++ lbl ++ " :<: e), kenv_1) ~> ("
                ++ lhs2tex ty' ++ ", e_" ++ show exn1 ++ ", Set (Set " ++ lbl
                ++ " :<: e_" ++ show exn1 ++ "), " ++ lhs2tex kenv1 ++ ")"
          ] ["bottom_" ++ lbl]

         return (ty', exn1, [ExnCon lbl :<: exn1], kenv1)

reconstruct env kenv (Seq e1 e2)
    = do (t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         (t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         e <- fresh
         
         debug [ -- FIXME
            "R-Seq"
            ] []
                  
         return (t2, e, [ExnVar exn1 :<: e, ExnVar exn2 :<: e] ++ c1 ++ c2
                ,[(e,kindOf (kenv1 ++ kenv) (ExnVar exn1))] ++ kenv2 ++ kenv1)

reconstruct env kenv (Fix e1)   -- FIXME: unknown to be sound (see notes)
    = do (t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         (ExnArr t' (ExnVar exn') t'' exn'', kenv') <- instantiate t1
         let subst1 = merge [] t'' t'
         let subst2 = [(exn', substExn' subst1 exn'')]
         e <- fresh
         let c = [substExn' (subst2 <.> subst1) exn'' :<: e] ++ c1

         debug [ -- FIXME
            "R-Fix"
            ] []

         return (substExnTy' (subst2 <.> subst1) t', e, c
                ,[(e,EXN)] ++ kenv' ++ kenv1)

reconstruct env kenv (Nil ty)
    = do (ty', ExnVar exn1, kenv1) <- C.complete [] ty
         exn2 <- fresh
         
         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             (Nil (" ++ lhs2tex ty ++ "))",
            "    =  let  (ty, e, kenv_1) = complete [] (" ++ lhs2tex ty ++ ")"
                ++ " ~> (" ++ lhs2tex ty' ++ ", e_" ++ show exn1 ++ ", "
                ++ lhs2tex kenv1 ++ ")",
            "            e_" ++ show exn2 ++ " be fresh",
            "       in   (" ++ lhs2tex (ExnList ty' (ExnVar exn1)) ++ ", e_"
                ++ show exn2 ++ ", EmptySet, " ++ lhs2tex ([(exn2, EXN)] ++ kenv1) ++ ")"
          ] ["exn_1", "kenv_1", "e_" ++ show exn2]

         -- FIXME: not completely sure about the kind of exn2 (should be ∅)
         return (ExnList ty' (ExnVar exn1), exn2, [], [(exn2, EXN)] ++ kenv1)

reconstruct env kenv (Cons e1 e2)
    = do (t1              , exn1, c1, kenv1) <- reconstruct env kenv e1
         (ExnList t2 exn2', exn2, c2, kenv2) <- reconstruct env kenv e2
         let t = join t1 t2
         ex1 <- fresh
         ex2 <- fresh

         debug [ -- FIXME
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             (Cons (" ++ lhs2tex e1 ++ ") (" ++ lhs2tex e2 ++ "))",
            "    =  let  (ty_1, e_1, C_1, kenv_1)  =   reconstruct env kenv ("
                ++ lhs2tex e1 ++ ")",
            "                                      ~>  ...",
            "            (ExnList ty_2 e'_2, e_2, C_2, kenv_2)  = reconstruct env kenv tm_2 ~> ",
            "            ty = join ty_1 ty_2",
            "            e_1 be fresh",
            "            e_2 be fresh",
            "       in   Y"
          ] ["ty_1", "ty_2", "e_1", "e_2", "C_1", "C_2", "kenv_1", "kenv_2"]

         -- FIXME: not completely sure about the kind of ex1 and ex2 (should be ∅)
         return (ExnList t (ExnVar ex1), ex2
            ,[ExnVar exn1 :<: ex1, exn2' :<: ex1, ExnVar exn2 :<: ex2] ++ c1 ++ c2
            ,[(ex1, kindOf (kenv1 ++ kenv) (ExnVar exn1))
             ,(ex2, kindOf (kenv2 ++ kenv) (ExnVar exn2))] ++ kenv2 ++ kenv1)

reconstruct env kenv (Case e1 e2 x1 x2 e3)
    = do (ExnList t1 exn1', exn1, c1, kenv1) <- reconstruct env kenv e1
         (t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         let env' = (x1, (t1, exn1')) : (x2, (ExnList t1 exn1', ExnVar exn1)) : env
         (t3, exn3, c3, kenv3) <- reconstruct env' (kenv1 ++ kenv) e3
         let t = join t2 t3
         exn <- fresh
         let c = [ExnVar exn1 :<: exn, ExnVar exn2 :<: exn, ExnVar exn3 :<: exn]
                    ++ c1 ++ c2 ++ c3

         debug [ -- FIXME
            "R-Case"
            ] []

         return (t, exn, c
                ,[(exn, kindOf (kenv1 ++ kenv) (ExnVar exn1))]
                    ++ kenv3 ++ kenv2 ++ kenv1)
         
-- * Kind reconstruction

kindOf :: KindEnv -> Exn -> Kind
kindOf kenv (ExnVar e)
    | Just k <- lookup e kenv = k
    | otherwise               = error "kindOf: not in scope"
kindOf kenv _
    = error "kindOf: not a variable"

-- * Instantiation

instantiate :: ExnTy -> FreshLog Log (ExnTy, KindEnv)
instantiate (ExnForall e k t)
    = do e' <- fresh
         (t', kenv) <- instantiate t
         return (substExnTy e e' t', [(e', k)] ++ kenv)
instantiate t
    = do return (t, [])

-- * Join / subtyping

join :: ExnTy -> ExnTy -> ExnTy
join ExnBool ExnBool
    = ExnBool
join (ExnForall x k t) (ExnForall x' k' t')
    | k == k'   = ExnForall x k (join t (substExnTy x' x t'))
    | otherwise = error "join: kind mismatch"
join (ExnList t exn) (ExnList t' exn')
    = ExnList (join t t') (ExnUnion exn exn')
join (ExnArr t1 (ExnVar exn1) t2 exn2) (ExnArr t1' (ExnVar exn1') t2' exn2')
    | exnTyEq (error "don't use me") t1 t1', exn1 == exn1'
        -- TODO: are we sure no alpha-renaming is needed?
        = ExnArr t1 (ExnVar exn1) (join t2 t2') (ExnUnion exn2 exn2')
    | otherwise = error $ "join: function space"
join t t'
    = error $ "join: t = " ++ show t ++ "; t' = " ++ show t'

-- * Merge / match

merge :: KindEnv -> ExnTy -> ExnTy -> Subst
merge env (ExnBool) (ExnBool)
    = []
merge env (ExnForall e k t) (ExnForall e' k' t')
    | k == k'   = merge ((e,k) : env) t (substExnTy e' e t')
    | otherwise = error "merge: kind mismatch"
-- FIXME: correct definition for lists?
merge env (ExnList t exn) (ExnList t' exn')
    = let (e, es) = deapply exn'
       in [(e, reapply env es exn)] <.> merge env t t'
merge env t@(ExnArr t1 (ExnVar exn1) t2 exn2) t'@(ExnArr t1' (ExnVar exn1') t2' exn2')
    | exnTyEq env t1 t1', exn1 == exn1'
        = let (e, es) = deapply exn2'
           in [(e, reapply env es exn2)] <.> merge env t2 t2'
    | otherwise = error $ "merge: function space (t = "   ++ show t
                          ++ "; t' = "  ++ show t' ++ "; env = " ++ show env
merge env t t'
    = error $ "merge: t = " ++ show t ++ "; t' = " ++ show t' ++ "; env = " ++ show env
    
-- NOTE: here the fully-appliedness and left-to-rightness comes into play
-- TODO: check this restriction in never violated
-- TODO: encode this restriction into Exn?
deapply :: Exn -> (Name, [Name])
deapply (ExnVar e) = (e, [])
deapply (ExnApp e1 (ExnVar e2))
    = let (e, es) = deapply e1
       in (e, es ++ [e2])           -- TODO: keep this in reverse order?
deapply _ = error "deapply: malformed"

reapply :: KindEnv -> [Name] -> Exn -> Exn
reapply env es exn
    = foldr (\e r -> ExnAbs e (lookup' "reapply" e env) r) exn es
    
-- * Constraint solving

solve :: KindEnv -> [Constr] -> [Name] -> Name -> Exn
solve env cs xs e =
    let dependencies :: M.Map Name [Constr]
        dependencies = foldr f M.empty cs
            where f c@(exn :<: _) d
                    = foldr (\e -> M.insertWith (++) e [c]) d (fevExn exn)
        
        analysis', analysis'', analysis :: M.Map Name Exn
        analysis' = foldr f M.empty cs
            -- FIXME: we need an abstracted Empty depending on the kind...
            where f (_ :<: e) d = M.insert e ExnEmpty d
        analysis'' = foldr f analysis' xs
            where f e d = M.insert e (ExnVar e) d
        analysis = M.insert e ExnEmpty analysis''
        
        f :: Constr -> M.Map Name Exn -> ([Constr], M.Map Name Exn)
        f (exn :<: e) analysis
                -- FIXME: need a whole lot more βη∪-normalization here
                = let exn1 = interpret analysis exn
                      exn2 = mapLookup "exn2" analysis e
                   in -- FIXME: is this environment sufficient? the call to solve
                      --        in reconstruct suggests perhaps not!
                      if isIncludedIn env exn1 exn2
                      then ( [], analysis )
                      else ( M.findWithDefault [] e dependencies
                           -- FIXME: should the above lookup ever be allowed to fail?
                           --        (it does!)
                           , M.insert e (exnNormalize (ExnUnion exn1 exn2)) analysis )
     in mapLookup "solve result" (worklist f cs analysis) e

-- TODO: move to LambdaUnion
isIncludedIn :: KindEnv -> Exn -> Exn -> Bool
isIncludedIn env exn1 exn2 = exnEq env (ExnUnion exn1 exn2) (exn2)

-- TODO: move to LambdaUnion?
interpret :: M.Map Name Exn -> Exn -> Exn
interpret env (ExnEmpty)
    = ExnEmpty
interpret env (ExnUnion e1 e2)
    = ExnUnion (interpret env e1) (interpret env e2)
interpret env (ExnCon lbl)
    = ExnCon lbl
interpret env (ExnVar e)
    -- FIXME: should this lookup ever fail? it does!
    = M.findWithDefault ExnEmpty e env
interpret env (ExnApp e1 e2)
    = ExnApp (interpret env e1) (interpret env e2)
interpret env (ExnAbs x k e)
    = ExnAbs x k (interpret (M.delete x env) e)

worklist :: (c -> a -> ([c], a)) -> [c] -> a -> a
worklist f [] x     = x
worklist f (c:cs) x = let (cs', x') = f c x in worklist f (cs ++ cs') x'

mapLookup :: (Ord k, Show k, Show a) => String -> M.Map k a -> k -> a
mapLookup msg m k = case M.lookup k m of
    Nothing -> error $ "mapLookup @ " ++ msg ++ ": could not find key '" ++ show k ++ "' in " ++ show m
    Just v  -> v
