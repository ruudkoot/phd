{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

module Analysis.Infer where

import Text.Blaze.Html5 (ToMarkup)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import           Analysis.Names
import           Analysis.Common
import qualified Analysis.LambdaUnion as LU
import qualified Analysis.Completion  as C
import           Analysis.Print

import qualified Data.Map    as M

-- | Exception type reconstruction

-- * Environments

type Env = [(Name, (ExnTy, Exn))]

instance Latex (Name, (ExnTy, Exn)) where
    latex (show -> e, (latex -> ty, latex -> exn))
        = "e_" ++ e ++ " : " ++ ty ++ " & " ++ exn

fev :: Env -> [Name]
fev = concatMap (\(_, (ty, exn)) -> fevExnTy ty ++ fevExn exn)

-- * Constraints

data Constr = Exn :<: Name
    deriving Show

instance Latex Constr where
    latex (exn :<: e) = latex exn ++ " \\sqsubseteq e_{" ++ show e ++ "}"

-- * Substitutions

instance Latex (Name, Exn) where
    latex (show -> e, latex -> exn)
        = "e_" ++ e ++ " -|> " ++ exn

-- * Reconstruction

type Result       = (ExnTy, Name, [Constr], KindEnv)
type Complete'    = (C.Complete, ExnTy, Exn, C.Env)
type Reconstruct' = (Reconstruct, ExnTy, Name, [Constr], KindEnv)
type Instantiate' = (ExnTy, KindEnv)

data Reconstruct
    = ReconstructVar   Env KindEnv Expr
                       ExnTy Exn Name
                       Result
    | ReconstructAbs   Env KindEnv Expr
                       Complete' Env Reconstruct' [Name] Exn ExnTy Name
                       Result
    | ReconstructApp   Env KindEnv Expr
                       Reconstruct' Reconstruct' Instantiate' Subst Name [Constr]
                       Result
    | ReconstructCon   Env KindEnv Expr
                       Name
                       Result
    | ReconstructCrash Env KindEnv Expr
                       Result
    | ReconstructSeq   Env KindEnv Expr
                       Result
    | ReconstructFix   Env KindEnv Expr
                       Result
    | ReconstructNil   Env KindEnv Expr
                       Result
    | ReconstructCons  Env KindEnv Expr
                       Result
    | ReconstructCase  Env KindEnv Expr
                       Result

instance ToMarkup Reconstruct where
    toMarkup (ReconstructVar   env kenv tm _ _ _ _)
        = derive "R-Var" [] ""
    toMarkup (ReconstructAbs   env kenv tm _ _ _ _ _ _ _ _)
        = derive "R-Abs" [] ""
    toMarkup (ReconstructApp   env kenv tm (re1,_,_,_,_) (re2,_,_,_,_) _ _ _ _ _)
        = derive "R-App" (map H.toMarkup [re1, re2]) ""
    toMarkup (ReconstructCon   env kenv tm _ _)
        = derive "R-Con" [] ""
    toMarkup (ReconstructCrash env kenv tm _)
        = derive "R-Crash" [] ""
    toMarkup (ReconstructSeq   env kenv tm _)
        = derive "R-Seq" [] ""
    toMarkup (ReconstructFix   env kenv tm _)
        = derive "R-Fix" [] ""
    toMarkup (ReconstructNil   env kenv tm _)
        = derive "R-Nil" [] ""
    toMarkup (ReconstructCons  env kenv tm _)
        = derive "R-Cons" [] ""
    toMarkup (ReconstructCase  env kenv tm _)
        = derive "R-Case" [] ""

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
         let exn2' = solve (kenv1 ++ [(exn1,EXN)] ++ kenv) c1 v exn2
         let t' = C.forallFromEnv kenv1 (ExnArr t1' (ExnVar exn1) t2' exn2')
         e <- fresh
         return $ ReconstructAbs env kenv tm co env' re v exn2' t' e #
            (t', e, [], [(e,EXN)])

reconstruct env kenv tm@(App e1 e2)
    = do re1@(_, t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         re2@(_, t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         ins@(ExnArr t2' (ExnVar exn2') t' exn', kenv') <- instantiate t1
         let subst = [(exn2', ExnVar exn2)] <.> match [] t2 t2'
         e <- fresh
         let c = [substExn' subst exn' :<: e, ExnVar exn1 :<: e] ++ c1 ++ c2
         return $ ReconstructApp env kenv tm re1 re2 ins subst e c #
            (substExnTy' subst  t', e, c
            ,[(e, kindOf (kenv1 ++ kenv) (ExnVar exn1))] ++ kenv' ++ kenv2 ++ kenv1)

reconstruct env kenv tm@(Con b)
    = do e <- fresh
         return $ ReconstructCon env kenv tm e #
            (ExnBool, e, [], [(e,EXN)])

reconstruct env kenv tm@(Crash lbl ty)
    = do (dty', ty', ExnVar exn1, kenv1) <- C.complete [] ty
         return $ ReconstructCrash env kenv tm #
            (ty', exn1, [ExnCon lbl :<: exn1], kenv1)

reconstruct env kenv tm@(Seq e1 e2)
    = do (_, t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         (_, t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         e <- fresh
         return $ ReconstructSeq env kenv tm #
            (t2, e, [ExnVar exn1 :<: e, ExnVar exn2 :<: e] ++ c1 ++ c2
            ,[(e,kindOf (kenv1 ++ kenv) (ExnVar exn1))] ++ kenv2 ++ kenv1)

reconstruct env kenv tm@(Fix e1)   -- FIXME: unknown to be sound (see notes)
    = do (_, t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         (ExnArr t' (ExnVar exn') t'' exn'', kenv') <- instantiate t1
         let subst1 = match [] t'' t'
         let subst2 = [(exn', substExn' subst1 exn'')]
         e <- fresh
         let c = [substExn' (subst2 <.> subst1) exn'' :<: e] ++ c1
         return $ ReconstructFix env kenv tm # 
            (substExnTy' (subst2 <.> subst1) t', e, c
            ,[(e,EXN)] ++ kenv' ++ kenv1)

reconstruct env kenv tm@(Nil ty)
    = do (dty', ty', ExnVar exn1, kenv1) <- C.complete [] ty
         exn2 <- fresh
         -- FIXME: not completely sure about the kind of exn2 (should be ∅)
         return $ ReconstructNil env kenv tm # 
            (ExnList ty' (ExnVar exn1), exn2, [], [(exn2, EXN)] ++ kenv1)

reconstruct env kenv tm@(Cons e1 e2)
    = do (_, t1              , exn1, c1, kenv1) <- reconstruct env kenv e1
         (_, ExnList t2 exn2', exn2, c2, kenv2) <- reconstruct env kenv e2
         let t = join t1 t2
         ex1 <- fresh
         ex2 <- fresh
         -- FIXME: not completely sure about the kind of ex1 and ex2 (should be ∅)
         return $ ReconstructCons env kenv tm # 
            (ExnList t (ExnVar ex1), ex2
            ,[ExnVar exn1 :<: ex1, exn2' :<: ex1, ExnVar exn2 :<: ex2] ++ c1 ++ c2
            ,[(ex1, kindOf (kenv1 ++ kenv) (ExnVar exn1))
            ,(ex2, kindOf (kenv2 ++ kenv) (ExnVar exn2))] ++ kenv2 ++ kenv1)

reconstruct env kenv tm@(Case e1 e2 x1 x2 e3)
    = do (_, ExnList t1 exn1', exn1, c1, kenv1) <- reconstruct env kenv e1
         (_, t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         let env' = (x1, (t1, exn1')) : (x2, (ExnList t1 exn1', ExnVar exn1)) : env
         (_, t3, exn3, c3, kenv3) <- reconstruct env' (kenv1 ++ kenv) e3
         let t = join t2 t3
         exn <- fresh
         let c = [ExnVar exn1 :<: exn, ExnVar exn2 :<: exn, ExnVar exn3 :<: exn]
                    ++ c1 ++ c2 ++ c3
         return $ ReconstructCase env kenv tm # 
            (t, exn, c
            ,[(exn, kindOf (kenv1 ++ kenv) (ExnVar exn1))] ++ kenv3 ++ kenv2 ++ kenv1)
         
-- * Kind reconstruction

kindOf :: KindEnv -> Exn -> Kind
kindOf kenv (ExnVar e)
    | Just k <- lookup e kenv = k
    | otherwise               = error "kindOf: not in scope"
kindOf kenv _
    = error "kindOf: not a variable"

-- * Instantiation

instantiate :: ExnTy -> Fresh (ExnTy, KindEnv)
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

-- * Match (merge, meet)

match :: KindEnv -> ExnTy -> ExnTy -> Subst
match env (ExnBool) (ExnBool)
    = []
match env (ExnForall e k t) (ExnForall e' k' t')
    | k == k'   = match ((e,k) : env) t (substExnTy e' e t')
    | otherwise = error "match: kind mismatch"
-- FIXME: correct definition for lists?
match env (ExnList t exn) (ExnList t' exn')
    = let (e, es) = deapply exn'
       in [(e, reapply env es exn)] <.> match env t t'
match env t@(ExnArr t1 (ExnVar exn1) t2 exn2) t'@(ExnArr t1' (ExnVar exn1') t2' exn2')
    | exnTyEq env t1 t1', exn1 == exn1'
        = let (e, es) = deapply exn2'
           in [(e, reapply env es exn2)] <.> match env t2 t2'
    | otherwise = error $ "match: function space (t = "   ++ show t
                          ++ "; t' = "  ++ show t' ++ "; env = " ++ show env
match env t t'
    = error $ "match: t = " ++ show t ++ "; t' = " ++ show t' ++ "; env = " ++ show env
    
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
