{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}

module Common  where

import Data.List (intersperse)
import qualified Data.Map as Map
import Data.Map (Map, insertWith)
import Data.Set (Set, (\\), delete, empty, member, singleton, toList, union, unions)
import qualified Data.Set as Set

import Util.List

import Language.Haskell.Exts.Annotated

import PrintType
import Refinement

import Control.Monad
import TCMonad

-- | Basic types

tyBool ref = TyCon (Phi ref) (UnQual NoPhi (Ident NoPhi "Bool"))

-- | Annotation-related

-- FIXME: Change type of Env to [(forall l. Name l, Type Phi)] instead?

stripNameAnn :: Name l -> Name Phi
stripNameAnn (Ident  _ s) = Ident  NoPhi s
stripNameAnn (Symbol _ s) = Symbol NoPhi s

unstripNameAnn :: Name Phi -> Name l
unstripNameAnn (Ident  NoPhi s) = Ident (error "unstripNameAnn: Ident")  s
unstripNameAnn (Symbol NoPhi s) = Ident (error "unstripNameAnn: Symbol") s

stripQNameAnn :: QName l -> QName Phi
stripQNameAnn (Qual    _ _ _ ) = error "stripQNameAnn: qualified name"
stripQNameAnn (UnQual  _ name) = UnQual  NoPhi (stripNameAnn name)
stripQNameAnn (Special _ con ) = Special NoPhi (stripSpecialConAnn con)

stripSpecialConAnn :: SpecialCon l -> SpecialCon Phi
stripSpecialConAnn (UnitCon  _            ) = UnitCon  NoPhi
stripSpecialConAnn (ListCon  _            ) = ListCon  NoPhi
stripSpecialConAnn (TupleCon _ boxed arity) = TupleCon NoPhi boxed arity
stripSpecialConAnn (Cons     _            ) = Cons     NoPhi

stripTyVarBindAnn :: TyVarBind l -> TyVarBind Phi
stripTyVarBindAnn (UnkindedVar _ name) = UnkindedVar NoPhi (stripNameAnn name)

stripTypeAnn :: Type l -> Type Phi
stripTypeAnn = error "stripTypeAnn"

applyExpSubst :: Show l => Map (Name Phi) (Exp l) -> Exp l -> Exp l
applyExpSubst subst e@(Var l1 (UnQual l2 name'))
    | Just e' <- Map.lookup (stripNameAnn name') subst = e'
    | otherwise                                        = e
applyExpSubst subst e@(Con _ _)
    = e
applyExpSubst subst e@(Lit _ _)
    = e
applyExpSubst subst e@(App l e1 e2)
    = App l (applyExpSubst subst e1) (applyExpSubst subst e2)
applyExpSubst subst e@(InfixApp l e1 qop e2)
    = InfixApp l (applyExpSubst subst e1) qop (applyExpSubst subst e2) -- FIXME: QOp also..
applyExpSubst subst e@(NegApp l e1)
    = NegApp l (applyExpSubst subst e1)
applyExpSubst subst e@(Lambda l ps e1)
    = Lambda l ps (applyExpSubst subst e1) -- FIXME: ignores bindings
applyExpSubst subst e@(Let l (BDecls l' ds) e1)
    = Let l (BDecls l' (map (\(PatBind l'' p mt (UnGuardedRhs l''' e2) mbs) -> PatBind l'' p mt (UnGuardedRhs l''' (applyExpSubst subst e2)) mbs) ds)) (applyExpSubst subst e1)
applyExpSubst subst e@(Case l e1 as)
    = Case l (applyExpSubst subst e1) (map (\(Alt l' p (UnGuardedAlt l'' e2) mb) -> Alt l' p (UnGuardedAlt l'' (applyExpSubst subst e2)) mb) as)
applyExpSubst subst e@(Tuple l es)
    = Tuple l (map (applyExpSubst subst) es)
applyExpSubst subst e@(List l es)
    = List l (map (applyExpSubst subst) es)
applyExpSubst subst e@(Paren l e1)
    = Paren l (applyExpSubst subst e1)
applyExpSubst _     e
    = error ("applyExpSubst: " ++ show e)

-- | Fresh variable supply

type Fresh = [Name Phi]

freshVars :: Fresh
freshVars = map (Ident NoPhi . ('?':) . show) [0..]

freshName :: TC (Name Phi)
freshName = do fr <- freshTC
               return (Ident NoPhi ('?' : show fr))
               
freshTV = do f <- freshName
             return (TyVar NoPhi f)
             
freshRV = do f <- freshName
             return (RefVar f)

-- | Simple type environment

type Env = [(QName Phi, Type Phi)]

instance Substitutable Subst Env where
    theta `applySubst` env = map (\(name, ty) -> (name, theta `applySubst` ty)) env

-- | Constraints

data Constr
    = (:=:) (Type Phi) (Type Phi)
    deriving (Eq)
    
instance Show Constr where
    show (t1 :=: t2) = printType t1 ++ " = " ++ printType t2

instance Substitutable Subst Constr where
    theta `applySubst` (s :=: t) = (theta `applySubst` s) :=: (theta `applySubst` t)

instance Substitutable Subst [Constr] where
    applySubst theta = map (applySubst theta)


-- | Substitutions

class Substitutable s t where
    applySubst :: s -> t -> t
    
data Subst = Subst { tySubst  :: Map (Name Phi) (Type Phi)
                   , annSubst :: Map (Name Phi) (Name Phi) }

instance Show Subst where
    show (Subst { tySubst = ts, annSubst = as })
        = let t = concatMap (\(x,t) -> prettyPrint x ++ " ↦ " ++ printType t ++ "\n") . Map.toList $ ts
              a = concatMap (\(x,t) -> "\n" ++ prettyPrint x ++ " ↦ " ++ prettyPrint t) . Map.toList $ as
           in t ++ ". . . . . . . . . . . . . ." ++ a
           
-- * Definitition for Refinements (to avoid circular imports)

instance Substitutable Subst RefConstr where
    theta `applySubst` (r1 :<: r2) = (theta `applySubst` r1) :<: (theta `applySubst` r2)
    
instance Substitutable Subst [RefConstr] where
    applySubst theta = map (applySubst theta)

-- instance (Substitutable s t) => Substitutable s [t] where
--    applySubst theta = map (applySubst theta)

instance Substitutable Subst Refinement where
    theta `applySubst` (RefVar name) = RefVar (Map.findWithDefault name name (annSubst theta))
    theta `applySubst` x             = x

-- * Compose substitutions

infixr 9 $.

($.) :: Subst -> Subst -> Subst
theta $. gamma = (theta `substApply` gamma) `substUnion` theta
    where substApply :: Subst -> Subst -> Subst
          substApply s@(Subst t1 a1) (Subst t2 a2) = Subst (Map.map (s `applySubst`) t2) (Map.map (a1 $@^) a2)
          
          ($@^) :: Map (Name Phi) (Name Phi) -> Name Phi -> Name Phi
          s $@^ n = Map.findWithDefault n n s

          substUnion :: Subst -> Subst -> Subst
          substUnion (Subst t1 a1) (Subst t2 a2) = Subst (t1 `Map.union` t2) (a1 `Map.union` a2)

-- * Apply substitution to type

instance Substitutable Subst (Type Phi) where
    theta `applySubst` tv@(TyVar NoPhi alpha)
        = Map.findWithDefault tv alpha (tySubst theta)
    theta `applySubst` tc@(TyCon phi con)
        = TyCon (theta `applySubst` phi) con
    theta `applySubst` (TyFun phi tau1 tau2)
        = TyFun (theta `applySubst` phi) (theta `applySubst` tau1) (theta `applySubst` tau2)
    theta `applySubst` (TyList phi tau)
        = TyList (theta `applySubst`phi) (theta `applySubst` tau)
    theta `applySubst` (TyTuple phi Boxed taus)
        = TyTuple (theta `applySubst` phi) Boxed (map (theta `applySubst`) taus)
    theta `applySubst` (TyApp phi tau1 tau2)
        = TyApp (theta `applySubst` phi) (theta `applySubst` tau1) (theta `applySubst` tau2)
    theta `applySubst` (TyForall uc (Just varBinds) ctx tau1)
        = let theta' = Subst { tySubst = foldr (\(UnkindedVar _ k) r -> k `Map.delete` r) (tySubst theta) varBinds
                             , annSubst = Map.empty
                             }
           in TyForall uc (Just varBinds) ctx (theta' `applySubst` tau1)
       
instance Substitutable Subst Phi where
    sigma `applySubst` (Phi (RefVar rv))
        = Phi (RefVar (Map.findWithDefault rv rv (annSubst sigma)))

-- | Free type variables & occurs check

-- * Free type variables of a type (scheme)

ftv :: Type Phi -> Set (Name Phi)

ftv (TyForall _ (Just varBinds) _ t)
    = foldr (\(UnkindedVar _ name) names -> name `delete` names) (ftv t) varBinds
ftv (TyVar _ name)
    = singleton name
ftv (TyFun _ tau1 tau2)
    = ftv tau1 `union` ftv tau2
ftv (TyCon _ _   )
    = empty
ftv (TyList _ a)
    = ftv a
ftv (TyTuple _ Boxed as)
    = foldr (union . ftv) empty as
ftv (TyApp _ t a)
    = ftv t `union` ftv a
    
-- * Free annotation variables of a type (scheme)

fav :: Type Phi -> Set (Name Phi)

fav (TyForall _ (Just varBinds) _ t)
    = foldr (\(UnkindedVar _ name) names -> name `delete` names) (fav t) varBinds
fav (TyVar NoPhi _)
    = empty
fav (TyFun phi tau1 tau2)
    = fav' phi `union` fav tau1 `union` fav tau2
fav (TyCon phi _)
    = fav' phi
fav (TyList phi a)
    = fav' phi `union` fav a
fav (TyTuple phi Boxed as)
    = fav' phi `union` foldr (union . fav) empty as
fav (TyApp NoPhi t a)
    = fav t `union` fav a

fav' :: Phi -> Set (Name Phi)

fav' (Phi (RefVar a))
    = singleton a

-- * Free type and annotation variables in a type environment

ftvEnv :: Env -> Set (Name Phi)
ftvEnv gamma = foldr (\(_, tau) ns -> ftv tau `union` ns) empty gamma

favEnv :: Env -> Set (Name Phi)
favEnv gamma = foldr (\(_, tau) ns -> fav tau `union` ns) empty gamma

-- | Names uses

uses :: (Ord l, Show l) => Exp l -> Set (Name l)

uses (Var _ (UnQual _ name))
    = singleton name
uses (Con _ (UnQual _ name))
    = empty
uses (Lit _ _)
    = empty
uses (Tuple _ es)
    = foldr (union . uses) empty es
uses (List _ es)
    = foldr (union . uses) empty es
uses (App _ e1 e2)
    = uses e1 `union` uses e2
uses (InfixApp _ e1 _ e2) -- FIXME: ignores QOp
    = uses e1 `union` uses e2
uses (Lambda _ pats e)
    = uses e \\ foldr (\(PVar _ name) names -> name `delete` names) empty pats
uses (Let _ (BDecls _ pbs) e2)
    = let (ns, es) = unzip (map (\(PatBind _ (PVar _ name) _ (UnGuardedRhs _ e1) _) -> (singleton name, uses e1)) pbs)
       in (uses e2 `union` unions es) \\ unions ns
uses (If _ g e1 e2)
    = uses g `union` uses e1 `union` uses e2
uses (Case _ e alts)
    = uses e `union` foldr (\(Alt _ _ (UnGuardedAlt _ e) _) r -> uses e `union` r) empty alts
uses (Paren _ e)
    = uses e
uses x
    = error ("uses: " ++ show x)

-- * Unification variable substitution in type and annotation for instantiation    

infixr 0 $@*

($@*) :: Map (Name Phi) (Name Phi) -> Type Phi -> Type Phi
sigma $@* (TyForall NoPhi (Just varBinds) Nothing tau1)
    = let sigma' = foldr (\(UnkindedVar NoPhi k) r -> k `Map.delete` r) sigma varBinds
       in TyForall NoPhi (Just varBinds) Nothing (sigma' $@* tau1)
sigma $@* (TyFun (Phi phi) tau1 tau2)
    = TyFun (Phi (sigma $@*^ phi)) (sigma $@* tau1) (sigma $@* tau2)
sigma $@* (TyTuple (Phi phi) Boxed taus)
    = TyTuple (Phi (sigma $@*^ phi)) Boxed (map (sigma $@*) taus)
sigma $@* (TyList (Phi phi) tau)
    = TyList (Phi (sigma $@*^ phi)) (sigma $@* tau)
sigma $@* (TyApp NoPhi tau1 tau2)
    = TyApp NoPhi (sigma $@* tau1) (sigma $@* tau2)
sigma $@* (TyVar NoPhi alpha)
    = TyVar NoPhi (Map.findWithDefault alpha alpha sigma)
sigma $@* (TyCon (Phi phi) con)
    = TyCon (Phi (sigma $@*^ phi)) con
sigma $@* x
    = error ("$@*: " ++ prettyPrint x)
