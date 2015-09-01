module Common  where

import Data.List (intersperse)
import qualified Data.Map as Map
import Data.Map (Map, insertWith)
import Data.Set (Set, (\\), delete, empty, member, singleton, toList, union)
import qualified Data.Set as Set

import Util.List

import Language.Haskell.Exts.Annotated

import PrintType
import Refinement

import Abstract.List hiding (Cons)

-- | Basic types

-- tyUnit = TyCon NoPhi (Special NoPhi (UnitCon NoPhi))
tyBool ref = TyCon (Phi ref) (UnQual NoPhi (Ident NoPhi "Bool"))
-- tyInt  = TyCon NoPhi (UnQual NoPhi (Ident NoPhi "Int"))
-- (-->)  = TyFun NoPhi

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

-- | Simple type environment

type Env = [(QName Phi, Type Phi)]

-- | Constraints

data Constr
    = (:=:!) String (Type Phi) (Type Phi)
    deriving (Eq)
    
(=:) = (:=:!) "?"
    
instance Show Constr where
    show ((:=:!) dbg t1 t2) = printType t1 ++ " = " ++ printType t2 ++ " | " ++ dbg ++ "\n"
    
-- | Substitutions

data Subst = Subst { tySubst  :: Map (Name Phi) (Type Phi)
                   , annSubst :: Map (Name Phi) (Name Phi) }

instance Show Subst where
    show (Subst { tySubst = ts, annSubst = as })
        = let t = concatMap (\(x,t) -> prettyPrint x ++ " ↦ " ++ printType t ++ "\n") . Map.toList $ ts
              a = concatMap (\(x,t) -> "\n" ++ prettyPrint x ++ " ↦ " ++ prettyPrint t) . Map.toList $ as
           in t ++ ". . . . . . . . . . . . . ." ++ a

-- * Compose substitutions

infixr 9 $.

($.) :: Subst -> Subst -> Subst
sigma $. gamma = (sigma `substApply` gamma) `substUnion` sigma
    where substApply :: Subst -> Subst -> Subst
          substApply s@(Subst t1 a1) (Subst t2 a2) = Subst (Map.map (s $@) t2) (Map.map (a1 $@^) a2)
          
          ($@^) :: Map (Name Phi) (Name Phi) -> Name Phi -> Name Phi
          s $@^ n = Map.findWithDefault n n s

          substUnion :: Subst -> Subst -> Subst
          substUnion (Subst t1 a1) (Subst t2 a2) = Subst (t1 `Map.union` t2) (a1 `Map.union` a2)

-- * Apply substitution to type

infixr 0 $@

($@) :: Subst -> Type Phi -> Type Phi
sigma $@ tv@(TyVar NoPhi alpha)
    = Map.findWithDefault tv alpha (tySubst sigma)
sigma $@ tc@(TyCon phi con)
    = TyCon (sigma $@+ phi) con
sigma $@ (TyFun phi tau1 tau2)
    = TyFun (sigma $@+ phi) (sigma $@ tau1) (sigma $@ tau2)
sigma $@ (TyList phi tau)
    = TyList (sigma $@+ phi) (sigma $@ tau)
sigma $@ (TyTuple phi Boxed taus)
    = TyTuple (sigma $@+ phi) Boxed (map (sigma $@) taus)
sigma $@ (TyApp phi tau1 tau2)
    = TyApp (sigma $@+ phi) (sigma $@ tau1) (sigma $@ tau2)
sigma $@ (TyForall NoPhi (Just varBinds) unknown tau1)
    = let sigma' = Subst { tySubst = foldr (\(UnkindedVar _ k) r -> k `Map.delete` r) (tySubst sigma) varBinds
                         , annSubst = Map.empty
                         }
       in TyForall NoPhi (Just varBinds) unknown (sigma' $@ tau1)
       
infixr 0 $@+

($@+) :: Subst -> Phi -> Phi
sigma $@+ (Phi (RefVar rv))
    = Phi (RefVar (Map.findWithDefault rv rv (annSubst sigma)))

       
-- * Apply substitution to an environment (or substitution)

infixr 0 $&&

($&&) :: Subst -> Env -> Env
theta $&& env = map (\(name, ty) -> (name, theta $@ ty)) env

-- * Apply substitution to a constraint set

infixr 0 $@@

($@@) :: Subst -> [Constr] -> [Constr]
theta $@@ cs = map (\((:=:!) _ s t) -> (theta $@ s) =: (theta $@ t)) cs

-- * Apply substitution to a refinement constraint set

infixr 0 $@^^^

($@^^^) :: Subst -> Refinement -> Refinement
theta $@^^^ (RefVar name) = RefVar (Map.findWithDefault name name (annSubst theta))
theta $@^^^ (RefList abs) = RefList (substAbsList (annSubst theta) abs)
theta $@^^^ x             = x

infixr 0 $@<

($@<) :: Subst -> [RefConstr] -> [RefConstr]
theta $@< rcs = map (\(s :<: t) -> (theta $@^^^ s) :<: (theta $@^^^ t)) rcs

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

-- * Free type variables in a type environment

ftvEnv :: Env -> Set (Name Phi)
ftvEnv gamma = foldr (\(_, tau) ns -> ftv tau `union` ns) empty gamma 

-- * Occurs check

occCheck :: Type Phi -> Type Phi -> Bool
occCheck (TyVar _ name) tau = not (name `member` ftv tau)

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
uses (Let _ (BDecls _ [PatBind _ (PVar _ name) _ (UnGuardedRhs _ e1) _]) e2)
    = name `delete` (uses e1 `union` uses e2)
uses (If _ g e1 e2)
    = uses g `union` uses e1 `union` uses e2
uses (Case _ e alts)
    = uses e `union` foldr (\(Alt _ _ (UnGuardedAlt _ e) _) r -> uses e `union` r) empty alts
uses (Paren _ e)
    = uses e
uses x
    = error ("uses: " ++ show x)

-- | Unification

-- TODO: factor out the recursion (scheme)
-- TODO: Switch occCheck and otherwise?

unify :: [Constr] -> Subst

unify []
    = Subst { tySubst  = Map.empty
            , annSubst = Map.empty }
unify (((:=:!) _ s t)       : c')
    | s == t       = unify c'
unify (((:=:!) _ s@(TyVar NoPhi x) t) : c')
    | occCheck s t = let u = Subst { tySubst  = Map.singleton x t
                                   , annSubst = Map.empty         }
                      in unify (u $@@ c') $. u
    | otherwise    = error "unify: occurs check"
unify (((:=:!) _ s t@(TyVar NoPhi x)) : c')
    | occCheck t s = let u = Subst { tySubst  = Map.singleton x s
                                   , annSubst = Map.empty         }
                      in unify (u $@@ c') $. u
    | otherwise    = error "unify: occurs check"
unify (((:=:!) _ s@(TyFun sr s1 s2) t@(TyFun tr t1 t2)) : c')
    = let u = uniphi sr tr
       in unify (u $@@ ((s1 =: t1) : (s2 =: t2) : c')) $. u
unify (((:=:!) _ s@(TyList sr s1) t@(TyList tr t1)) : c')
    = let u = uniphi sr tr
       in unify (u $@@ ((s1 =: t1) : c')) $. u
unify (((:=:!) _ s@(TyTuple sr Boxed ss) t@(TyTuple tr Boxed ts)) : c')
    | length ss == length ts
        = let u = uniphi sr tr
           in unify (u $@@ (zipWith (=:) ss ts ++ c')) $. u
    | otherwise    = error "unify: tuple arity mismatch"
unify (((:=:!) _ (TyCon (Phi (RefVar phi)) s) (TyCon (Phi (RefVar psi)) t)) : c')
    | s == t       = let u = Subst { tySubst  = Map.empty
                                   , annSubst = Map.singleton phi psi }
                      in unify (u $@@ c') $. u
    | otherwise    = error "unify: constructor clash"
unify (((:=:!) _ s@(TyApp NoPhi s1 s2) t@(TyApp NoPhi t1 t2)) : c')
    = unify ((s1 =: t1) : (s2 =: t2) : c')
unify x
    = error ("unify: fail (" ++ show x ++ ")")
    
-- * Unify annotation variables
uniphi :: Phi -> Phi -> Subst
uniphi (Phi (RefVar a)) (Phi (RefVar b))
    = Subst { tySubst  = Map.empty
            , annSubst = Map.singleton a b }
uniphi x y
    = error ("uniphi: " ++ show x ++ " | " ++ show y)

    
-- | Generalization & Instantiation

-- * Generalization (assumes tau is a type and not a type scheme)

gen :: Env -> Type Phi -> Type Phi

gen gamma tau
    = let alphas = ftv tau \\ ftvEnv gamma
       in TyForall NoPhi (Just (map (UnkindedVar NoPhi) (toList alphas))) Nothing tau

-- * Instantiation

inst :: Fresh -> Type Phi -> (Type Phi, [RefConstr])

inst fresh (TyForall (UC { uc = cs}) (Just varBinds) Nothing t)
    = let sigma = Map.fromList $ zipWith (\(UnkindedVar NoPhi name) f -> (name, f)) varBinds fresh
       in (sigma $@* t, (Subst {annSubst = sigma}) $@< cs)
inst fresh t
    = (t, []) --error "inst: not a type scheme"

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
