module Refinement where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Language.Haskell.Exts.Annotated hiding (Cons)

import Abstract.Unit
import Abstract.Bool
import Abstract.Int
import Abstract.List

import Latex

-- | Annotations

data Phi
    = Phi { phi :: Refinement }
    | NoPhi
    | UC { uc :: [RefConstr] } -- unsolved constraints
    deriving (Eq, Ord)
    
instance Show Phi where
    show (Phi r) = show r
    show (NoPhi) = "X"

-- | Refinements

data Refinement
    = RefVar (Name Phi)
    | RefUnit AbsUnit
    | RefBool AbsBool
    | RefInt  AbsInt
    | RefList (AbsList (Name Phi))
    | RefLambda         -- perhaps just use top?
    | RefTop            -- for now: chars, tuples, lists, etc.
    deriving (Eq, Ord)

instance Show Refinement where
    show (RefVar    name   ) = prettyPrint name
    show (RefUnit   absunit) = show absunit
    show (RefBool   absbool) = show absbool
    show (RefInt    absint ) = show absint
    show (RefList   abslist) = show abslist
    show (RefLambda        ) = "λ"
    show (RefTop           ) = "T"

instance Latex Refinement where
    latex (RefVar    name  ) = prettyPrint name
    latex (RefInt    absint) = undefined -- latex absint
    latex (RefLambda       ) = "\\lambda"
    latex (RefTop          ) = "\\top"
    
-- | Constraints

data RefConstr
    = Refinement :<: Refinement
    deriving (Eq, Ord)

instance Show RefConstr where
    show (t1 :<: t2) = show t1 ++ " ⊆ " ++ show t2
    
-- | Substitutions (ONLY USED IN Main for sanity checking)

type RefSubst = Map (Name Phi) (Refinement, Refinement)

infixr 0 $@^!

($@^!) :: RefSubst -> Refinement -> Refinement
sigma $@^! ref@(RefVar name)
    = snd (Map.findWithDefault (undefined, ref) name sigma)
sigma $@^! ref@(RefList abslist)
    = RefList (instAbsList (putSquarePegInRoundHoleU sigma) topAbsList abslist)
sigma $@^! ref@_
    = ref
    
infixr 0 $@^?
    
($@^?) :: RefSubst -> Refinement -> Refinement
sigma $@^? ref@(RefVar name)
    = fst (Map.findWithDefault (ref, undefined) name sigma)
sigma $@^? ref@(RefList abslist)
    = RefList (instAbsList (putSquarePegInRoundHoleL sigma) botAbsList abslist)
sigma $@^? ref@_
    = ref
    
infixr 0 $@@^

($@@^) :: RefSubst -> [RefConstr] -> [RefConstr]
theta $@@^ cs = map (\(s :<: t) -> (theta $@^! s) :<: (theta $@^? t)) cs

infixr 0 $@@^!

($@@^!) :: RefSubst -> [RefConstr] -> [RefConstr]
theta $@@^! cs = map (\(s :<: t) -> (theta $@^! s) :<: (theta $@^! t)) cs

infixr 0 $@@^?

($@@^?) :: RefSubst -> [RefConstr] -> [RefConstr]
theta $@@^? cs = map (\(s :<: t) -> (theta $@^? s) :<: (theta $@^? t)) cs

-- * List

putSquarePegInRoundHoleL :: RefSubst -> Map (Name Phi) (AbsList (Name Phi))
putSquarePegInRoundHoleL subst = fmap (\(RefList a, _) -> a) subst

putSquarePegInRoundHoleU :: RefSubst -> Map (Name Phi) (AbsList (Name Phi))
putSquarePegInRoundHoleU subst = fmap (\(_, RefList a) -> a) subst

consRefVar :: Refinement -> AbsList (Name Phi)
consRefVar (RefVar name) = AbsList (Set.singleton (Cons (ListVar name)))

-- * Unification variable renaming for instantiation

infixr 0 $@*^

($@*^) :: Map (Name Phi) (Name Phi) -> Refinement -> Refinement
sigma $@*^ (RefVar name)
    = RefVar (Map.findWithDefault name name sigma)
sigma $@*^ x
    = x

-- | Satifiability check

refSat :: Refinement -> Refinement -> Bool
refSat (RefTop   ) (RefTop   ) = True
refSat (RefLambda) (RefLambda) = True
refSat (RefUnit a) (RefUnit b) = a `subsetAbsUnit` b
refSat (RefBool a) (RefBool b) = a `subsetAbsBool` b
refSat (RefInt  a) (RefInt  b) = a `subsetAbsInt`  b
refSat (RefList a) (RefList b) = a `subsetAbsList` b
    
-- | Sanity check

sanityCheck :: [RefConstr] -> Bool
sanityCheck = and . map check
    where check :: RefConstr -> Bool
          check (RefLambda :<: RefLambda) = True
          check (RefTop    :<: RefTop   ) = True
          check (RefUnit a :<: RefUnit b) = a `subsetAbsUnit` b
          check (RefBool a :<: RefBool b) = a `subsetAbsBool` b
          check (RefInt  a :<: RefInt  b) = a `subsetAbsInt`  b
          check (RefList a :<: RefList b) = a `subsetAbsList` b
          check _                         = False
          
-- | Evil hackish stuff

promoteVar :: Refinement -> Refinement
promoteVar (RefList l) | Just name <- isVarAbsList l = RefVar name
promoteVar x = x
