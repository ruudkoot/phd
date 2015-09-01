module Constr where

-- FIXME: can be generalized from a set to a lattice solver (join/meet)
-- FIXME: a lot of variables are still called ref*

import qualified Data.Graph      as G
import qualified Data.Graph.Util as G
import qualified Data.Map        as M
import qualified Data.Map.Util   as M
import qualified Data.Set        as S
import qualified Data.Set.Util   as S

import Common

-- | Subset constraints

type Constr a = S.Set (Constr' a)

data Constr' a
    = Elem a :<: Elem a     -- FIXME: LHS a :<: Name?
    deriving (Eq, Ord, Show)
    
data Elem a  -- FIXME: needs a better name
    = Unif Name
    | Conc (S.Set a)        -- FIXME: needs a better name
    deriving (Eq, Ord, Show)
    
class (Ord a, Show a) => ConstrElem a where
    demote :: a -> Elem a
    injVar :: Name -> a
    prjVar :: a -> Name
    
injUnif :: ConstrElem a => Elem a -> Elem a       -- FIXME: call injVar directly?
injUnif (Unif u) = Conc (S.singleton (injVar u))

prjUnif :: ConstrElem a => a -> Elem a
prjUnif x = Unif (prjVar x)

-- | Simplification

-- * Decomposition into singleton (atomic?) constraints

decompose :: ConstrElem a => Constr a -> Constr a
decompose c
    = S.foldr (\c' r -> r `S.union` decompose' c') S.empty c

decompose' :: ConstrElem a => Constr' a -> Constr a
decompose' (Conc refs :<: b@(Unif _))
    = S.unionMap (\ref' -> S.singleton (Conc (S.singleton ref') :<: b)) refs
decompose' (Unif b1 :<: b2@(Unif _)) -- FIXME: we shouldn't (but do) generate these
    = S.singleton (Conc (S.singleton (injVar b1)) :<: b2)
   
-- * Remove reflexive constraints

removeReflexive :: ConstrElem a => Constr a -> Constr a
removeReflexive
    = S.foldr (\c'@(l :<: r) cr -> if l == injUnif r then cr else S.insert c' cr)
              S.empty

-- * Constract cyclic constraints (strongly connected components)

-- FIXME: extremely dubious code

type NameSubst = M.Map Name Name -- FIXME

contractCycles :: ConstrElem a => Constr a -> (Constr a, NameSubst)
contractCycles c
    = let sccs = G.stronglyConnCompR (toGraph c)
       in foldr pc (S.empty, M.empty) sccs

pc :: ConstrElem a =>
    G.SCC ((), a, [a]) -> (Constr a, NameSubst) -> (Constr a, NameSubst)
pc (G.AcyclicSCC ((), r, vs)) (cr, sr)
    = ( foldr (\v -> S.insert (Conc (S.singleton r) :<: prjUnif v)) cr vs
      , sr                                                                           )
pc (G.CyclicSCC scc@(((), r', _):scc')) (cr, sr)
    = ( foldr (\((), r, vs) cr' ->
            foldr (\v -> S.insert (Conc (S.singleton r) :<: prjUnif v)) cr' vs
        ) cr scc
      , foldr (\((), r'', _) sr' -> M.insert (prjVar r'') (prjVar r') sr') sr scc' )

-- | Constraint solving (assumes constraints have been decomposed and decycled!)
                   -- FIXME: solver should take care of prepocessing the constraint set

type Subst' a = M.Map Name (Elem a) -- FIXME: newtype; Set not Elem

solve :: ConstrElem a => Constr a -> Subst' a -> Subst' a
solve c subst0
    = let sccs = G.stronglyConnCompR (toGraph c)
       in foldr processComponent subst0 sccs

processComponent :: ConstrElem a => G.SCC ((), a, [a]) -> Subst' a -> Subst' a
processComponent (G.AcyclicSCC ((), ref, vs)) subst
    = case demote ref of
        Unif b -> let f x | v <- prjVar x = M.insertWith refJoin v (M.findWithDefault (Conc S.empty) b subst) --(subst M.!! b) --FIXME: why are we missing stuff???
                   in foldr f subst vs
        conc   -> let f x | v <- prjVar x = M.insertWith refJoin v conc
                   in foldr f subst vs
processComponent (G.CyclicSCC _) _
    = error "processComponent: did you forget to decompose the constraint set?"

-- FIXME: Use a representation more suited for the none R version and already apply prj
toGraph :: ConstrElem a => Constr a -> [((), a, [a])]
toGraph = map (\(k, v) -> ((), k, S.toList v)) . M.toList . toMap

toMap :: ConstrElem a => Constr a -> M.Map a (S.Set a)
toMap = S.foldr f M.empty
    where f (Conc ref1' :<: Unif ref2) | Just (ref1, _) <- S.minView ref1'
            = M.insertWith S.union ref1 (S.singleton (injVar ref2))

refJoin :: ConstrElem a => Elem a -> Elem a -> Elem a
refJoin (Conc refs1) (Conc refs2) = Conc (refs1 `S.union` refs2)
