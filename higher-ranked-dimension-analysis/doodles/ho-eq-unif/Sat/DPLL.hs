{-# LANGUAGE ViewPatterns #-}

module Sat.DPLL (
) where

import Data.Maybe
    ( mapMaybe )
import Data.Set
    ( Set, (\\), empty, insert, intersection, singleton, size, toList, union )

-- | Data.Set | ----------------------------------------------------------------

overlaps :: Ord atom => Set atom -> Set atom -> Bool
overlaps p q = size (p `intersection` q) > 0

-- | Boolean expressions | -----------------------------------------------------

data Exp atom
    = Atom atom
    | Val Bool
    | Not (Exp atom)
    | And (Exp atom) (Exp atom)
    | Or  (Exp atom) (Exp atom)
  deriving Show

-- | Conjunctive normal form | -------------------------------------------------

type Clause atom = (Set atom, Set atom)
type CNF    atom = [Clause atom]

unionClause :: Ord atom => Clause atom -> Clause atom -> Clause atom
unionClause (pos1, neg1) (pos2, neg2) = (pos1 `union` pos2, neg1 `union` neg2)

toCNF :: Ord atom => Exp atom -> CNF atom
toCNF (Atom a    ) = [(singleton a, empty)]
toCNF (Val  True ) = []
toCNF (Val  False) = [(empty, empty)]
toCNF (Not  t    ) = negCNF (toCNF t)
toCNF (And  t1 t2) = toCNF t1 ++ toCNF t2
toCNF (Or   t1 t2) = [ t1' `unionClause` t2' | t1' <- toCNF t1, t2' <- toCNF t2 ]

negCNF :: Ord atom => CNF atom -> CNF atom
negCNF []        = [(empty, empty)]
negCNF (t1 : ts) =
    let ts' = negCNF ts
     in [ (pos, t1' `insert` neg) | t1' <- toList (fst t1), (pos, neg) <- ts' ]
            ++
        [ (t1' `insert` pos, neg) | t1' <- toList (snd t1), (pos, neg) <- ts' ]

-- | David-Putney-Logemann-Loveland | ------------------------------------------

allLiterals :: Ord atom => CNF atom -> (Set atom, Set atom)
allLiterals = foldr unionClause (empty, empty)

singlePolarityLiterals :: Ord atom => CNF atom -> (Set atom, Set atom)
singlePolarityLiterals cnf =
    let (pos, neg) = allLiterals cnf in (pos \\ neg, neg \\ pos)

oneLiteralClauses :: Ord atom => CNF atom -> (Set atom, Set atom)
oneLiteralClauses = foldr op (empty, empty)
  where
    op (x@(size -> 1),   size -> 0 ) (pos, neg) = (x `union` pos, neg)
    op (   size -> 0, x@(size -> 1)) (pos, neg) = (pos, x `union` neg)
    op _                             (pos, neg) = (pos, neg)

eliminateOneLiteralClauses :: Ord atom => CNF atom -> CNF atom
eliminateOneLiteralClauses cnf =
    let (posOLC, negOLC) = oneLiteralClauses cnf

        eliminate (pos, neg)
            | pos `overlaps` posOLC || neg `overlaps` negOLC
                = Nothing
            | otherwise
                = Just (pos \\ negOLC, neg \\ posOLC)

     in if posOLC `overlaps` negOLC then
            [(empty, empty)]
        else
            mapMaybe eliminate cnf

positiveNegativeRule :: Ord atom => CNF atom -> CNF atom
positiveNegativeRule cnf =
    let (posOnly, negOnly) = singlePolarityLiterals cnf

        eliminate (pos, neg) = pos `overlaps` posOnly || neg `overlaps` negOnly

     in filter eliminate cnf

eliminateAtom :: Ord atom => atom -> CNF atom -> CNF atom
