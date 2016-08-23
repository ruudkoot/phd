{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns  #-}

module Sat.DPLL (
    Exp(..),
    toCNF,
    dp,
    dpll
) where

import Data.Function
    ( on )
import Data.List
    ( minimumBy )
import Data.Map
    ( Map )
import Data.Maybe
    ( mapMaybe )
import Data.Set
    ( Set, (\\), delete, empty, findMin, insert, intersection, member, singleton
    , size, toList, union
    )
import qualified Data.Set as Set

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

type Clause    atom = (Set atom, Set atom)
type CNF       atom = [Clause atom]
type Valuation atom = [(atom, Bool)]

posLit :: atom -> Clause atom
posLit a = (singleton a, empty)

negLit :: atom -> Clause atom
negLit a = (empty, singleton a)

isConsistent :: CNF atom -> Bool
isConsistent = null

isInconsistent :: CNF atom -> Bool
isInconsistent = any (\(pos,neg) -> Set.null pos && Set.null neg)

clauseSize :: Clause atom -> Int
clauseSize (pos, neg) = size pos + size neg

unionClause :: Ord atom => Clause atom -> Clause atom -> Clause atom
unionClause (pos1, neg1) (pos2, neg2) = (pos1 `union` pos2, neg1 `union` neg2)

toCNF :: Ord atom => Exp atom -> CNF atom
toCNF (Atom a    ) = [(singleton a, empty)]
toCNF (Val  True ) = []
toCNF (Val  False) = [(empty, empty)]
toCNF (Not  t    ) = negCNF (toCNF t)
toCNF (And  t1 t2) = toCNF t1 ++ toCNF t2
toCNF (Or   t1 t2) = [ unionClause t1' t2' | t1' <- toCNF t1, t2' <- toCNF t2 ]

negCNF :: Ord atom => CNF atom -> CNF atom
negCNF []        = [(empty, empty)]
negCNF (t1 : ts) =
    let ts' = negCNF ts
     in [ (pos, t1' `insert` neg) | t1' <- toList (fst t1), (pos, neg) <- ts' ]
            ++
        [ (t1' `insert` pos, neg) | t1' <- toList (snd t1), (pos, neg) <- ts' ]

-- | Davis-Putney-Logemann-Loveland | ------------------------------------------

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
    
partitionClauses
    :: Ord atom
    => atom
    -> CNF atom
    -> (CNF atom, CNF atom, CNF atom)
partitionClauses a []
    = ([], [], [])
partitionClauses a (c@(pos, neg) : cnf@(partitionClauses a -> (as, bs, rs)))
    | a `member` pos = ((delete a pos, neg) : as, bs, rs)
    | a `member` neg = (as, (pos, delete a neg) : bs, rs)
    | otherwise      = (as, bs, c : rs)
    
toValuation :: Ord atom => Set atom -> Set atom -> Valuation atom
toValuation pos neg = map (, True) (toList pos) ++ map (, False) (toList neg)

eliminateOneLiteralClauses :: Ord atom => CNF atom -> (CNF atom, Valuation atom)
eliminateOneLiteralClauses cnf =
    let (posOLC, negOLC) = oneLiteralClauses cnf

        eliminate (pos, neg)
            | pos `overlaps` posOLC || neg `overlaps` negOLC
                = Nothing
            | otherwise
                = Just (pos \\ negOLC, neg \\ posOLC)

     in if posOLC `overlaps` negOLC then
            ([(empty, empty)], [])
        else
            (mapMaybe eliminate cnf, toValuation posOLC negOLC)

positiveNegativeRule :: Ord atom => CNF atom -> (CNF atom, Valuation atom)
positiveNegativeRule cnf =
    let (posOnly, negOnly) = singlePolarityLiterals cnf

        eliminate (pos, neg) = pos `overlaps` posOnly || neg `overlaps` negOnly

     in (filter (not . eliminate) cnf, toValuation posOnly negOnly)

eliminateAtom :: Ord atom => atom -> CNF atom -> CNF atom
eliminateAtom a cnf =
    let (as, bs, rs) = partitionClauses a cnf
     in [ unionClause a b | a <- as, b <- bs ] ++ rs

selectAtomToEliminate :: Ord atom => CNF atom -> atom
selectAtomToEliminate cnf =
    let (pos, neg) = minimumBy (compare `on` clauseSize) cnf
     in findMin (pos `union` neg)

dp :: Ord atom => CNF atom -> Bool
dp cnf1 =
    let (cnf2, _) = eliminateOneLiteralClauses cnf1
     in if isInconsistent cnf2 then
            False
        else
            let (cnf3, _) = positiveNegativeRule cnf2
             in if isConsistent cnf3 then
                    True
                else
                    dp (eliminateAtom (selectAtomToEliminate cnf3) cnf3)

dpll :: Ord atom => CNF atom -> [Valuation atom]
dpll cnf1 =
    let (cnf2, olc) = eliminateOneLiteralClauses cnf1
     in if isInconsistent cnf2 then
            []
        else
            let (cnf3, pnr) = positiveNegativeRule cnf2
             in if isConsistent cnf3 then
                    [pnr ++ olc]
                else
                    let p = selectAtomToEliminate cnf3
                     in map ((pnr ++ olc) ++) (dpll (posLit p : cnf3))
                            ++
                        map ((pnr ++ olc) ++) (dpll (negLit p : cnf3))
