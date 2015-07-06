module Main where

-- Types

type Idx = Int

data Name
    = Free  Idx
    | Bound Idx
    | Con   Idx
    deriving (Read, Show)

data Ty
    = Base Idx
    | Arr  Ty Ty
    deriving (Read, Show)

data Ty' 
    = Base' Idx
    | Arr'  [Ty'] Idx

data Tm
    = Var Name
    | Abs Ty Tm
    | App Tm Tm
    deriving (Read, Show)

data Nf'
    = Nf' [Ty'] Name [Nf']
    deriving (Read, Show)
    
heading :: Nf' -> Name
heading (Nf' _ x _) = x
    
rigid :: Nf' -> Bool
rigid (Nf' _ (Free  _) _) = False
rigid (Nf' _ (Bound _) _) = True
rigid (Nf' _ (Con   _) _) = True

-- Unification

type DisagreementSet  = [(Nf',Nf')]
type SubstitutionPair = (Idx, Tm)

data MatchingTree
    = S
    | F
    | Node DisagreementSet [(SubstitutionPair, MatchingTree)]
    
simpl :: DisagreementSet -> MatchingTree
simpl n = case mapM f n of
            Nothing -> F
            Just n' -> undefined
    where f (Nf' _ e

