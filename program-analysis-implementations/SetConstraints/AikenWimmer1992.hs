module AikenWimmers1992 where

import qualified Data.Set as S

-- | Syntax

type Name = String

data SetExpr
    = O
    | I
    | Var Name
    | Not SetExpr
    | SetExpr :|: SetExpr
    | SetExpr :&: SetExpr
    | Con Con [SetExpr]
    deriving (Eq, Ord, Show)

data SetConstr
    = SetExpr :<: SetExpr
    deriving (Eq, Ord, Show)
    
data SetEquality
    = SetExpr :=: SetExpr
    deriving (Eq, Ord, Show)

type System           = S.Set SetConstr
type SolvedFormSystem = S.Set SetEquality

-- | Algorithms

oneLevelSystem :: System -> FreshM System
oneLevelSystem = S.mapM (\(a :<: b) -> oneLevel (a :&: Not b) :<: O)

oneLevel :: SetExpr -> FreshM SetExpr
oneLevel = undefined

-- | Freshness Monad

type FreshM r = State [Name] r

class Fresh t where
    fresh :: InferM t

instance Fresh Name where
    fresh = do (x:xs) <- get
               put xs
               return x

-- | Examples

-- * Constructors (should be a parameter)

data Con = A | B | C deriving (Eq, Ord, Show)
    
a :: Con -> Int
a A = 0
a B = 1
a C = 2



