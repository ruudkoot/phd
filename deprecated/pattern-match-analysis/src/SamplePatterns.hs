module Main where

data Either a b
    = Left a
    | Right b
    
data Pair a b
    = Pair { fst :: a, snd :: b }
    
-- | Multiple patterns

main = \x -> case x of
                Left [a]     -> 1
                Right (a, 4) -> 2
    
-- | Single patterns

-- * PIrrPat
{-
main = \x -> case x of
                ~(a:as) -> 1
-}
-- * PWildcard
{-
main = \x -> case x of
                _ -> 1
-}

-- * PAsPat
{-
main = \x -> case x of
                a@(Left b) -> a
-}

-- * PRec
{-
main = \x -> case x of
                Pair { fst = i, snd = b } -> 1
-}

-- * PList
{-
main = \x -> case x of
                [1,a] -> a
-}
{-
main = \x -> case x of
                [1] -> 2
-}
{-
main = \x -> case x of
                Left [a,b] -> a
-}
{-
main = \x -> case x of
                Left [a] -> a
-}

-- * PTuple
{-
main = \x -> case x of
                (a,b) -> (b,a)
-}

-- * PLit, PNeg
{-
main = \x -> case x of
                "a" -> "b"
-}
{-
main = \x -> case x of
                'a' -> 'b'
-}
{-
main = \x -> case x of
                -1 -> -2
-}
{-
main = \x -> case x of
                1 -> 2
-}

-- * PVar, PApp, PInfixApp
{-
main = \x -> case x of
                () -> ()
-}
{-
main = \x -> case x of
                (a:as) -> 1
-}
{-
main = \x -> case x of
                Left a -> a
-}
