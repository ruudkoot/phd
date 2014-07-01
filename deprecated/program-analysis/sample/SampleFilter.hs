{-# LANGUAGE NoMonomorphismRestriction #-}

module Test where

-- | Neil Mitchell

-- * Risers
--{-
main = let risers = \x -> case x of 
                            [] -> []
                            (y:ys) -> case ys of
                                        [] -> (y : []) : []
                                        (z:zs) -> risers2 (risers3 z zs) (y <= z) y
           risers2 = \x -> \y -> \z -> if y then
                                        (z : snd x) : (fst x)
                                       else
                                        (z : []) : (snd x : fst x)
           risers3 = \x -> \y -> risers4 (risers (x : y))
           risers4 = \x -> case x of
                            (y:ys) -> (ys, y)
        in risers
---}

-- | Prelude

-- * Filter
{-

filter :: (a -> Bool) -> [a] -> [b]
filter _ []     = []
filter p (x:xs) | p x       = x : filter p xs
                | otherwise =     filter p xs

---}

{-
-- main :: (a -> Bool) -> [a] -> [a]
main = let filter = \p -> \ys -> case ys of
                                   [] -> []
                                   (x:xs) -> let g = p x
                                              in if g then x : filter p xs
                                                      else     filter p xs
       in filter (\x -> x) [True, False]
-}

{-
-- main :: (a -> Bool) -> [a] -> [a]
main = let filter = \p -> \ys -> case ys of
                                   [] -> []
                                   (x:xs) -> let g = p x
                                              in if g then x : filter p xs
                                                      else     filter p xs
       in filter
-}


{-
-- main :: (a -> Bool) -> [a] -> [a]
main = let filter = \p -> \ys -> case ys of
                                   [] -> []
                                   (x:xs) -> let g = p x
                                              in if g then x : xs
                                                      else     xs
       in filter
-}

{-
-- main :: (a -> Bool) -> [a] -> [a]
main = \p -> \ys -> case ys of
                        [] -> []
                        (x:xs) -> let g = p x
                                   in if g then x : xs
                                           else     xs
-}

{-
-- main :: (Integer -> Bool) -> [Integer] -> [Integer]
main = let filter = \p -> \ys -> case ys of
                                    [] -> []
                                    (x:xs) -> let g = p x
                                               in if g then x : [1,2,3]
                                                       else     [1,2,3]
        in filter
-}

{-
-- main :: (Integer -> Bool) -> [Integer] -> [Integer]
main = \p -> \ys -> case ys of
                        [] -> []
                        (x:xs) -> let g = p x
                                   in if g then x : [1,2,3]
                                           else     [1,2,3]
-}

-- * Map

{-
main = let map4 = \f -> \xss -> case xss of
                                 []     -> []
                                 (x:xs) -> f x : map4 f xs
        in map4 (\x -> [-3]) [1,2,3]
-}
{-
main = let map4 = \f -> \xss -> case xss of
                                 []     -> []
                                 (x:xs) -> f x : map4 f xs
        in map4
-}
{-
main = let map3 = \f -> \xss -> case xss of
                                 []     -> []
                                 (x:xs) -> f x : xs
        in map3
-}
{- (?33 ⊆ {[],_:?45}, {[]} ⊆ ?39) => ((?21@X -> [?15@X]@?39)@λ -> ([?21@X]@?33 -> [?15@X]@?39)@λ)@λ
main = let map2 = \f -> \xss -> case xss of
                                 []     -> []
                                 (x:xs) -> f x
        in map2 (\x -> [True]) [1,2,3]
-}
{- (?33 ⊆ {_:?45}) => ((?21@X -> ?78@X)@λ -> ([?21@X]@?33 -> ?78@X)@λ)@λ
main = let map1 = \f -> \xss -> case xss of
                                 (x:xs) -> f x
        in map1
-}

-- * Tail

{-
main = \b -> let tail = \xss -> case xss of
                                   (x:xs) -> xs
              in tail (if b then [] else [1,2,3])
-}
{-
main = let tail = \xss -> case xss of
                            (x:xs) -> xs
        in tail []
-}

{-
main = let tail = \xss -> case xss of
                            (x:xs) -> xs
        in tail [1,2,3]
-}


{- (?27 ⊆ {_:?39}) => ([?15@X]@?27 -> [?15@X]@?39)@λ
main = let tail = \xss -> case xss of
                            (x:xs) -> xs
        in tail
-}

-- * Head

{-
main = let head = \xss -> case xss of
                            (x:xs) -> x
        in head []
-}

{-
main = let head = \xss -> case xss of
                            (x:xs) -> x
        in head [1,2,3]
-}


{- (?27 ⊆ {_:?39}) => ([?15@X]@?27 -> ?15@X)@λ
main = let head = \xss -> case xss of
                            (x:xs) -> x
        in head
-}

-- | Higher-order function
-- main = \f -> \x -> let r = f x in r
-- main = \f -> \x -> let r = f True in r
-- main = \f -> let r = f True in r
-- main = \f -> \x -> f x
