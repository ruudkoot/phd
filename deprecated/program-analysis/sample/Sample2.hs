module Main where

-- | Case

main = \xs -> case xs of
                []     -> 666
                (y:ys) -> y

-- | If-then-else + Lambda

-- main = \a -> \b -> if a then b else a
-- main = \b -> if b then b else b
-- main = \b -> if b then 42 else 666

-- * Nested

-- main = if False then (if True then 42 else 24) else 666
-- main = if True then (if True then 42 else 24) else 666

-- * Simple

-- main = if False then 42 else 666
-- main = if True then 42 else 666

-- | Constants

-- main = 42
