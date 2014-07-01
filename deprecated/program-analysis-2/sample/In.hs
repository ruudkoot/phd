-- {-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Test where
{-
data Bool
    = True
    | False
-}
{-
data Either a b
    = Left a
    | Right b
-}
{-
data Pair a b
    = Pair { fst :: a, snd :: b }
-}

-- | Patterns

-- * Real
{- head
main = \x -> case x of
                (a:as) -> as
-}

-- * Complex
{-
main = \x -> case x of
                Left [a]     -> [a,True]
                Right (a, 4) -> [a,a]
-}
{-
main = \x -> case x of
                Left [a]     -> 1
                Right (a, 4) -> 2
-}

-- | Either

-- * Case-statement

{-
main = \x -> case x of
                Left  a -> Right a
                Right b -> Left  b
-}
{-
main = \x -> case x of
                Left  a -> a
                Right b -> b
-}
{-
main = \x -> case x of
                Left  a -> 10
                Right b -> 20
-}      
{-
main = case Left True of
        Left  a -> 10
        Right b -> 20
-}

-- * App

-- main = \x -> Left x

-- * Type error

-- main = \x -> if x then Left True else Left 42

-- * Non-app

-- main = \x -> if x then Left True else Left False
-- main = \x -> if x then Left True else Right 42
-- main = \x -> if x then Left True else Right False
-- main = Left True

-- | Undefined

-- main = \x -> error x
-- main = error
-- main = undefined

-- | Let-bindings

-- * Mutually recursive
{-
main = let f = g
           g = h
           h = f
        in h
-}
{-
main = let f = g
           g = f
        in f
-}

-- * Simultaneous
{-
main = let a = b
           b = 42
        in b
-}
{-
main = let a = b
           b = 42
        in a
-}
{-
main = let a = 0
           b = 1
        in b
-}
{-
main = let a = 0
           b = 1
        in a
--}
-- * Recursion & Generalization
{-
main = let di = \a -> let b = di a in a
        in (di True, di 4, di)
-}
{-
main = let di = \a -> di a
        in (di True, di 4, di)
-}

-- * Recursive

{- [Int] -> Int
main = let mul = (\a -> (\b -> mul b a))
        in let factorialish = (\n -> case n of
                                        []     -> 1
                                        (x:xs) -> mul x (factorialish xs))
            in factorialish
-}
{-
main = let mul = (\a -> (\b -> mul b a))
        in let factorialish = (\n -> case n of
                                        []     -> 1
                                        (x:xs) -> mul x x{-(factorialish xs)-})
            in factorialish
-}
{-
main = let mul = (\a -> (\b -> mul b a))
        in let factorialish = (\n -> case n of
                                        []     -> 1
                                        (x:xs) -> mul x (factorialish xs))
            in mul
-}
{-
main = let mul = (\a -> (\b -> mul b a))
        in let b = 4
            in mul
-}

-- main = let mul = (\a -> (\b -> mul b a)) in let factorialish = (\n -> if False then 1 else mul n (factorialish n)) in factorialish
-- main = let f = f in f
-- main = let f = f in 42

-- * Generalization
{-
main = let id = \a -> a
        in (id True, id 4, id)
-}

-- * Fixing the type of an environment variable in a let-binding
{-
main = \a -> let f = case a of
                        []     -> 1
                        (x:xs) -> f
              in a
-}
{-
main = \a -> let f = case a of
                        []     -> 1
                        (x:xs) -> 2
              in a
-}

-- * Miscellaneous

{-
main = \bs -> let f = \as -> case as of
                              []     -> 1
                              (x:xs) -> 2
               in f bs
-}
{-
main = let f = \as -> case as of
                        []     -> 1
                        (x:xs) -> 2
        in f
-}
{-
main = \as -> case as of
                []     -> 1
                (x:xs) -> 2
-}
{- -- <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
main = let pm = \a -> case a of
                         -- []      -> [0]
                         (a:as)  -> case as of
                                      []      -> [0,1]
                                      (b:bs)  -> [1,2,3]
        in pm
-} -- <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
{-
main = \a -> case a of
                []     -> True
                (b:bs) -> False
-}

-- * Simultaneous let-bindings
{-
main = let a = 0
           b = 2
        in a
-}
{-
main = let a = 1
        in let b = 2
            in a
-}
{-
main = let a = 1
           b = 2
        in b
-}
{-
main = let a = 1
           b = 2
        in 42
-}

-- * Constructor clashes

-- main = (\x -> if x then (\y -> x) else (\z -> 42))
-- main = (\x -> if x then (\y -> True) else (\z -> 42))

-- * Correct

-- main = (\x -> let f = (\y -> y) in if x then (\y -> y) else (\z -> 42))
-- main = (\x -> if x then (\y -> y) else (\z -> 42))
-- main = let f = (\x -> x) in if True then f else f

-- main = let f = (\x -> x) in f (f True)
-- main = let f = (\x -> x) in f True
-- main = let f = (\x -> x) in f

-- * Variable lookup

-- main = let x = 42 in x

-- | Abstraction and application

-- * My example

{- -- <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
main = \b -> \phi -> if b
                     then if phi 42 then 100 else 200
                     else if phi 43 then 300 else 400
-} -- <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<

-- * Monomorphic

{-
main = if True
       then (\x -> let fix2int = if True then 666 else x in x)
       else (\y -> let fix2int = if True then 123 else y in y)
-}
-- main = (\f -> let fix2int = if True then 666 else f in if True then 42 else f)
-- main = (\f -> let fix2int = if True then 42 else f in if True then 42 else 13)

-- main = (\f -> let fix2int = if True then 42 else f in f)
-- main = (\f -> let fix2int = if True then 42 else f in 42)

-- * Polymorphic

-- main = \f -> [f 0, f (-1)]
-- main = \f -> [f True, f False]
-- main = \f -> f True

-- main = (\f -> False) True
-- main = (\f -> f) True

-- main = \z -> if True then \x -> z else \y -> z
-- main = \z -> if True then \x -> x else \y -> y
-- main = if True then (\x -> x) else (\y -> y)

-- main = (\x -> x)
-- main = (\x -> True)

-- | If-then-else

-- main = if True then 42 else -13
-- main = if True then 42 else 666

-- | Lists

-- * (:)

-- main = True : [1]
-- main = (-1) : [2]
-- main = 1 : [-2]
-- main = 1 : [2]
-- main = 1 : []

-- * List of functions

-- main = [\x -> 7, \x -> -13]
-- main = [\x -> 7, \x -> 13]
-- main = [\x -> x, \y -> y]

-- * List

-- main = [True,1]
-- main = [1,2,3,4,5,6,7,8,9]
-- main = [True, False]
-- main = []

-- | Tuples

-- * Tuple operations

-- main = [__prj_1_2,__prj_2_3]
-- main = [__prj_1_3,__prj_2_3,__prj_3_3]
-- main = (__prj_1_2,__prj_2_3)
-- main = (snd (fst,snd)) (snd,fst) -- ! answer okay, but sanity check fails here...
-- main = snd (fst, fst) -- ! answer okay, but sanity check fails here...
-- main = snd (\x -> x, \y -> y)
-- main = snd ((1,2,3),(4,5,6,7))
-- main = snd ([1], [2,3])
-- main = (fst,snd)
-- main = [fst,snd]
-- main = [fst]
-- main = snd (1,True)
-- main = fst (1,True)
-- main = fst  -- constraint in quantifier or annotation?

-- * Tuples

-- main = \x -> (\y -> y, \z -> x)
-- main = (1, -2)

-- | Basic constructors

-- * Integers

-- main = -7
-- main = 0
-- main = 42

-- * Booleans

-- main = True
-- main = False

-- * Unit

-- main = ()

-- | Risers

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

-- | Mutual recursion and generalization
{-
main = \f -> \a -> f (f a)

-}
{-
main = \f -> \x -> let g = f in q
---}
{-
main = let f = \x -> let g = \y -> x y
                      in let h = g
                         in q
        in f
-}
{- [LetRec] OK
main = let f = \a -> let r = (\b -> \q -> snd r b a,  \c -> \w -> fst r a c)
                      in (fst r, snd r)
        in f
-}
{- [LetMutRec] OK
main = let f = \a -> let g = \b -> \q -> h b a
                         h = \c -> \w -> g a c
                      in (g, h)
        in f
-}
{- OK
main = let f = \a -> let g = \b -> \q -> g b a
                         h = \c -> \w -> h a c
                      in (g, h)
        in f
-}
{- OK
main = let id = \x -> x
        in (id True, id 5, id id, id id)
-}
{- OK
main = let id = \x -> x
        in dq
-}
{- OK
main = let id = \x -> x
           const = \k -> \x -> k
           v = const
           w = const 5
           p = (id, id, const, const 5, const True, id True, id 5)
        in (id, const, v, w, p)
-}
