{-
main = \b -> \phi -> if b
                     then if phi 42 then 100 else 200
                     else if phi 43 then 300 else 400
-}

--{-
main = let f = \b -> \phi -> if b
                             then if phi [42] then 100 else 200
                             else if phi [43] then 300 else 400
           g = \x -> case x of
                        []     -> True
           h = \x -> case x of
                        (a:as) -> True
        in f True g
---}

{-
main = let pm = \a -> case a of
                         -- []      -> [0]
                         (a:as)  -> case as of
                                      []      -> [0,1]
                                      (b:bs)  -> [1,2,3]
        in pm
-}

{-
main = let head = \xss -> case xss of
                            (x:xs) -> x
        in head
-}

{-
main = let tail = \xss -> case xss of
                            (x:xs) -> xs
        in tail
-}

{- (not precise enough)
main = let f = \b -> let tail = \xss -> case xss of
                                           (x:xs) -> xs
                      in tail (if b then [] else [1,2,3])
        in f False
-}

{-
main = let map4 = \f -> \xss -> case xss of
                                 []     -> []
                                 (x:xs) -> f x : map4 f xs
        in map4 (\x -> x) [1,2,3]
-}

{-
main = let filter = \p -> \ys -> case ys of
                                   [] -> []
                                   (x:xs) -> let g = p x
                                              in if g then x : filter p xs
                                                      else     filter p xs
       in filter (\x -> x) [True, False]
-}

{-
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
-}
