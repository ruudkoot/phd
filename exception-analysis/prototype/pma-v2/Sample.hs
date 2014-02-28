module Sample where
{-
-- Prelude functions
length []     = 0
length (b:bs) = 1 + length bs

map f []     = []
map f (y:ys) = f y : map f ys
            
filter p xs = case xs of
                [] -> []
                (y:ys) -> if p y then y : filter p ys else filter p ys
                

main = let l = [1,3,5] in filter (\z -> z <= length l) l
-}
-- Risers

risers1 =
  let r1 a b c = if b then (c : snd a) : (fst a) else [c] : (snd a : fst a)

      r2 d = case d of
               (e:es) -> (es, e)

      rx = \u -> case u of
                     []     -> []
                     (v:vs) -> case vs of
                                 []     -> (v : []) : []
                                 (w:ws) -> r1 (ry w ws) (v <= w) v
      ry = \x y -> r2 (rx (x : y))

  in rx
  
main = risers1 [1,3,5,8,5,3,6,3]
