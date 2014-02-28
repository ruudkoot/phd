theModule
  = let risers1
          = let r2
                  = \ d ->
                      case d of
                          e : es -> (es, e)
              in
              let r1
                    = \ a ->
                        \ b ->
                          \ c ->
                            if b then ((c : snd a) : fst a) else ((c : []) : (snd a : fst a))
                in
                let rx'ry
                      = let rx'ry_f
                              = \ rx'ry_x ->
                                  (\ u ->
                                     case u of
                                         [] -> []
                                         v : vs -> case vs of
                                                       [] -> ((v : []) : [])
                                                       w : ws -> r1 (snd (rx'ry_f ()) w ws) (v <= w)
                                                                   v,
                                   \ x -> \ y -> r2 (fst (rx'ry_f ()) (x : y)))
                          in rx'ry_f
                  in fst (rx'ry ())
      in
      let main
            = risers1 (1 : (3 : (5 : (8 : (5 : (3 : (6 : (3 : []))))))))
        in main

