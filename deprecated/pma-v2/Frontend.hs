module Frontend where

import qualified Data.Map      as M
import qualified Data.Map.Util as M
import qualified Data.Set      as S
import qualified Data.Set.Util as S
import qualified Data.Graph    as G

import System.Environment

import Language.Haskell.Exts
import qualified Common as PMA

main = do
    args <- getArgs
    let fileName = if null args then "Sample.hs" else head args
    main' fileName

main' fileName = do
    contents <- readFile fileName
    let parseResult = parseModuleWithMode defaultParseMode contents
    case parseResult of
        ParseOk hModule            
            -> do putStrLn $ header "Source"
                  putStrLn $ prettyPrint hModule
                  putStrLn $ header "AST (haskell-src-exts)"
                  putStrLn $ show hModule
                  putStrLn $ header "Pre-Processing"
                  let ppr = preProcess hModule
                  putStrLn $ prettyPrint ppr
                  putStrLn $ header "AST (PMA)"
                  let ast = convert ppr
                  putStrLn $ show ast
                  putStrLn $ header "Reverted AST"
                  putStrLn $ prettyPrint (revert' ast)
        ParseFailed srcLoc message
            -> do print srcLoc
                  print message

-- | Conversion

convert :: Exp -> PMA.Expr
convert (Var (UnQual (Ident name)))
    = PMA.Var (PMA.name name )
convert (Con (UnQual (Ident "True")))
    = PMA.Con (PMA.Bool True )
convert (Con (UnQual (Ident "False")))
    = PMA.Con (PMA.Bool False)
convert (Con (Special UnitCon))
    = PMA.Con PMA.Unit
convert (Lit (Int n))
    = PMA.Con (PMA.Int (fromInteger n))
convert (InfixApp e1 (QConOp (Special Cons)) e2)
    = PMA.Cons (convert e1) (convert e2)
convert (InfixApp e1 (QVarOp (UnQual (Symbol "<="))) e2)
    = PMA.Op PMA.LEQ (convert e1) (convert e2)
convert (InfixApp e1 (QVarOp (UnQual (Symbol "+"))) e2)
    = PMA.Op PMA.ADD (convert e1) (convert e2)
convert (App e1 e2)
    = PMA.App (convert e1) (convert e2)
convert (Lambda _ pats e)
    = foldr (\(PVar (Ident x)) -> PMA.Abs (PMA.name x)) (convert e) pats
convert (Let (BDecls decls) e)
    = let decls' = map desugarFunBind decls
          defUse = map defUseDecl decls'
          graph = defUseGraph defUse
          sccs = G.stronglyConnComp graph
       in foldr f (convert e) sccs
            where f (G.AcyclicSCC
                       (PatBind _ (PVar (Ident x)) Nothing (UnGuardedRhs e1) (BDecls []))
                    ) r
                        = PMA.Let (PMA.name x) (convert e1) r
                  f (G.CyclicSCC
                      [PatBind _ (PVar (Ident f)) Nothing (UnGuardedRhs e1) (BDecls [])]
                    ) r
                        = let intSubst = M.fromList
                                            [ ( PMA.name f
                                              , PMA.Var (PMA.name (f ++ "_f")) ) ]
                           in PMA.Let (PMA.name f)
                                      (PMA.Fix
                                         (PMA.name $ f ++ "_f")
                                         (intSubst `applySubst` (convert e1))
                                      )
                                      r    
                  f (G.CyclicSCC
                      [ PatBind _ (PVar (Ident x1)) Nothing (UnGuardedRhs e1) (BDecls [])
                      , PatBind _ (PVar (Ident x2)) Nothing (UnGuardedRhs e2) (BDecls [])
                      ]
                    ) r
                        = let newName  = x1 ++ "'" ++ x2 {- FIXME: unsafe -}
                              extSubst = M.fromList
                                            [ ( PMA.name x1
                                              , PMA.Fst (PMA.Var $ PMA.name newName) )
                                            , ( PMA.name x2
                                              , PMA.Snd (PMA.Var $ PMA.name newName) )
                                            ]
                              intSubst = M.fromList
                                            [ ( PMA.name x1
                                              , PMA.Fst (PMA.Var $ PMA.name (newName ++ "_f")) )
                                            , ( PMA.name x2
                                              , PMA.Snd (PMA.Var $ PMA.name (newName ++ "_f")) )
                                            ]
                           in PMA.Let (PMA.name newName) 
                                      (PMA.Fix
                                           (PMA.name $ newName ++ "_f")
                                           (PMA.Pair (intSubst `applySubst` (convert e1))
                                                     (intSubst `applySubst` (convert e2))
                                           )
                                      )
                                      (extSubst `applySubst` r)
                  f (G.CyclicSCC decls) r
                        = error "mutual recursion involving more than two declarations"
convert (If e0 e1 e2)
    = PMA.If (toLbl e0) (convert e0) (convert e1) (convert e2)
convert (Case e0 [ Alt _ p1 (UnGuardedAlt e1) (BDecls []) ])
    | PList [] <- desugarPat p1
        = PMA.Case (toLbl e0)
                   (convert e0)
                   (Just (convert e1))
                   Nothing
convert (Case e0 [ Alt _ p2 (UnGuardedAlt e2) (BDecls []) ])
    | PApp (Special Cons) [PVar (Ident a), PVar (Ident as)] <- desugarPat p2
        = PMA.Case (toLbl e0)
                   (convert e0)
                   Nothing
                   (Just (PMA.name a, PMA.name as, convert e2))
convert (Case e0 [ Alt _ p1 (UnGuardedAlt e1) (BDecls [])
                 , Alt _ p2 (UnGuardedAlt e2) (BDecls []) ])
    | PList []                                              <- desugarPat p1
    , PApp (Special Cons) [PVar (Ident a), PVar (Ident as)] <- desugarPat p2
        = PMA.Case (toLbl e0)
                   (convert e0)
                   (Just (convert e1))
                   (Just (PMA.name a, PMA.name as, convert e2))
convert (Tuple [e1, e2])
    = PMA.Pair (convert e1) (convert e2)
convert (List es)
    = foldr (\e r -> PMA.Cons (convert e) r) PMA.Nil es
convert (Paren e)
    = convert e
convert x = error $ "convert : " ++ show x

applySubst :: M.Map PMA.Name PMA.Expr -> PMA.Expr -> PMA.Expr -- FIXME: move to Common
applySubst subst e@(PMA.Var name)
    = M.findWithDefault e name subst
applySubst subst e@(PMA.Con _)
    = e
applySubst subst (PMA.Abs x e)
    = PMA.Abs x ((subst `M.restrict` [x]) `applySubst` e)
applySubst subst (PMA.Fix f e)
    = PMA.Fix f ((subst `M.restrict` [f]) `applySubst` e)
applySubst subst (PMA.App e1 e2)
    = PMA.App (subst `applySubst` e1) (subst `applySubst` e2)
applySubst subst (PMA.Let x e1 e2)
    = PMA.Let x ((subst `M.restrict` [x]) `applySubst` e1) (subst `applySubst` e2)
applySubst subst (PMA.If lbl e0 e1 e2)
    = PMA.If lbl (subst `applySubst` e0) (subst `applySubst` e1) (subst `applySubst` e2)
-- Operators
applySubst subst (PMA.Op op e1 e2)
    = PMA.Op op (subst `applySubst` e1) (subst `applySubst` e2)
-- Pairs
applySubst subst (PMA.Pair e1 e2)
    = PMA.Pair (subst `applySubst` e1) (subst `applySubst` e2)
applySubst subst (PMA.Fst e)
    = PMA.Fst (subst `applySubst` e)
applySubst subst (PMA.Snd e)
    = PMA.Snd (subst `applySubst` e)
-- Lists
applySubst subst PMA.Nil
    = PMA.Nil
applySubst subst (PMA.Cons e1 e2)
    = PMA.Cons (subst `applySubst` e1) (subst `applySubst` e2)
applySubst subst (PMA.Case lbl e0 arm1 arm2)
    = PMA.Case lbl
               (subst `applySubst` e0)
               (fmap (applySubst subst) arm1)
               (fmap (\(x, xs, e2) ->
                        (x, xs, (subst `M.restrict` [x, xs]) `applySubst` e2)
                     )
                     arm2
               )
               
toLbl :: Exp -> String
toLbl (Var (UnQual (Ident x))) = x
toLbl _                        = "!"

desugarPat :: Pat -> Pat
desugarPat p@(PVar _)
    = p
desugarPat (PInfixApp p1 qname p2)
    = PApp qname [desugarPat p1, desugarPat p2]
desugarPat (PApp qname pats)
    = PApp qname (map desugarPat pats)
desugarPat (PTuple pats)
    = PTuple (map desugarPat pats)
desugarPat (PList pats)
    = PList (map desugarPat pats)
desugarPat (PParen pat)
    = desugarPat pat

revert' :: PMA.Expr -> Decl
revert' e = PatBind noSrcLoc (PVar (Ident "theModule")) Nothing (UnGuardedRhs (revert e)) (BDecls [])

revert :: PMA.Expr -> Exp
revert (PMA.Var name)
    = Var (UnQual (Ident (PMA.fromName name)))
revert (PMA.Con PMA.Unit)
    = Con (Special UnitCon)
revert (PMA.Con (PMA.Bool b))
    = Con (UnQual (Ident (show b)))
revert (PMA.Con (PMA.Int n))
    = Lit (Int $ toInteger n)
revert (PMA.Abs x e)
    = Lambda noSrcLoc [PVar (Ident (PMA.fromName x))] (revert e)
revert (PMA.Fix f e)
    = Let (BDecls [PatBind noSrcLoc
                           (PVar (Ident (PMA.fromName f)))
                           Nothing
                           (UnGuardedRhs (revert e))
                           (BDecls [])
                  ]
          )
          (Var (UnQual (Ident (PMA.fromName f))))
revert (PMA.App e1 e2)
    = App (revert e1) (revert e2)
revert (PMA.Let x e1 e2)
    = Let (BDecls [PatBind noSrcLoc
                           (PVar (Ident (PMA.fromName x)))
                           Nothing
                           (UnGuardedRhs (revert e1))
                           (BDecls [])
                  ]
          )
          (revert e2)
revert (PMA.If _lbl e0 e1 e2)
    = If (revert e0) (revert e1) (revert e2)
-- Operators
revert (PMA.Op op e1 e2)
    = Paren (InfixApp (revert e1) (revertOp op) (revert e2)) where
        revertOp (PMA.LEQ) = QConOp (UnQual (Symbol "<="))
        revertOp (PMA.ADD) = QConOp (UnQual (Symbol "+"))
-- Pairs
revert (PMA.Pair e1 e2)
    = Tuple [revert e1, revert e2]
revert (PMA.Fst e)
    = App (Var (UnQual (Ident "fst"))) (revert e)
revert (PMA.Snd e)
    = App (Var (UnQual (Ident "snd"))) (revert e)
-- Lists
revert (PMA.Nil)
    = List []
revert (PMA.Cons e1 e2)
    = Paren (InfixApp (revert e1) (QConOp (Special Cons)) (revert e2))
revert (PMA.Case _lbl e0 arm1 arm2)
    = Case (revert e0)
           (maybe [] (\e1 -> [Alt noSrcLoc
                                 (PList [])
                                 (UnGuardedAlt (revert e1))
                                 (BDecls [])
                             ]
                     ) arm1
           ++
            maybe [] (\(x,xs,e2) -> [Alt noSrcLoc
                                        (PInfixApp (PVar (Ident (PMA.fromName x)))
                                                   (Special Cons)
                                                   (PVar (Ident (PMA.fromName xs)))
                                        )
                                        (UnGuardedAlt (revert e2))
                                        (BDecls [])
                                    ]
                     ) arm2
           )

-- | Pre-Processing

preProcess (Module _ moduleName [] Nothing Nothing [] decls)
    = let (funBinds, patBinds, []) = splitTopLevel decls
          patBinds2 = map desugarFunBind funBinds
          topLevel = Let (BDecls (patBinds ++ patBinds2)) (Var (UnQual (Ident "main")))
       in topLevel

-- * Split top-level declarations into bindings and data type declarations

splitTopLevel :: [Decl] -> ([Decl], [Decl], [Decl])
splitTopLevel [] = ([],[],[])
splitTopLevel (dd@(DataDecl _ _ _ _ _ _ _):decls)
    = let (fbs, pbs, dds) = splitTopLevel decls in (fbs, pbs, dd:dds)
splitTopLevel (fb@(FunBind matches):decls)
    = let (fbs, pbs, dds) = splitTopLevel decls in (fb:fbs, pbs, dds)
splitTopLevel (pb@(PatBind _ _ _ _ _):decls)
    = let (fbs, pbs, dds) = splitTopLevel decls in (fbs, pb:pbs, dds)
    
-- * Desugar function bindigns into pattern bindings
-- FIXME: fails in most cases

desugarFunBind :: Decl -> Decl
desugarFunBind (FunBind [Match srcLoc name pats Nothing (UnGuardedRhs e) (BDecls [])])
    = let e' = Lambda noSrcLoc pats e
       in PatBind srcLoc (PVar name) Nothing (UnGuardedRhs e') (BDecls [])
desugarFunBind p@(PatBind _ _ _ _ _) = p

-- * Extract the defintions and uses from a pattern binding (FIXME: make into a class?)

defUseDecl :: Decl -> (Decl, S.Set Name, S.Set Name)
defUseDecl decl@(PatBind _ pat Nothing rhs (BDecls []))
    = let def = defPat pat
          use = useRhs rhs
       in if S.size def /= 1
          then error $ "I'm not sure if I can reliably handle simultaneous"
                       ++ "declarations yet, as this gets tricky in combination"
                       ++ "with mutual recursion"
          else (decl, def, use)

defPat :: Pat -> S.Set Name
defPat (PVar name) = S.singleton name
defPat (PLit _) = S.empty

useRhs :: Rhs -> S.Set Name
useRhs (UnGuardedRhs exp) = useExp exp

useExp :: Exp -> S.Set Name
useExp (Var (UnQual name)) = S.singleton name
useExp (Con _) = S.empty
useExp (Lit _) = S.empty
useExp (InfixApp e1 _op e2) = useExp e1 `S.union` useExp e2
useExp (App e1 e2) = useExp e1 `S.union` useExp e2
useExp (Lambda _ _pats e) = useExp e
useExp (Let (BDecls decls) e) = let decls' = map desugarFunBind decls
                                 in S.unions (map useDecl decls') `S.union` useExp e
useExp (If e0 e1 e2) = useExp e0 `S.union` useExp e1 `S.union` useExp e2
useExp (Case e alts) = S.unions (map useAlt alts) `S.union` useExp e
useExp (Tuple [e1,e2]) = useExp e1 `S.union` useExp e2
useExp (List es) = S.unions (map useExp es)
useExp (Paren e) = useExp e
useExp x = error $ "useExp: " ++ show x

useDecl :: Decl -> S.Set Name
useDecl (PatBind _ _pat Nothing rhs (BDecls [])) = useRhs rhs
useDecl x = error $ "useDecl: " ++ show x

useAlt :: Alt -> S.Set Name
useAlt (Alt _ _pat (UnGuardedAlt e) (BDecls [])) = useExp e

-- | Binding-group analysis

defUseGraph :: [(Decl, S.Set Name, S.Set Name)] -> [(Decl, S.Set Name, [S.Set Name])]
defUseGraph all
    = foldr (\(decl, def, use) r ->
                (decl, def, foldr (\(_, def', use') r' -> if use `S.overlap` def' then def' : r' else r') [] all) : r
            ) [] all

-- | blablabla

-- * Main

header hdr
    = "== " ++ hdr ++ " " ++ replicate (76 - length hdr) '='

-- * haskell-srcs-ext

noSrcLoc = SrcLoc "" 0 0
