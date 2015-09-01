-- {-# LANGAUGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}

-- TODO: desugar TyList into TyApp (TyCon []) (TyVar ...)

module TypeInference where

import Prelude

import Data.Graph
import Data.Map hiding (lookup, map, toList)
import Data.Set (toList)

import Util
import Util.List

import Language.Haskell.Exts.Annotated

import Common
import PatternTyping
import Refinement
import Solver
import qualified AbstractInterpretation as AI

import Abstract.Unit
import Abstract.Bool
import Abstract.Int
import Abstract.List hiding (Cons)

deriving instance Show a => Show (SCC a)

-- | Result of type inference

data R = R { _ty :: Type Phi            -- annotated type
           , _cs :: [Constr]            -- constraints on simple types
           , _rc :: [RefConstr]         -- constraints on refinement variables
        -- , _ae :: Exp (Type Phi)      -- type-annotated AST
           }
    
-- | Create a fresh variable

makeVar :: Name Phi -> Name Phi -> Type Phi
makeVar t phi = TyVar (Phi (RefVar phi)) t
    
-- | Type inference

typeInfer :: (Ord l, Show l) => Env -> Fresh -> Exp l -> R

-- * Variables
typeInfer gamma (f1:f2:f3:f4:f5:fresh) (Var _ name)
    | Just ty <- lookup (stripQNameAnn name) gamma
       = let (tyInst, rcInst) = inst fresh ty
          in R { _ty = tyInst
               , _cs = []
               , _rc = rcInst
               }
    | UnQual NoPhi (Ident NoPhi "fst") <- stripQNameAnn name
        = let tv1 = TyFun (Phi (RefVar f4)) (TyTuple (Phi (RefVar f3)) Boxed [TyVar NoPhi f1, TyVar NoPhi f2]) (TyVar NoPhi f1)
           in R { _ty = tv1
                , _cs = []
                , _rc = [RefVar f3 :<: RefTop, RefLambda :<: RefVar f4]
                }
    | UnQual NoPhi (Ident NoPhi "snd") <- stripQNameAnn name
        = let tv1 = TyFun (Phi (RefVar f4)) (TyTuple (Phi (RefVar f3)) Boxed [TyVar NoPhi f1, TyVar NoPhi f2]) (TyVar NoPhi f2)
           in R { _ty = tv1
                , _cs = []
                , _rc = [RefVar f3 :<: RefTop, RefLambda :<: RefVar f4]
                }
    -- projection function for n-tuples (generated in the mutual-recursion type rule)
    | UnQual NoPhi (Ident NoPhi ('_':'_':'p':'r':'j':'_':ss)) <- stripQNameAnn name
        = let (index, arity) = (\(a,_:b) -> (read a, read b)) (break (=='_') ss)
              fs             = take arity fresh
              tv1            = TyFun (Phi (RefVar f4)) (TyTuple (Phi (RefVar f3)) Boxed (map (TyVar NoPhi) fs)) (TyVar NoPhi (fs!!(index-1)))
           in R { _ty = tv1
                , _cs = []
                , _rc = [RefVar f3 :<: RefTop, RefLambda :<: RefVar f4]
                }
    -- hard-coded (<=) operator to make intersting function such as risers type-check
    | UnQual NoPhi (Symbol NoPhi "<=") <- stripQNameAnn name
        = let tv1 = TyFun (Phi (RefVar f1)) (TyCon (Phi (RefVar f3)) (UnQual NoPhi (Ident NoPhi "Int"))) (TyFun (Phi (RefVar f2)) (TyCon (Phi (RefVar f4)) (UnQual NoPhi (Ident NoPhi "Int"))) (TyCon (Phi (RefVar f5)) (UnQual NoPhi (Ident NoPhi "Bool"))))
              in R { _ty = tv1
                   , _cs = []
                   , _rc = [ RefLambda :<: RefVar f1, RefLambda :<: RefVar f2
                           , RefVar f3 :<: RefInt topAbsInt, RefVar f4 :<: RefInt topAbsInt
                           , RefBool topAbsBool :<: RefVar f5
                           ]
                   }
    | otherwise
        = error ("typeInfer: variable \"" ++ prettyPrint name ++ "\" not found in environment\n" ++ concatMap ((++"\n") . prettyPrint) (map fst gamma))

-- * Constants and constructors
typeInfer gamma (f:_) (Con _ (Special _ (UnitCon _)))
    = R { _ty = TyCon (Phi (RefVar f)) (Special NoPhi (UnitCon NoPhi))
        , _cs = []
        , _rc = [RefUnit (injectUnit ()) :<: RefVar f]
        }

typeInfer gamma (f:_) (Con _ (UnQual _ (Ident _ "True")))
    = R { _ty = TyCon (Phi (RefVar f)) (UnQual NoPhi (Ident NoPhi "Bool"))
        , _cs = []
        , _rc = [RefBool (injectBool True) :<: RefVar f]
        }

typeInfer gamma (f:_) (Con _ (UnQual _ (Ident _ "False")))
    = R { _ty = TyCon (Phi (RefVar f)) (UnQual NoPhi (Ident NoPhi "Bool"))
        , _cs = []
        , _rc = [RefBool (injectBool False) :<: RefVar f]
        }

{-    
typeInfer gamma (a:b:fresh) (Con (UnQual (Ident "Left" )))
    = R { _ty = TyVar a --> tyEither (TyVar a) (TyVar b)
        , _cs = []
        }
             
typeInfer gamma (a:b:fresh) (Con (UnQual (Ident "Right")))
    = R { _ty = TyVar b --> tyEither (TyVar a) (TyVar b)
        , _cs = []
        }
-}

typeInfer gamma (f:_) (Lit _ (Int _ n _))
    = R { _ty = TyCon (Phi (RefVar f)) (UnQual NoPhi (Ident NoPhi "Int"))
        , _cs = []
        , _rc = [RefInt (injectInt n) :<: RefVar f]
        }

typeInfer gamma (f:_) (NegApp _ (Lit _ (Int _ n _))) -- TODO: make more general
    = R { _ty = TyCon (Phi (RefVar f)) (UnQual NoPhi (Ident NoPhi "Int"))
        , _cs = []
        , _rc = [RefInt (injectInt (-n)) :<: RefVar f]
        }

typeInfer gamma (f:fresh) (Tuple _ es)
    = let fe      = zip (splice (length es) fresh) es
          results = map (\(f, e) -> typeInfer gamma f e) fe
       in R { _ty = TyTuple (Phi (RefVar f)) Boxed (map _ty results)
            , _cs = concat (map _cs results)
            , _rc = [RefTop :<: RefVar f] ++ concat (map _rc results)
            }
       
typeInfer gamma (f1:f2:f3:fresh) (List _ es)
    = let fe      = zip (splice (length es) fresh) es
          results = map (\(f, e) -> typeInfer gamma f e) fe
          tyParam = (TyVar NoPhi f1)
       in R { _ty = TyList (Phi (RefVar f3)) tyParam
            , _cs = map (=: tyParam) (map _ty results)
                      ++ concat (map _cs results)
            , _rc = [RefList (injectList es) :<: RefVar f3] ++ concat (map _rc results)
            }

-- * Cons
typeInfer gamma fresh (InfixApp _ x (QConOp _ (Special _ (Cons _))) xs) -- desugar and add to Gamma0
    = let (fresh1, fresh2, (f3:f4:_)) = splice3 fresh
          R { _ty = th, _cs = ch, _rc = rh } = typeInfer gamma fresh1 x
          R { _ty = tt, _cs = ct, _rc = rt } = typeInfer gamma fresh2 xs
       in R { _ty = TyList (Phi (RefVar f3)) th
            , _cs = [TyList (Phi (RefVar f4)) th =: tt] ++ ch ++ ct
            , _rc = [RefList (absCons f4) :<: RefVar f3] ++ rh ++ rt
            }

-- * Lambda abstractions
typeInfer gamma (f1:f2:fresh) (Lambda _ [PVar _ name'] e)
    = let name = UnQual NoPhi (stripNameAnn name')

          tv1  = TyVar  NoPhi f1
          rv1  = RefVar       f2

          R { _ty = tE, _cs = cE, _rc = rcE }
            = typeInfer ((name, tv1):gamma) fresh e

       in R { _ty = TyFun (Phi rv1) tv1 tE
            , _cs = cE
            , _rc = [RefLambda :<: rv1] ++ rcE
            }

-- * Application
typeInfer gamma fresh (App _ f x)
    = let (fresh1, fresh2, f1:f2:f3:_) = splice3 fresh
    
          tv1     = TyVar  NoPhi f1
          tv2     = TyVar  NoPhi f2
          rv1     = RefVar       f3
          
          R { _ty = tF, _cs = cF, _rc = rcF }
            = typeInfer gamma fresh1 f

          R { _ty = tX, _cs = cX, _rc = rcX }
            = typeInfer gamma fresh2 x
            
       in R { _ty = tv2
            , _cs = [(:=:!) "app1" tF (TyFun (Phi rv1) tv1 tv2), (:=:!) "app2" tv1 tX] ++ cF ++ cX --- could be reduced to one constriant...
            , _rc = [RefLambda :<: rv1 {- or the other way around, or both? -}] ++ rcF ++ rcX
            }
            
-- * Infix application (desugar-step)
typeInfer gamma fresh (InfixApp l x op y)
    = typeInfer gamma fresh (App l (App l (op2exp op) x) y)
        where op2exp (QVarOp l name) = Var l name
              op2exp (QConOp l name) = Con l name

-- * Let-binding
typeInfer gamma fresh (Let _ (BDecls _ binds) e2)
    -- Recursive
    = let bindGroups = stronglyConnComp (map toGraphElement binds)
            where toGraphElement (PatBind _ (PVar _ name) _ (UnGuardedRhs _ e1) _)
                    = ( (name, e1)
                      , stripNameAnn name
                      , map stripNameAnn . toList . uses $ e1 )
       in ti fresh gamma bindGroups e2

-- * If-then-else
typeInfer gamma fresh (If _ g e1 e2)
    = let [fs1,fs2,fs3,(f4:_)] = splice 4 fresh
          R { _ty = tG,  _cs = cG , _rc = rcG  } = typeInfer gamma fs1 g
          R { _ty = tE1, _cs = cE1, _rc = rcE1 } = typeInfer gamma fs2 e1
          R { _ty = tE2, _cs = cE2, _rc = rcE2 } = typeInfer gamma fs3 e2
       in R { _ty = tE1
            , _cs = [tG =: tyBool (RefVar f4), tE1 =: tE2] ++ cG ++ cE1 ++ cE2
            , _rc = [RefVar f4 :<: RefBool topAbsBool] ++ rcG ++ rcE1 ++ rcE2
            }
            
-- * Case (Lists)
typeInfer gamma fresh (Case _ g [Alt _ (PList _ []) (UnGuardedAlt _ eNil) _, Alt _ (PParen _ (PInfixApp _ (PVar _ x') (Special _ (Cons _)) (PVar _ xs'))) (UnGuardedAlt _ eCons) _])
    = let [fs1, fs2, fs3, f1:f2:f3:_] = splice 4 fresh

          tv1 = TyVar  NoPhi f1
          rv1 = RefVar       f2
          rv2 = RefVar       f3
          
          x   = UnQual NoPhi (stripNameAnn x' )
          xs  = UnQual NoPhi (stripNameAnn xs')
          env = [(x, tv1), (xs, TyList (Phi rv2) tv1)]
    
          R { _ty = tG, _cs = cG, _rc = rcG } = typeInfer gamma fs1 g
          R { _ty = tN, _cs = cN, _rc = rcN } = typeInfer gamma fs2 eNil
          R { _ty = tC, _cs = cC, _rc = rcC } = typeInfer (env ++ gamma) fs3 eCons
          
       in R { _ty = tN
            , _cs = [tG =: TyList (Phi rv1) tv1, tN =: tC] ++ cG ++ cN ++ cC
            , _rc = [rv1 :<: RefList (injectList[] `mergeAbsList` consRefVar rv2)] ++ rcG ++ rcN ++ rcC
            }
            
-- * Case (Nil only)
typeInfer gamma fresh (Case _ g [Alt _ (PList _ []) (UnGuardedAlt _ eNil) _])
    = let [fs1, fs2, fs3, f1:f2:f3:_] = splice 4 fresh
    
          tv1 = TyVar  NoPhi f1
          rv1 = RefVar       f2
          rv2 = RefVar       f3
              
          R { _ty = tG, _cs = cG, _rc = rcG } = typeInfer gamma fs1 g
          R { _ty = tN, _cs = cN, _rc = rcN } = typeInfer gamma fs2 eNil
          
       in R { _ty = tN
            , _cs = [tG =: TyList (Phi rv1) tv1] ++ cG ++ cN
            , _rc = [rv1 :<: RefList (injectList [])] ++ rcG ++ rcN
            }
            
-- * Case (Cons only)
typeInfer gamma fresh (Case _ g [Alt _ (PParen _ (PInfixApp _ (PVar _ x') (Special _ (Cons _)) (PVar _ xs'))) (UnGuardedAlt _ eCons) _])
    = let [fs1, fs2, fs3, f1:f2:f3:_] = splice 4 fresh
    
          tv1 = TyVar  NoPhi f1
          rv1 = RefVar       f2
          rv2 = RefVar       f3
          
          x   = UnQual NoPhi (stripNameAnn x' )
          xs  = UnQual NoPhi (stripNameAnn xs')
          env = [(x, tv1), (xs, TyList (Phi rv2) tv1)]
    
          R { _ty = tG, _cs = cG, _rc = rcG } = typeInfer gamma fs1 g
          R { _ty = tC, _cs = cC, _rc = rcC } = typeInfer (env ++ gamma) fs3 eCons
          
       in R { _ty = tC
            , _cs = [tG =: TyList (Phi rv1) tv1] ++ cG ++ cC
            , _rc = [rv1 :<: RefList (consRefVar rv2)] ++ rcG ++ rcC
            }
       

{-
-- * Case
typeInfer gamma fresh (Case _ e alts)
    = let [f1, f2] = splice 2 fresh
          R { _ty = tG, _cs = cG } = typeInfer gamma f1 e
          R { _ty = tR, _cs = cR } = caseType gamma f2 tG (map (\(Alt _ pat (UnGuardedAlt _ exp) _) -> (pat, exp)) alts)
       in R { _ty = tR
            , _cs = cG ++ cR
            }
    where
        caseType :: Env -> Fresh -> Type Phi -> [(Pat Phi, Exp Phi)] -> R
        caseType gamma (f:fresh) tE pes
            = let -- Fresh variables
                  [fs1,fs2]   = map (splice (length pes)) (splice 2 fresh)
                  -- Setup
                  (ps,  exps) = unzip pes
                  -- Pattern type alternatives
                  (pts, envs) = unzip (zipWith (patternType gamma) fs1 ps)
                  -- Type infer alternatives
                  rs          = zipWith3 (typeInfer . (++ gamma)) envs fs2 exps
               in R { _ty = TyVar NoPhi f
                    , _cs = map (tE =:) pts
                            ++ map (TyVar NoPhi f =:) (map _ty rs)
                            ++ concatMap _cs rs
                    }
-}
-- * Parenthesis
typeInfer gamma fresh (Paren _ e) = typeInfer gamma fresh e

-- * Catch-all
typeInfer _ _ e = error ("typeInfer: " ++ show e)

-- | Let-bindings

ti fresh gamma [] e2
    = typeInfer gamma fresh e2
    
-- Non-recursive
ti fresh gamma (AcyclicSCC (name', e1) : bgs) e2
    = let (fresh1, fresh2, _) = splice3 fresh
          name                = UnQual NoPhi (stripNameAnn name')

          R { _ty = s1, _cs = c1, _rc = rc1 }
            = typeInfer gamma fresh1 e1
          sigma
            = unify c1
          t1
            -- = gen gamma (sigma $@ s1)
            = s1
          R { _ty = t2, _cs = c2, _rc = rc2 }
            = ti fresh2 ((name, t1):({- sigma $&& -}gamma)) bgs e2

       in R { _ty = t2
            , _cs = c1 ++ c2
            , _rc = rc1 ++ rc2
            }

-- Recursive
ti fresh gamma (CyclicSCC [(name', e1)] : bgs) e2
    = let (fresh1, fresh2, f1:f2:_) = splice3 fresh
          name                    = UnQual NoPhi (stripNameAnn name')
          
          tv1                     = TyVar  NoPhi f1
          rv1                     = RefVar       f2

          R { _ty = sFix, _cs = cFix, _rc = rcFix }
            = typeInfer gamma fresh1 (Lambda (error "Lambda") [PVar (error "PVar") name'] e1)

          sigma
            = unify ((sFix =: TyFun (Phi rv1) tv1 tv1) : cFix)

          genTau
            -- = gen gamma (sigma $@ tv1)
            = sigma $@ tv1

          R { _ty = t2, _cs = c2, _rc = rc2 }
            = ti fresh2 ((name, genTau):({-sigma $&& -}gamma)) bgs e2
            
       in R { _ty = t2
            , _cs = {- (sFix =: TyFun (Phi rv1) tv1 tv1) : -} cFix ++ c2
            , _rc = rcFix ++ rc2
            }

-- Mutually recursive
ti fresh gamma (CyclicSCC bs : bgs) e2
    = let (fresh1, fresh2, fn:f1:f2:_) = splice3 fresh

          freshName           = fn
          (names', names, es) = unzip3 (map (\(name', e) -> (name', stripNameAnn name', e)) bs)
          l                   = length names

          -- expSubst :: Map (Name Phi) (Exp l)
          expSubst = fromList (zipWith3 (\idx name' name -> (name, App undefined (Var undefined (UnQual undefined (Ident undefined ("__prj_"++(show idx)++"_"++(show l))))) (Var undefined (UnQual undefined (unstripNameAnn fn))))) [1..] names' names)

          e' = Tuple (error "Tuple") (map (applyExpSubst expSubst) es)

          R { _ty = sFix, _cs = cFix, _rc = rcFix }
            = typeInfer gamma fresh1 (Lambda (error "Lambda") [PVar (error "PVar") (unstripNameAnn freshName)] e')

          tv1 = TyVar  NoPhi f1
          rv1 = RefVar       f2

          sigma  = unify ((sFix =: TyFun (Phi rv1) tv1 tv1) : cFix)
          genTau = sigma $@ tv1
          
          R { _ty = t2, _cs = c2, _rc = rc2 }
            = ti fresh2 ((UnQual NoPhi freshName, genTau):gamma) bgs (applyExpSubst expSubst e2)

       in R { _ty = t2
            , _cs = cFix ++ c2
            , _rc = rcFix ++ rc2
            }
