-- {-# LANGAUGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}

-- TODO: desugar TyList into TyApp (TyCon []) (TyVar ...)

module TypeInference where

import Prelude

import Control.Monad

import Data.Graph
import Data.List (intersperse)
import Data.Map hiding (lookup, map, toList)
import Data.Set (toList)

import Util
import Util.List

import Language.Haskell.Exts.Annotated

import Common
import PrintType
import Refinement

import TCMonad
import TypeInference.Instantiation
import TypeInference.Generalization

import Solver.Unification

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

typeInfer :: (Ord l, Show l) => Env -> Exp l -> TC R


-- * Variables
typeInfer gamma (Var _ name)
    | Just ty <- lookup (stripQNameAnn name) gamma
       = do (tyInst, rcInst) <- inst ty
            return R { _ty = tyInst
                     , _cs = []
                     , _rc = rcInst
                     }
    | UnQual NoPhi (Ident NoPhi "fst") <- stripQNameAnn name
        = do tv1 <- freshTV
             tv2 <- freshTV
             rv1 <- freshRV
             rv2 <- freshRV

             let ty = TyFun (Phi rv1) (TyTuple (Phi rv2) Boxed [tv1, tv2]) tv1

             return (R { _ty = ty
                       , _cs = []
                       , _rc = []
                       })
    | UnQual NoPhi (Ident NoPhi "snd") <- stripQNameAnn name
        = do tv1 <- freshTV
             tv2 <- freshTV
             rv1 <- freshRV
             rv2 <- freshRV
             
             let ty = TyFun (Phi rv1) (TyTuple (Phi rv2) Boxed [tv1, tv2]) tv2

             return (R { _ty = ty
                       , _cs = []
                       , _rc = []
                       })
    -- projection function for n-tuples (generated in the mutual-recursion type rule)
    | UnQual NoPhi (Ident NoPhi ('_':'_':'p':'r':'j':'_':ss)) <- stripQNameAnn name
        = do let (index, arity) = (\(a,_:b) -> (read a, read b)) (break (=='_') ss)
             fs                 <- replicateM arity freshName
             f3                 <- freshName
             f4                 <- freshName
             
             let tv1            = TyFun (Phi (RefVar f4)) (TyTuple (Phi (RefVar f3)) Boxed (map (TyVar NoPhi) fs)) (TyVar NoPhi (fs!!(index-1)))

             return (R { _ty = tv1
                       , _cs = []
                       , _rc = []
                       })
    -- hard-coded (<=) operator to make intersting function such as risers type-check
    | UnQual NoPhi (Symbol NoPhi "<=") <- stripQNameAnn name
        = do f1 <- freshName
             f2 <- freshName
             f3 <- freshName
             f4 <- freshName
             f5 <- freshName        
             let tv1 = TyFun (Phi (RefVar f1)) (TyCon (Phi (RefVar f3)) (UnQual NoPhi (Ident NoPhi "Int"))) (TyFun (Phi (RefVar f2)) (TyCon (Phi (RefVar f4)) (UnQual NoPhi (Ident NoPhi "Int"))) (TyCon (Phi (RefVar f5)) (UnQual NoPhi (Ident NoPhi "Bool"))))
             return (R { _ty = tv1
                       , _cs = []
                       , _rc = []
                       })
    | otherwise
        = error ("typeInfer: variable \"" ++ prettyPrint name ++ "\" not found in environment\n" ++ concatMap (\(name, ty) -> prettyPrint name ++ " :: " ++ printType ty ++ "\n") gamma)

-- * Constants and constructors
typeInfer gamma (Con _ (Special _ (UnitCon _)))
    = do rv <- freshRV
         return (R { _ty = TyCon (Phi rv) (Special NoPhi (UnitCon NoPhi))
                   , _cs = []
                   , _rc = []
                   })

typeInfer gamma (Con _ (UnQual _ (Ident _ "True")))
    = do rv <- freshRV
         return (R { _ty = TyCon (Phi rv) (UnQual NoPhi (Ident NoPhi "Bool"))
                   , _cs = []
                   , _rc = []
                   })

typeInfer gamma (Con _ (UnQual _ (Ident _ "False")))
    = do rv <- freshRV
         return (R { _ty = TyCon (Phi rv) (UnQual NoPhi (Ident NoPhi "Bool"))
                   , _cs = []
                   , _rc = []
                   })

typeInfer gamma (Lit _ (Int _ n _))
    = do rv <- freshRV
         return (R { _ty = TyCon (Phi rv) (UnQual NoPhi (Ident NoPhi "Int"))
                , _cs = []
                , _rc = []
                })

typeInfer gamma (NegApp _ (Lit _ (Int _ n _))) -- TODO: make more general
    = do rv <- freshRV
         return (R { _ty = TyCon (Phi rv) (UnQual NoPhi (Ident NoPhi "Int"))
                   , _cs = []
                   , _rc = []
                   })

typeInfer gamma (Tuple _ es)
    = do rv      <- freshRV
         results <- mapM (typeInfer gamma) es
         return (R { _ty = TyTuple (Phi rv) Boxed (map _ty results)
                   , _cs = concat (map _cs results)
                   , _rc = [] ++ concat (map _rc results)
                   })

typeInfer gamma (List _ es)
    = do tv1     <- freshTV
         rv1     <- freshRV

         results <- mapM (typeInfer gamma) es
        
         return (R { _ty = TyList (Phi rv1) tv1
                   , _cs = map (:=: tv1) (map _ty results)
                           ++ concat (map _cs results)
                   , _rc = [] ++ concat (map _rc results)
                   })

-- * Cons
typeInfer gamma (InfixApp _ x (QConOp _ (Special _ (Cons _))) xs) -- TODO: desugar and add to Gamma0
    = do f3 <- freshRV
         f4 <- freshRV
    
         R { _ty = th, _cs = ch, _rc = rh } <- typeInfer gamma x
         R { _ty = tt, _cs = ct, _rc = rt } <- typeInfer gamma xs
         
         return (R { _ty = TyList (Phi f3) th
                   , _cs = [TyList (Phi f4) th :=: tt] ++ ch ++ ct
                   , _rc = [] ++ rh ++ rt
                   })

-- * Lambda abstractions
typeInfer gamma (Lambda _ [PVar _ name'] e)
    = do  let name = UnQual NoPhi (stripNameAnn name')

          tv1 <- freshTV
          rv1 <- freshRV

          R { _ty = tE, _cs = cE, _rc = rcE }
            <- typeInfer ((name, tv1):gamma) e

          return (R { _ty = TyFun (Phi rv1) tv1 tE
                    , _cs = cE
                    , _rc = [] ++ rcE
                    })

-- * Application
typeInfer gamma (App _ f x)
    = do tv1     <- freshTV
         rv1     <- freshRV
          
         R { _ty = tF, _cs = cF, _rc = rcF } <- typeInfer gamma f
         R { _ty = tX, _cs = cX, _rc = rcX } <- typeInfer gamma x
            
         return (R { _ty = tv1
                   , _cs = [tF :=: (TyFun (Phi rv1) tX tv1)] ++ cF ++ cX
                   , _rc = [] ++ rcF ++ rcX
                   })

-- * Infix application (desugar-step)
typeInfer gamma (InfixApp l x op y)
    = typeInfer gamma (App l (App l (op2exp op) x) y)
        where op2exp (QVarOp l name) = Var l name
              op2exp (QConOp l name) = Con l name

-- * Let-bindings
typeInfer gamma (Let _ (BDecls _ binds) e2)
    = let -- Binding group analysis
          bindGroups = stronglyConnComp (map toGraphElement binds)
            where toGraphElement (PatBind _ (PVar _ name) _ (UnGuardedRhs _ e1) _)
                    = ( (name, e1)
                      , stripNameAnn name
                      , map stripNameAnn . toList . uses $ e1 )
       in typeInferBindingGroup gamma bindGroups e2

-- * If-then-else
typeInfer gamma (If _ g e1 e2)
    = do rv1 <- freshRV
    
         R { _ty = tG,  _cs = cG , _rc = rcG  } <- typeInfer gamma g
         R { _ty = tE1, _cs = cE1, _rc = rcE1 } <- typeInfer gamma e1
         R { _ty = tE2, _cs = cE2, _rc = rcE2 } <- typeInfer gamma e2

         return (R { _ty = tE1
                   , _cs = [tG :=: tyBool rv1, tE1 :=: tE2] ++ cG ++ cE1 ++ cE2
                   , _rc = [] ++ rcG ++ rcE1 ++ rcE2
                   })

-- * Case (Lists)
typeInfer gamma (Case _ g [Alt _ (PList _ []) (UnGuardedAlt _ eNil) _, Alt _ (PParen _ (PInfixApp _ (PVar _ x') (Special _ (Cons _)) (PVar _ xs'))) (UnGuardedAlt _ eCons) _])
    = do tv1 <- freshTV
         rv1 <- freshRV
         rv2 <- freshRV
          
         let x   = UnQual NoPhi (stripNameAnn x' )
         let xs  = UnQual NoPhi (stripNameAnn xs')
         let env = [(x, tv1), (xs, TyList (Phi rv2) tv1)]
    
         R { _ty = tG, _cs = cG, _rc = rcG } <- typeInfer gamma g
         R { _ty = tN, _cs = cN, _rc = rcN } <- typeInfer gamma eNil
         R { _ty = tC, _cs = cC, _rc = rcC } <- typeInfer (env ++ gamma) eCons
          
         return (R { _ty = tN
                   , _cs = [tG :=: TyList (Phi rv1) tv1, tN :=: tC] ++ cG ++ cN ++ cC
                   , _rc = [] ++ rcG ++ rcN ++ rcC
                   })

-- * Case (Nil only)
typeInfer gamma (Case _ g [Alt _ (PList _ []) (UnGuardedAlt _ eNil) _])
    = do tv1 <- freshTV
         rv1 <- freshRV
         rv2 <- freshRV
              
         R { _ty = tG, _cs = cG, _rc = rcG } <- typeInfer gamma g
         R { _ty = tN, _cs = cN, _rc = rcN } <- typeInfer gamma eNil
          
         return (R { _ty = tN
                   , _cs = [tG :=: TyList (Phi rv1) tv1] ++ cG ++ cN
                   , _rc = [] ++ rcG ++ rcN
                   })
            
-- * Case (Cons only)
typeInfer gamma (Case _ g [Alt _ (PParen _ (PInfixApp _ (PVar _ x') (Special _ (Cons _)) (PVar _ xs'))) (UnGuardedAlt _ eCons) _])
    = do tv1 <- freshTV
         rv1 <- freshRV
         rv2 <- freshRV
          
         let x   = UnQual NoPhi (stripNameAnn x' )
         let xs  = UnQual NoPhi (stripNameAnn xs')
         let env = [(x, tv1), (xs, TyList (Phi rv2) tv1)]
    
         R { _ty = tG, _cs = cG, _rc = rcG } <- typeInfer gamma g
         R { _ty = tC, _cs = cC, _rc = rcC } <- typeInfer (env ++ gamma) eCons
          
         return (R { _ty = tC
                   , _cs = [tG :=: TyList (Phi rv1) tv1] ++ cG ++ cC
                   , _rc = [] ++ rcG ++ rcC
                   })

-- * Parenthesis
typeInfer gamma (Paren _ e) = typeInfer gamma e

-- * Catch-all
typeInfer _ e = error ("typeInfer (unsupported expression): " ++ show e)

-- | Let-bindings | ------------------------------------------------------------

typeInferBindingGroup :: (Ord l, Ord l', Show l, Show l') =>
      Env -> [SCC (Name l', Exp l')] -> Exp l -> TC R

-- * Processed all binding groups, continue inferring type of the body
typeInferBindingGroup gamma [] e2
    = typeInfer gamma e2
    
-- * Non-recursive binding
typeInferBindingGroup gamma (AcyclicSCC (name', e1) : bgs) e2
    = do let name = UnQual NoPhi (stripNameAnn name')

         R { _ty = s1, _cs = c1, _rc = rc1 }
            <- typeInfer gamma e1

         (sigma, theta)
            <- gen gamma s1 c1 rc1

         R { _ty = t2, _cs = c2, _rc = rc2 }
            <- typeInferBindingGroup ((name, sigma):(theta `applySubst` gamma)) bgs e2

         logTC ("[Let] " ++ prettyPrint name ++ " :: " ++ printType sigma)

         return (R { _ty = t2
                   , _cs = c2 ++ c1
                   , _rc = rc2
                   })

-- * Recursive binding
typeInferBindingGroup gamma (CyclicSCC [(name', e1)] : bgs) e2
    = do let name = UnQual NoPhi (stripNameAnn name')
          
         tv1 <- freshTV
         rv1 <- freshRV

         let e1Fix = Lambda (error "Lambda") [PVar (error "PVar") name'] e1

         R { _ty = sFix, _cs = cFix, _rc = rcFix }
            <- typeInfer gamma e1Fix

         (sigma, theta)
            <- gen gamma tv1 ((sFix :=: TyFun (Phi rv1) tv1 tv1) : cFix) rcFix

         R { _ty = t2, _cs = c2, _rc = rc2 }
            <- typeInferBindingGroup ((name, sigma):(theta `applySubst` gamma)) bgs e2
            
         logTC ("[LetRec] " ++ prettyPrint name ++ " :: " ++ printType sigma)
            
         return (R { _ty = t2
                   , _cs = c2 ++ cFix
                   , _rc = rc2
                   })

-- * Mutually recursive bindings
typeInferBindingGroup gamma (CyclicSCC bs : bgs) e2
    = do fn <- freshName -- fresh name for transformed binding
         let (names', names, es) = unzip3 (map (\(name', e) -> (name', stripNameAnn name', e)) bs)
         let l                   = length names
         let expSubst = fromList (zipWith3 (\idx name' name -> (name, App undefined (Var undefined (UnQual undefined (Ident undefined ("__prj_"++(show idx)++"_"++(show l))))) (Var undefined (UnQual undefined (unstripNameAnn fn))))) [1..] names' names)

         let e'       = Tuple (error "Tuple") (map (applyExpSubst expSubst) es)
         let e'Fix    = Lambda (error "Lambda") [PVar (error "PVar") (unstripNameAnn fn)] e'

         R { _ty = sFix, _cs = cFix, _rc = rcFix }
            <- typeInfer gamma e'Fix

         tv1 <- freshTV
         rv1 <- freshRV
         
         (sigma, theta)
            <- gen gamma tv1 ((sFix :=: TyFun (Phi rv1) tv1 tv1) : cFix) rcFix

         R { _ty = t2, _cs = c2, _rc = rc2 }
            <- typeInferBindingGroup ((UnQual NoPhi fn, sigma):(theta `applySubst` gamma)) bgs (applyExpSubst expSubst e2)

         logTC ("[LetMutRec] (" ++ concat (intersperse "," (map prettyPrint names)) ++ ") :: " ++ printType sigma)

         return (R { _ty = t2
                   , _cs = c2 ++ cFix
                   , _rc = rc2
                   })
