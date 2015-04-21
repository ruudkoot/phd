module Analysis.Infer.Common (
    checkKind
) where

import           Analysis.Common
import           Analysis.Infer.Types

-- * Kind checking of annotation

checkKind :: KindEnv -> Exn -> Maybe Kind
checkKind env ExnEmpty
    = return EXN
checkKind env (ExnUnion exn1 exn2)
    = do k1 <- checkKind env exn1
         k2 <- checkKind env exn2
         if k1 == k2 then
            return k1
         else
            error "kind (ExnUnion)"
checkKind env (ExnCon _)
    = return EXN
checkKind env (ExnVar e)
    = case lookup e env of
        Just k -> return k
        _      -> error "unbound (ExnVar)"
checkKind env (ExnApp exn1 exn2)
    = do (k2' :=> k1) <- checkKind env exn1
         k2           <- checkKind env exn2
         if k2 == k2' then
            return k1
         else
            error "kind (ExnApp)"
checkKind env (ExnAbs e k exn)
    = do () <- case lookup e env of
                 Nothing -> return ()
                 _       -> error "shadowing (ExnAbs)"
         k2 <- checkKind ((e,k):env) exn
         return (k :=> k2)
