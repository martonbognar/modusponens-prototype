{-# OPTIONS_GHC -Wall #-}

-- TODO: discuss implicit types in metaTop and metaIs functions

module TypeCheck where


import qualified LambdaC as LC

import Control.Applicative ((<|>))
import Control.Monad (guard)

import CommonTypes
import Syntax

-- * NeColus Typing
-- ----------------------------------------------------------------------------

-- | For a NeColus type, get the corresponding LambdaC type.
translateType :: Type -> LC.Type
translateType TyNat       = LC.TyNat
translateType TyTop       = LC.TyTop
translateType (TyArr a b) = LC.TyArr (translateType a) (translateType b)
translateType (TyIs a b)  = LC.TyTup (translateType a) (translateType b)
translateType (TyRec l a) = LC.TyRec l (translateType a)


-- | Get the type of a variable from a context.
typeFromContext :: Context -> Variable -> Maybe Type
typeFromContext Empty _ = fail "Variable not in context"
typeFromContext (Snoc c v vt) x
  | v == x    = return vt
  | otherwise = typeFromContext c x


-- | Check whether two types are disjoint.
disjoint :: Type -> Type -> Bool
disjoint TyTop        _            = True
disjoint _            TyTop        = True
disjoint (TyArr _ a2) (TyArr _ b2) = disjoint a2 b2
disjoint (TyIs a1 a2) b            = disjoint a1 b && disjoint a2 b
disjoint a            (TyIs b1 b2) = disjoint a b1 && disjoint a b2
disjoint (TyRec l1 a) (TyRec l2 b) = (l1 /= l2) || disjoint a b
disjoint TyNat        TyArr{}      = True
disjoint TyArr{}      TyNat        = True
disjoint TyNat        TyRec{}      = True
disjoint TyRec{}      TyNat        = True
disjoint TyArr{}      TyRec{}      = True
disjoint TyRec{}      TyArr{}      = True
disjoint TyNat        TyNat        = False


-- | Inference
inference :: Context -> Expression -> Maybe (Type, LC.Term)
-- T-TOP
inference _ ExTop = return (TyTop, LC.TmTop)
-- T-LIT
inference _ (ExLit i) = return (TyNat, LC.TmLit i)
-- T-VAR
inference c (ExVar v)
  = do t <- typeFromContext c v
       return (t, LC.TmVar v)
-- T-APP
inference c (ExApp e1 e2)
  = do (TyArr a1 a2, v1) <- inference c e1
       v2 <- checking c e2 a1
       return (a2, LC.TmApp v1 v2)
-- T-ANNO
inference c (ExAnn e a)
  = do v <- checking c e a
       return (a, v)
-- T-PROJ
inference c (ExRecFld e l)
  = do (TyRec l' a, v) <- inference c e
       guard (l' == l)
       return (a, LC.TmRecFld v l)
-- T-MERGE
inference c (ExMerge e1 e2)
  = do (a1, v1) <- inference c e1
       (a2, v2) <- inference c e2
       guard (disjoint a1 a2)
       return (TyIs a1 a2, LC.TmTup v1 v2)
-- T-RCD
inference c (ExRec l e)
  = do (a, v) <- inference c e
       return (TyRec l a, LC.TmRecCon l v)

inference _ ExAbs {} = fail "Inference error"


-- | Checking
checking :: Context -> Expression -> Type -> Maybe LC.Term
-- T-ABS
checking c (ExAbs x e) (TyArr a b)
  = do v <- checking (Snoc c x a) e b
       return (LC.TmAbs x (translateType a) v)
-- T-SUB
checking c e a
  = do (b, v) <- inference c e
       co <- subtype Null b a
       return (LC.TmCast co v)


-- | Meta-top function for coercions.
metaTop :: Queue -> LC.Coercion
metaTop Null = LC.CoAnyTop (translateType TyTop)
metaTop (ExtraLabel q l)
  = LC.CoTrans (LC.CoRec l (metaTop q)) (LC.CoTopRec l)
metaTop (ExtraType q a)
  = LC.CoTrans
      (LC.CoArr (LC.CoAnyTop a') (metaTop q))
      (LC.CoTrans LC.CoTopArr (LC.CoAnyTop a'))
    where
      a' = translateType a


-- | Meta-intersection function for coercions.
metaIs :: Queue -> LC.Coercion
metaIs Null = LC.CoRefl (translateType TyTop)
metaIs (ExtraLabel q l)
  = LC.CoTrans (LC.CoRec l (metaIs q)) (LC.CoDistRec l top' top') where
      top' = translateType TyTop
metaIs (ExtraType q a)
  = LC.CoTrans
      (LC.CoArr (LC.CoRefl a') (metaIs q))
      (LC.CoDistArr a' a' a')
    where
      a' = translateType a


-- | Algorithmic subtyping
subtype :: Queue -> Type -> Type -> Maybe LC.Coercion
-- A-AND
subtype q a (TyIs b1 b2)
  = do c1 <- subtype q a b1
       c2 <- subtype q a b2
       return (LC.CoTrans (metaIs q) (LC.CoPair c1 c2))
-- A-ARR
subtype q a (TyArr b1 b2)
  = subtype (ExtraType q b1) a b2
-- A-RCD
subtype q a (TyRec l b)
  = subtype (ExtraLabel q l) a b
-- A-TOP
subtype q a TyTop
  = return (LC.CoTrans (metaTop q) (LC.CoAnyTop a')) where
      a' = translateType a
-- A-ARRNAT
subtype queue (TyArr a1 a2) TyNat
  | Just (Right a, q) <- viewL queue
  = do c1 <- subtype Null a a1
       c2 <- subtype q a2 TyNat
       return (LC.CoArr c1 c2)
-- A-RCDNAT
subtype queue (TyRec l' a) TyNat
  | Just (Left l, q) <- viewL queue
  , l == l'
  = do c <- subtype q a TyNat
       return (LC.CoRec l c)
-- A-ANDN1 & A-ANDN2
subtype q (TyIs a1 a2) TyNat
  =   do c <- subtype q a1 TyNat
         return (LC.CoTrans c (LC.CoLeft a1' a2'))
  <|> do c <- subtype q a2 TyNat
         return (LC.CoTrans c (LC.CoRight a1' a2'))
  where
    a1' = translateType a1
    a2' = translateType a2
-- A-NAT
subtype Null TyNat TyNat = return (LC.CoRefl (translateType TyNat))

-- Failing cases...
subtype ExtraLabel{} TyNat   TyNat = fail "Subtype error"
subtype ExtraType{}  TyNat   TyNat = fail "Subtype error"
subtype Null         TyTop   TyNat = fail "Subtype error"
subtype ExtraLabel{} TyTop   TyNat = fail "Subtype error"
subtype ExtraType{}  TyTop   TyNat = fail "Subtype error"
subtype Null         TyArr{} TyNat = fail "Subtype error"
subtype ExtraLabel{} TyArr{} TyNat = fail "Subtype error"
subtype ExtraType{}  TyArr{} TyNat = fail "Subtype error"
subtype Null         TyRec{} TyNat = fail "Subtype error"
subtype ExtraLabel{} TyRec{} TyNat = fail "Subtype error"
subtype ExtraType{}  TyRec{} TyNat = fail "Subtype error"
