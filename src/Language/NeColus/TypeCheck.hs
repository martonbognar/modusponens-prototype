{-# OPTIONS_GHC -Wall #-}

module Language.NeColus.TypeCheck where

import qualified Language.LambdaC as LC

import Control.Applicative ((<|>))
import Control.Monad (guard)

import Language.NeColus.Syntax

-- * NeColus Typing
-- ----------------------------------------------------------------------------

-- | For a NeColus type, get the corresponding LambdaC type.
elabType :: Type -> LC.Type
elabType TyNat       = LC.TyNat
elabType TyTop       = LC.TyTop
elabType (TyArr a b) = LC.TyArr (elabType a) (elabType b)
elabType (TyIs a b)  = LC.TyTup (elabType a) (elabType b)
elabType (TyRec l a) = LC.TyRec (convertLabel l) (elabType a)

convertVar :: Variable -> LC.Variable
convertVar (MkVar i) = LC.MkVar i

convertLabel :: Label -> LC.Label
convertLabel (MkLabel l) = LC.MkLabel l

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


-- | Experimental unary disjoint.
uDisjoint :: Type -> Bool
uDisjoint TyTop       = True
uDisjoint TyNat       = True
uDisjoint (TyIs a b ) = disjoint a b && uDisjoint a && uDisjoint b
uDisjoint (TyArr _ b) = uDisjoint b
uDisjoint (TyRec _ t) = uDisjoint t


inference :: Expression -> Maybe (Type, LC.Term)
inference = inferenceWithContext Empty


-- | inferenceWithContext
inferenceWithContext :: Context -> Expression -> Maybe (Type, LC.Term)
-- T-TOP
inferenceWithContext _ ExTop = return (TyTop, LC.TmTop)
-- T-LIT
inferenceWithContext _ (ExLit i) = return (TyNat, LC.TmLit i)
-- T-VAR
inferenceWithContext c (ExVar v)
  = do t <- typeFromContext c v
       return (t, LC.TmVar (convertVar v))
-- T-APP
inferenceWithContext c (ExApp e1 e2)
  = do (TyArr a1 a2, v1) <- inferenceWithContext c e1
       v2 <- checking c e2 a1
       return (a2, LC.TmApp v1 v2)
-- T-ANNO
inferenceWithContext c (ExAnn e a)
  = do v <- checking c e a
       return (a, v)
-- T-PROJ
inferenceWithContext c (ExRecFld e l)
  = do (TyRec l' a, v) <- inferenceWithContext c e
       guard (l' == l)
       return (a, LC.TmRecFld v (convertLabel l))
-- T-MERGE
inferenceWithContext c (ExMerge e1 e2)
  = do (a1, v1) <- inferenceWithContext c e1
       (a2, v2) <- inferenceWithContext c e2
      --  guard (disjoint a1 a2) -- the original NeColus implementation
       guard (uDisjoint (TyIs a1 a2))
       return (TyIs a1 a2, LC.TmTup v1 v2)
-- T-RCD
inferenceWithContext c (ExRec l e)
  = do (a, v) <- inferenceWithContext c e
       return (TyRec l a, LC.TmRecCon (convertLabel l) v)

inferenceWithContext _ ExAbs {} = fail "Inference error"


-- | Checking
checking :: Context -> Expression -> Type -> Maybe LC.Term
-- T-ABS
checking c (ExAbs x e) (TyArr a b)
  = do v <- checking (Snoc c x a) e b
       return (LC.TmAbs (convertVar x) (elabType a) v)
-- T-SUB
checking c e a
  = do (b, v) <- inferenceWithContext c e
       co <- subtype Null b a
       return (LC.TmCast co v)


-- | Meta-top function for coercions.
metaTop :: Queue -> LC.Coercion
metaTop Null = LC.CoAnyTop (elabType TyTop)
metaTop (ExtraLabel q l)
  = LC.CoTrans (LC.CoRec l' (metaTop q)) (LC.CoTopRec l')
    where
      l' = convertLabel l
metaTop (ExtraType q a)
  = LC.CoTrans
      (LC.CoArr (LC.CoAnyTop a') (metaTop q))
      LC.CoTopArr
    where
      a' = elabType a


-- | Convert a queue to a type. (Definition 24)
queueToType :: Queue -> Type -> Type
queueToType Null a = a
queueToType (ExtraType q a) b = queueToType q (TyArr b a)
queueToType (ExtraLabel q l) a = queueToType q (TyRec l a)


-- | Meta-intersection function for coercions.
metaIs :: Queue -> Type -> Type -> LC.Coercion
metaIs Null b1 b2 = LC.CoRefl (elabType (TyIs b1 b2))
metaIs (ExtraLabel q l) b1 b2
  = LC.CoTrans
      (LC.CoRec l' (metaIs q b1 b2))
      (LC.CoDistRec l' arrB1 arrB2)
    where
      l' = convertLabel l
      arrB1 = elabType $ queueToType q b1
      arrB2 = elabType $ queueToType q b2
metaIs (ExtraType q a) b1 b2
  = LC.CoTrans
      (LC.CoArr (LC.CoRefl a') (metaIs q b1 b2))
      (LC.CoDistArr a' arrB1 arrB2)
    where
      a' = elabType a
      arrB1 = elabType $ queueToType q b1
      arrB2 = elabType $ queueToType q b2


-- | Algorithmic subtyping
subtype :: Queue -> Type -> Type -> Maybe LC.Coercion
-- A-AND
subtype q a (TyIs b1 b2)
  = do c1 <- subtype q a b1
       c2 <- subtype q a b2
       return (LC.CoTrans (metaIs q b1 b2) (LC.CoPair c1 c2))
-- A-ARR
subtype q a (TyArr b1 b2)
  = subtype (ExtraType q b1) a b2
-- A-RCD
subtype q a (TyRec l b)
  = subtype (ExtraLabel q l) a b
-- A-TOP
subtype q a TyTop
  = return (LC.CoTrans (metaTop q) (LC.CoAnyTop a')) where
      a' = elabType a
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
       return (LC.CoRec (convertLabel l) c)
-- A-ANDN1 & A-ANDN2
subtype q (TyIs a1 a2) TyNat
  =   do c <- subtype q a1 TyNat
         return (LC.CoTrans c (LC.CoLeft a1' a2'))
  <|> do c <- subtype q a2 TyNat
         return (LC.CoTrans c (LC.CoRight a1' a2'))
  where
    a1' = elabType a1
    a2' = elabType a2
-- A-NAT
subtype Null TyNat TyNat = return (LC.CoRefl (elabType TyNat))

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
