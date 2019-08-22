{-# OPTIONS_GHC -Wall #-}

module NeColus where

import qualified LambdaC as LC

import Text.PrettyPrint
import PrettyPrinter

type Variable = String
type Label    = String

-- * Main NeColus types
-- ----------------------------------------------------------------------------

data Type
  = TyNat
  | TyTop
  | TyArr Type Type
  | TyIs Type Type
  | TyRec Label Type

data Expression
  = ExVar Variable
  | ExLit Int
  | ExTop
  | ExAbs Variable Expression
  | ExApp Expression Expression
  | ExMerge Expression Expression
  | ExAnn Expression Type
  | ExRec Label Expression
  | ExRecFld Expression Label

data Context
  = Empty
  | Snoc Context Variable Type


-- | Determine equality between two types.
eqTypes :: Type -> Type -> Bool
eqTypes TyNat TyNat                 = True
eqTypes TyTop TyTop                 = True
eqTypes (TyArr t1 t2) (TyArr t3 t4) = eqTypes t1 t3 && eqTypes t2 t4
eqTypes (TyIs t1 t2) (TyIs t3 t4)   = eqTypes t1 t3 && eqTypes t2 t4
eqTypes (TyRec l1 t1) (TyRec l2 t2) = eqTypes t1 t2 && l1 == l2
eqTypes _ _                         = False

-- * Pretty Printing
-- ----------------------------------------------------------------------------

instance PrettyPrint Type where
  ppr TyNat         = ppr "Nat"
  ppr TyTop         = ppr "Unit"
  ppr (TyArr t1 t2) = hsep [ppr t1, arrow, ppr t2]
  ppr (TyIs t1 t2)  = hsep [ppr t1, ppr "&", ppr t2]
  ppr (TyRec l t)   = braces $ hsep [ppr l, colon, ppr t]

instance PrettyPrint Expression where
  ppr (ExVar v)       = ppr v
  ppr (ExLit i)       = ppr i
  ppr ExTop           = parens empty
  ppr (ExAbs v e)     = hcat [ppr "\\", ppr v, dot, ppr e]
  ppr (ExApp e1 e2)   = ppr e1 <+> ppr e2
  ppr (ExMerge e1 e2) = hsep [ppr e1, comma, comma, ppr e2]
  ppr (ExAnn e t)     = hsep [ppr e, colon, ppr t]
  ppr (ExRec l e)     = braces $ hsep [ppr l, equals, ppr e]
  ppr (ExRecFld e l)  = hcat [ppr e, dot, ppr l]

instance PrettyPrint Context where
  ppr Empty        = ppr "•"
  ppr (Snoc c v t) = hcat [ppr c, comma, ppr v, colon, ppr t]

instance Show Type where
  show = render . ppr

instance Show Expression where
  show = render . ppr

instance Show Context where
  show = render . ppr


translateType :: Type -> LC.Type
translateType TyNat       = LC.TyNat
translateType TyTop       = LC.TyTop
translateType (TyArr a b) = LC.TyArr (translateType a) (translateType b)
translateType (TyIs a b)  = LC.TyTup (translateType a) (translateType b)
translateType (TyRec l a) = LC.TyRec l (translateType a)


-- | Get the type of a variable from a context.
typeFromContext :: Context -> Variable -> Maybe Type
typeFromContext Empty _ = Nothing
typeFromContext (Snoc c v vt) x
  | v == x    = Just vt
  | otherwise = typeFromContext c x


disjoint :: Type -> Type -> Bool
-- D-TOPL
disjoint TyTop _ = True
-- D-TOPR
disjoint _ TyTop = True
-- D-ARR
disjoint (TyArr _ a2) (TyArr _ b2)
  | disjoint a2 b2 = True
-- D-ANDL
disjoint (TyIs a1 a2) b
  | disjoint a1 b
  , disjoint a2 b
  = True
-- D-ANDR
disjoint a (TyIs b1 b2)
  | disjoint a b1
  , disjoint a b2
  = True
-- D-RCDEQ
disjoint (TyRec l1 a) (TyRec l2 b)
  | l1 == l2
  , disjoint a b
  = True
-- D-RCDNEQ
disjoint (TyRec l1 _) (TyRec l2 _)
  | l1 /= l2 = True
-- D-AXNATARR
disjoint TyNat (TyArr _ _) = True
-- D-AXARRNAT
disjoint (TyArr _ _) TyNat = True
-- D-AXNATRCD
disjoint TyNat (TyRec _ _) = True
-- D-AXRCDNAT
disjoint (TyRec _ _) TyNat = True
-- D-AXARRRCD
disjoint (TyArr _ _) (TyRec _ _) = True
-- D-AXRCDARR
disjoint (TyRec _ _) (TyArr _ _) = True

disjoint _ _ = False


-- | Inference
inference :: Context -> Expression -> Maybe (Type, LC.Term)
-- T-TOP
inference _ ExTop = Just (TyTop, LC.TmTop)
-- T-LIT
inference _ (ExLit i) = Just (TyNat, LC.TmLit i)
-- T-VAR
inference c (ExVar v)
  | Just t <- typeFromContext c v
  = Just (t, LC.TmVar v)
-- T-APP
inference c (ExApp e1 e2)
  | Just (TyArr a1 a2, v1) <- inference c e1
  , Just v2 <- checking c e2 a1
  = Just (a2, LC.TmApp v1 v2)
-- T-ANNO
inference c (ExAnn e a)
  | Just v <- checking c e a
  = Just (a, v)
-- T-PROJ
inference c (ExRecFld e l)
  | Just (TyRec l' a, v) <- inference c e
  , l' == l
  = Just (a, LC.TmRecFld v l)
-- T-MERGE
inference c (ExMerge e1 e2)
  | Just (a1, v1) <- inference c e1
  , Just (a2, v2) <- inference c e2
  , disjoint a1 a2
  = Just (TyIs a1 a2, LC.TmTup v1 v2)
-- T-RCD
inference c (ExRec l e)
  | Just (a, v) <- inference c e
  = Just (TyRec l a, LC.TmRecCon l v)

inference _ _ = Nothing


-- | Checking
checking :: Context -> Expression -> Type -> Maybe LC.Term
-- T-ABS
checking c (ExAbs x e) (TyArr a b)
  | Just v <- checking (Snoc c x a) e b
  = Just (LC.TmAbs x (translateType a) v)
-- T-SUB
checking c e a
  | Just (b, v) <- inference c e
  , Just co <- subtype Null b a
  = Just (LC.TmCast co v)

checking _ _ _ = Nothing


data Queue
  = Null
  | ExtraLabel Queue Label
  | ExtraType Queue Type

isNullQueue :: Queue -> Bool
isNullQueue Null = True
isNullQueue _    = False
{-# INLINE isNullQueue #-}

viewL :: Queue -> Maybe (Either Label Type, Queue)
viewL Null = Nothing
viewL (ExtraLabel q l)
  | isNullQueue q = return (Left l, Null)
  | otherwise     = do (res, queue) <- viewL q
                       return (res, ExtraLabel queue l)
viewL (ExtraType q t)
  | isNullQueue q = return (Right t, Null)
  | otherwise     = do (res, queue) <- viewL q
                       return (res, ExtraType queue t)


metaTop :: Queue -> LC.Coercion
metaTop Null = LC.CoAnyTop (translateType TyTop)
metaTop (ExtraLabel q l)
  = LC.CoTrans (LC.CoRec l (metaTop q)) (LC.CoTopRec l)
metaTop (ExtraType q a)
  = LC.CoTrans
      (LC.CoArr (LC.CoAnyTop (translateType a)) (metaTop q))
      (LC.CoTrans LC.CoTopArr (LC.CoAnyTop (translateType a)))

metaIs :: Queue -> LC.Coercion
metaIs Null = LC.CoRefl (translateType TyTop)
metaIs (ExtraLabel q l)
  = LC.CoTrans (LC.CoRec l (metaIs q)) (LC.CoDistRec l (translateType TyTop) (translateType TyTop))
metaIs (ExtraType q a)
  = LC.CoTrans
      (LC.CoArr (LC.CoRefl (translateType a)) (metaIs q))
      (LC.CoDistArr (translateType a) (translateType a) (translateType a))

-- | Algorithmic subtyping
subtype :: Queue -> Type -> Type -> Maybe LC.Coercion
-- A-AND
subtype q a (TyIs b1 b2)
  | Just c1 <- subtype q a b1
  , Just c2 <- subtype q a b2
  = Just (LC.CoTrans (metaIs q) (LC.CoPair c1 c2))
-- A-ARR
subtype q a (TyArr b1 b2)
  | Just c <- subtype (ExtraType q b1) a b2 = Just c
-- A-RCD
subtype q a (TyRec l b)
  | Just c <- subtype (ExtraLabel q l) a b = Just c
-- A-TOP
subtype q a TyTop = Just (LC.CoTrans (metaTop q) (LC.CoAnyTop (translateType a)))
-- A-ARRNAT
subtype queue (TyArr a1 a2) TyNat
  | Just (Right a, q) <- viewL queue
  = do c1 <- subtype Null a a1
       c2 <- subtype q a2 TyNat
       return (LC.CoArr c1 c2)
-- A-RCDNAT
subtype (ExtraLabel q l) (TyRec l' a) TyNat
  | l == l'
  , Just c <- subtype q a TyNat
  = Just (LC.CoRec l c)
-- A-ANDN1
subtype q (TyIs a1 a2) TyNat
  | Just c <- subtype q a1 TyNat
  = Just (LC.CoTrans c (LC.CoLeft (translateType a1) (translateType a2)))
-- A-ANDN2
subtype q (TyIs a1 a2) TyNat
  = do c <- subtype q a2 TyNat
       let a1' = translateType a1
           a2' = translateType a2
       return $ LC.CoTrans c (LC.CoRight a1' a2')
-- A-NAT
subtype Null TyNat TyNat = Just (LC.CoRefl (translateType TyNat))

subtype _ _ _ = Nothing
