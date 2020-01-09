-- {-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.NeColus.TypeCheck (inference, checking) where

import qualified Language.LambdaC as LC

import Control.Applicative ((<|>))
import Data.Variable
import Control.Monad.Fail

import Language.NeColus.Syntax

type TcM a = Either String a

instance MonadFail (Either String) where
  fail = Left

guardWithMsg :: Bool -> String -> TcM ()
guardWithMsg True  _ = return ()
guardWithMsg False s = Left s

-- * NeColus Typing
-- ----------------------------------------------------------------------------

-- | For a NeColus type, get the corresponding LambdaC type.
elabType :: Type -> LC.Type
elabType TyNat       = LC.TyNat
elabType TyBool      = LC.TyBool
elabType TyTop       = LC.TyTop
elabType (TyArr a b) = LC.TyArr (elabType a) (elabType b)
elabType (TyIs a b)  = LC.TyTup (elabType a) (elabType b)
-- elabType (TyRec l a) = LC.TyRec l (elabType a)


-- | Get the type of a variable from a context.
typeFromContext :: Context -> Variable -> TcM Type
typeFromContext Empty _ = Left "Variable not in context"
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
-- disjoint (TyRec l1 a) (TyRec l2 b) = (l1 /= l2) || disjoint a b
disjoint TyNat        (TyArr _ b2) = disjoint TyNat b2 -- was buggy before
disjoint (TyArr _ b2) TyNat        = disjoint b2 TyNat -- was buggy before
-- disjoint TyNat        TyRec{}      = True
-- disjoint TyRec{}      TyNat        = True
-- disjoint TyArr{}      TyRec{}      = True
-- disjoint TyRec{}      TyArr{}      = True
disjoint TyNat        TyNat        = False
disjoint TyBool       TyBool       = False
disjoint TyNat        TyBool       = True
disjoint TyBool       TyNat        = True
disjoint TyBool       (TyArr _ b2) = disjoint TyBool b2
disjoint (TyArr _ b2) TyBool       = disjoint b2 TyBool


-- | Experimental unary disjoint.
uDisjoint :: Type -> Bool
uDisjoint TyTop       = True
uDisjoint TyNat       = True
uDisjoint TyBool      = True
uDisjoint (TyIs a b ) = disjoint a b && uDisjoint a && uDisjoint b
uDisjoint (TyArr _ b) = uDisjoint b
-- uDisjoint (TyRec _ t) = uDisjoint t


inference :: Expression -> TcM (Type, LC.Term)
inference = inferenceWithContext Empty


-- | inferenceWithContext
inferenceWithContext :: Context -> Expression -> TcM (Type, LC.Term)
-- T-TOP
inferenceWithContext _ ExTop = return (TyTop, LC.TmTop)
-- T-LIT
inferenceWithContext _ (ExLit i) = return (TyNat, LC.TmLit i)
-- T-BOOL
inferenceWithContext _ (ExBool b) = return (TyBool, LC.TmBool b)
-- T-VAR
inferenceWithContext c (ExVar v)
  = do t <- typeFromContext c v
       return (t, LC.TmVar v)
-- T-APP
inferenceWithContext c (ExApp e1 e2)
  = do (TyArr a1 a2, v1) <- inferenceWithContext c e1
       v2 <- checking c e2 a1
       return (a2, LC.TmApp v1 v2)
-- T-ANNO
inferenceWithContext c (ExAnn e a)
  = do v <- checking c e a
       return (a, v)
-- -- T-PROJ
-- inferenceWithContext c (ExRecFld e l)
--   = do (TyRec l' a, v) <- inferenceWithContext c e
--        guard (l' == l)
--        return (a, LC.TmRecFld v l)
-- T-MERGE
inferenceWithContext c (ExMerge e1 e2)
  = do (a1, v1) <- inferenceWithContext c e1
       (a2, v2) <- inferenceWithContext c e2
      --  guard (disjoint a1 a2) -- the original NeColus implementation
       guardWithMsg
         (uDisjoint (TyIs a1 a2))
         ("Not uDisjoint: " ++ show (TyIs a1 a2))
       return (TyIs a1 a2, LC.TmTup v1 v2)
-- -- T-RCD
-- inferenceWithContext c (ExRec l e)
--   = do (a, v) <- inferenceWithContext c e
--        return (TyRec l a, LC.TmRecCon l v)
-- failing case
inferenceWithContext _ ExAbs {} = Left "inferenceWithContext: ExAbs"


-- | Checking
checking :: Context -> Expression -> Type -> TcM LC.Term
-- T-ABS
checking c (ExAbs x e) (TyArr a b)
  = do v <- checking (Snoc c x a) e b
       return (LC.TmAbs x (elabType a) v)
-- T-SUB
checking c e a
  = do (b, v) <- inferenceWithContext c e
       co <- subtype b a
       return (LC.TmCast co v)

topArrows :: Queue -> LC.Coercion
topArrows Null = LC.CoAnyTop (elabType TyTop)
topArrows (ExtraType l a) = LC.CoTrans (LC.CoArr (LC.CoAnyTop a') (topArrows l)) LC.CoTopArr
  where a' = elabType a


-- | Convert a queue to a type. (Definition 24)
queueToType :: Queue -> Type -> Type
queueToType Null a = a
queueToType (ExtraType q b) a = queueToType q (TyArr b a)
-- queueToType (ExtraLabel q l) a = queueToType q (TyRec l a)


distArrows' :: Queue -> LC.Coercion -> Type -> Type -> LC.Coercion
distArrows' Null k _ _ = k
distArrows' (ExtraType q t) k a b = LC.CoTrans (LC.CoArr (LC.CoRefl t') (distArrows' q k a b)) (LC.CoDistArr t' a' b')
  where t' = elabType t
        a' = elabType $ queueToType q a
        b' = elabType $ queueToType q b

distArrows :: Queue -> Type -> Type -> LC.Coercion
distArrows Null t1 t2 = LC.CoRefl t'
  where t' = elabType (TyIs t1 t2)
distArrows (ExtraType q t) t1 t2 = LC.CoTrans (LC.CoArr (LC.CoRefl t') (distArrows q t1 t2)) (LC.CoDistArr t' t1' t2')
  where t' = elabType t
        t1' = elabType $ queueToType q t1
        t2' = elabType $ queueToType q t2

eqTypes :: Type -> Type -> Bool
eqTypes TyNat  TyNat  = True
eqTypes TyBool TyBool = True
eqTypes TyTop  TyTop  = True
eqTypes (TyArr t1 t2) (TyArr t1' t2') = eqTypes t1 t1' && eqTypes t2 t2'
eqTypes (TyIs t1 t2) (TyIs t1' t2') = eqTypes t1 t1' && eqTypes t2 t2'
eqTypes _ _ = False


data CallStack
  = EmptyStack
  | Add Type Type CallStack


stackContains :: CallStack -> Type -> Type -> Bool
stackContains EmptyStack _ _ = False
stackContains (Add a' t' s) a t = (eqTypes t t' && eqTypes a a') || stackContains s a t


data XEnv
  = XHole
  | XCoArr XEnv Type Type LC.Coercion
  | XProjLeft XEnv Type Type
  | XProjRight XEnv Type Type
  | XModPon Queue LC.Coercion LC.Coercion Type Type


xSem :: XEnv -> LC.Coercion -> LC.Coercion
xSem XHole k                 = k
xSem (XCoArr x _ _ k1) k     = xSem x (LC.CoArr k1 k)
xSem (XProjLeft x a b) k     = xSem x (LC.CoTrans k (LC.CoLeft a' b'))
  where a' = elabType a
        b' = elabType b
xSem (XProjRight x a b) k    = xSem x (LC.CoTrans k (LC.CoRight a' b'))
  where a' = elabType a
        b' = elabType b
xSem (XModPon m k1 k2 a b) k = LC.CoTrans (distArrows' m (LC.CoTrans k (LC.CoMP (LC.CoLeft arr a') (LC.CoRight arr a'))) a b) (LC.CoPair k1 k2)
  where a' = elabType a
        arr = elabType (TyArr a b)


subtype :: Type -> Type -> TcM LC.Coercion
subtype a b = sub1 EmptyStack Null a b


sub1 :: CallStack -> Queue -> Type -> Type -> TcM LC.Coercion
sub1 s l a TyNat = do
  x <- sub2 s l Null a XHole a TyNat
  return (xSem x (LC.CoRefl (elabType TyNat)))
sub1 s l a TyBool = do
  x <- sub2 s l Null a XHole a TyBool
  return (xSem x (LC.CoRefl (elabType TyBool)))
sub1 s l a (TyArr b1 b2) = sub1 s (appendType l b1) a b2
sub1 s l a (TyIs b1 b2) = do
  k1 <- sub1 s l a b1
  k2 <- sub1 s l a b2
  return (LC.CoTrans (distArrows l b1 b2) (LC.CoPair k1 k2))
sub1 _ l a TyTop = let a' = elabType a in do
  return (LC.CoTrans (topArrows l) (LC.CoAnyTop a'))


sub2 :: CallStack -> Queue -> Queue -> Type -> XEnv -> Type -> Type -> TcM XEnv
sub2 _ Null _ _ x TyNat  TyNat  = return x
sub2 _ Null _ _ x TyBool TyBool = return x
sub2 s l m a0 x (TyArr a1 a2) TyNat = case l of
    Null -> sub2ModPon
    (ExtraType l' b1) -> sub2Arr l' b1 <|> sub2ModPon
  where
    sub2Arr l' b1 = do
      k <- sub1 s Null b1 a1
      sub2 s l' (appendType m b1) a0 (XCoArr x b1 a1 k) a2 TyNat

    sub2ModPon = do
      let arr = elabType (TyArr a1 a2)
          t   = (queueToType m a1)
          s'  = Add a0 t s
      guardWithMsg
        (not (stackContains s a0 t))
        ("loop detected: " ++ show a0 ++ " < " ++ show t)
      k1 <- sub1 s' Null a0 t
      sub2 s l m a0 (XModPon m (xSem x (LC.CoRefl arr)) k1 a1 a2) a2 TyNat

sub2 s l m a0 x (TyArr a1 a2) TyBool = case l of
    Null -> sub2ModPon
    (ExtraType l' b1) -> sub2Arr l' b1 <|> sub2ModPon
  where
    sub2Arr l' b1 = do
      k <- sub1 s Null b1 a1
      sub2 s l' (appendType m b1) a0 (XCoArr x b1 a1 k) a2 TyBool

    sub2ModPon = do
      let arr = elabType (TyArr a1 a2)
          t   = queueToType m a1
      guardWithMsg
        (not (stackContains s a0 t))
        ("loop detected: " ++ show a0 ++ " < " ++ show t)

      k1 <- sub1 (Add a0 t s) Null a0 t
      sub2 s l m a0 (XModPon m (xSem x (LC.CoRefl arr)) k1 a1 a2) a2 TyBool

sub2 s l m a0 x (TyIs a1 a2) TyNat
   =  sub2 s l m a0 (XProjLeft  x a1 a2) a1 TyNat
  <|> sub2 s l m a0 (XProjRight x a1 a2) a2 TyNat
sub2 s l m a0 x (TyIs a1 a2) TyBool
   =  sub2 s l m a0 (XProjLeft  x a1 a2) a1 TyBool
  <|> sub2 s l m a0 (XProjRight x a1 a2) a2 TyBool

sub2 _ Null             _ _ _ TyNat       TyTop       = Left "sub2 ... Null ... TyNat       TyTop      "
sub2 _ Null             _ _ _ TyNat       TyBool      = Left "sub2 ... Null ... TyNat       TyBool     "
sub2 _ Null             _ _ _ TyNat       (TyArr _ _) = Left "sub2 ... Null ... TyNat       (TyArr _ _)"
sub2 _ Null             _ _ _ TyNat       (TyIs _ _)  = Left "sub2 ... Null ... TyNat       (TyIs _ _) "

sub2 _ Null             _ _ _ TyBool      TyTop       = Left "sub2 ... Null ... TyBool      TyTop      "
sub2 _ Null             _ _ _ TyBool      TyNat       = Left "sub2 ... Null ... TyBool      TyNat      "
sub2 _ Null             _ _ _ TyBool      (TyArr _ _) = Left "sub2 ... Null ... TyBool      (TyArr _ _)"
sub2 _ Null             _ _ _ TyBool      (TyIs _ _)  = Left "sub2 ... Null ... TyBool      (TyIs _ _) "

sub2 _ (ExtraType _ _)  _ _ _ TyBool      _           = Left "sub2 ... (ExtraType _ _) ... TyBool"
sub2 _ (ExtraType _ _)  _ _ _ TyNat       _           = Left "sub2 ... (ExtraType _ _) ... TyNat "

sub2 _ Null             _ _ _ TyTop       _           = Left "sub2 ... Null            ... TyTop"
sub2 _ (ExtraType _ _)  _ _ _ TyTop       _           = Left "sub2 ... (ExtraType _ _) ... TyTop"

sub2 _ Null             _ _ _ (TyArr _ _) TyTop       = Left "sub2 ... (TyArr _ _) TyTop      "
sub2 _ (ExtraType _ _)  _ _ _ (TyArr _ _) TyTop       = Left "sub2 ... (TyArr _ _) TyTop      "
sub2 _ Null             _ _ _ (TyArr _ _) (TyArr _ _) = Left "sub2 ... (TyArr _ _) (TyArr _ _)"
sub2 _ (ExtraType _ _)  _ _ _ (TyArr _ _) (TyArr _ _) = Left "sub2 ... (TyArr _ _) (TyArr _ _)"
sub2 _ Null             _ _ _ (TyArr _ _) (TyIs _ _)  = Left "sub2 ... (TyArr _ _) (TyIs _ _) "
sub2 _ (ExtraType _ _)  _ _ _ (TyArr _ _) (TyIs _ _)  = Left "sub2 ... (TyArr _ _) (TyIs _ _) "

sub2 _ Null             _ _ _ (TyIs _ _)  TyTop       = Left "sub2 ... (TyIs _ _)  TyTop      "
sub2 _ (ExtraType _ _)  _ _ _ (TyIs _ _)  TyTop       = Left "sub2 ... (TyIs _ _)  TyTop      "
sub2 _ Null             _ _ _ (TyIs _ _)  (TyArr _ _) = Left "sub2 ... (TyIs _ _)  (TyArr _ _)"
sub2 _ (ExtraType _ _)  _ _ _ (TyIs _ _)  (TyArr _ _) = Left "sub2 ... (TyIs _ _)  (TyArr _ _)"
sub2 _ Null             _ _ _ (TyIs _ _)  (TyIs _ _)  = Left "sub2 ... (TyIs _ _)  (TyIs _ _) "
sub2 _ (ExtraType _ _)  _ _ _ (TyIs _ _)  (TyIs _ _)  = Left "sub2 ... (TyIs _ _)  (TyIs _ _) "

