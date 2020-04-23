{-# OPTIONS_GHC -Wall #-}

module Language.NeColus.TypeCheck (inference, checking) where

import qualified Language.LambdaC as Target

import Control.Applicative ((<|>))
import Data.Variable
import Data.Label
import Data.Maybe

import Language.NeColus.Syntax

type TcM a = Either String a

data AlgContext
  = Hole
  | ContextAbs Variable AlgContext
  | ExprApp AlgContext Expression
  | ContextApp Expression AlgContext
  | ContextPair AlgContext Expression
  | ExprPair Expression AlgContext
  | ContextRec Label AlgContext

guardWithMsg :: Bool -> String -> TcM ()
guardWithMsg True  _ = return ()
guardWithMsg False s = Left s

-- * NeColus Typing
-- ----------------------------------------------------------------------------

eqMono :: Monotype -> Monotype -> Bool
eqMono TyNat  TyNat  = True
eqMono TyTop  TyTop  = True

eqTypes :: Type -> Type -> Bool
eqTypes (TyMono m1) (TyMono m2) = eqMono m1 m2
eqTypes (TyArr t1 t2) (TyArr t1' t2') = eqTypes t1 t1' && eqTypes t2 t2'
eqTypes (TyIs t1 t2) (TyIs t1' t2') = eqTypes t1 t1' && eqTypes t2 t2'
eqTypes _ _ = False


elabMono :: Monotype -> Target.Type
elabMono TyNat = Target.TyNat
elabMono TyTop = Target.TyTop


-- | For a NeColus type, get the corresponding LambdaC type.
elabType :: Type -> Target.Type
elabType (TyMono m) = elabMono m
elabType (TyArr a b) = Target.TyArr (elabType a) (elabType b)
elabType (TyIs a b)  = Target.TyTup (elabType a) (elabType b)
-- elabType (TyRec l a) = Target.TyRec l (elabType a)


-- | Get the type of a variable from a context.
typeFromContext :: TypeContext -> Variable -> TcM Type
typeFromContext Empty _ = Left "Variable not in context"
typeFromContext (VarSnoc c v vt) x
  | v == x    = return vt
  | otherwise = typeFromContext c x


wellFormedSubst :: TypeContext -> Substitution -> Bool
wellFormedSubst _ EmptySubst = True
wellFormedSubst (SubstSnoc ctx v1 b) (Cons v2 a sub)
  | v1 == v2  = wellFormedSubst ctx sub && isJust (disjoint ctx a b)
  | otherwise = wellFormedSubst ctx (Cons v2 a sub)
wellFormedSubst (VarSnoc ctx v1 b) (Cons v2 a sub) = wellFormedSubst ctx (Cons v2 a sub)

unify :: TypeContext -> Type -> Type -> Maybe Substitution
unify ctx (TyMono TyNat) (TyMono TyNat) = Just EmptySubst
unify ctx (TyMono TyNat) (TySubstVar v)
  | wellFormedSubst ctx (Cons v (TyMono TyNat) EmptySubst) = Just (Cons v (TyMono TyNat) EmptySubst)
unify ctx (TySubstVar v1) (TyMono (TyVar v2))
  | v1 == v2 && wellFormedSubst ctx (Cons v1 (TyMono (TyVar v1)) EmptySubst) = Just (Cons v1 (TyMono (TyVar v1)) EmptySubst)
unify _ _ _ = Nothing

disjoint :: TypeContext -> Type -> Type -> Maybe Substitution
disjoint ctx (TyMono TyTop)         a
  = Just EmptySubst
disjoint ctx a                      (TyMono TyTop)
  = Just EmptySubst
disjoint ctx (TyMono (TyVar ap))     b
  = case (typeFromContext ctx ap) of
      Left _ -> Nothing
      Right a -> do
        (c, s) <- subRight ctx Null a b
        return s
disjoint ctx a                      (TyMono (TyVar bt))
  = case (typeFromContext ctx bt) of
      Left _ -> Nothing
      Right b -> if eqTypes a b then Just EmptySubst else Nothing
disjoint ctx (TyArr a1 a2) (TyArr b1 b2)
  = disjoint ctx a2 b2
disjoint ctx a                      (TyArr b1 b2)
  = disjoint ctx a b2
disjoint ctx (TyArr a1 a2) b
  = disjoint ctx a2 b
disjoint ctx (TyIs a1 a2)           b
  = do
    s1 <- disjoint ctx a1 b
    s2 <- disjoint ctx a2 b
    return s2
disjoint ctx a                      (TyIs b1 b2)
  = do
    s1 <- disjoint ctx a b1
    s2 <- disjoint ctx a b2
    return s2
disjoint ctx (TyAbs a a1 a2)        (TyAbs b b1 b2)
  = disjoint (VarSnoc ctx a (TyIs a1 b1)) a2 b2
disjoint ctx a                      b
  = undefined

subtyping :: Type -> Type -> Maybe Target.Coercion
subtyping = undefined

subRight :: TypeContext -> Queue -> Type -> Type -> Maybe (Target.Coercion, Substitution)
subRight = undefined

subLeft :: TypeContext -> Queue -> Queue -> Substitution -> Type -> Type -> Maybe (Substitution, AlgContext)
subLeft = undefined


-- | Check whether two types are disjoint.
-- disjoint :: Type -> Type -> Bool
-- disjoint (TyMono TyTop)        _            = True
-- disjoint _            (TyMono TyTop)        = True
-- disjoint (TyArr _ a2) (TyArr _ b2) = disjoint a2 b2
-- disjoint (TyIs a1 a2) b            = disjoint a1 b && disjoint a2 b
-- disjoint a            (TyIs b1 b2) = disjoint a b1 && disjoint a b2
-- -- disjoint (TyRec l1 a) (TyRec l2 b) = (l1 /= l2) || disjoint a b
-- disjoint (TyMono TyNat)        (TyArr _ b2) = disjoint (TyMono TyNat) b2 -- was buggy before
-- disjoint (TyArr _ b2) (TyMono TyNat)        = disjoint b2 (TyMono TyNat) -- was buggy before
-- -- disjoint (TyMono TyNat)        TyRec{}      = True
-- -- disjoint TyRec{}      (TyMono TyNat)        = True
-- -- disjoint TyArr{}      TyRec{}      = True
-- -- disjoint TyRec{}      TyArr{}      = True
-- disjoint (TyMono TyNat)        (TyMono TyNat)        = False


-- | Experimental unary disjoint.
-- uDisjoint :: Type -> Bool
-- uDisjoint (TyMono TyTop)       = True
-- uDisjoint (TyMono TyNat)       = True
-- uDisjoint (TyIs a b ) = disjoint a b && uDisjoint a && uDisjoint b
-- uDisjoint (TyArr _ b) = uDisjoint b
-- -- uDisjoint (TyRec _ t) = uDisjoint t


inference :: Expression -> TcM (Type, Target.Expression)
inference = inferenceWithContext Empty


-- | inferenceWithContext
inferenceWithContext :: TypeContext -> Expression -> TcM (Type, Target.Expression)
-- T-TOP
inferenceWithContext _ ExTop = return ((TyMono TyTop), Target.ExTop)
-- T-LIT
inferenceWithContext _ (ExLit i) = return ((TyMono TyNat), Target.ExLit i)
-- T-VAR
inferenceWithContext c (ExVar v)
  = do t <- typeFromContext c v
       return (t, Target.ExVar v)
-- T-APP
inferenceWithContext c (ExApp e1 e2)
  = do ~(TyArr a1 a2, v1) <- inferenceWithContext c e1
       v2 <- checking c e2 a1
       return (a2, Target.ExApp v1 v2)
-- T-ANNO
inferenceWithContext c (ExAnn e a)
  = do v <- checking c e a
       return (a, v)
-- -- T-PROJ
-- inferenceWithContext c (ExRecFld e l)
--   = do (TyRec l' a, v) <- inferenceWithContext c e
--        guard (l' == l)
--        return (a, Target.TmRecFld v l)
-- T-MERGE
inferenceWithContext c (ExMerge e1 e2)
  = do (a1, v1) <- inferenceWithContext c e1
       (a2, v2) <- inferenceWithContext c e2
      --  guard (disjoint a1 a2) -- the original NeColus implementation
      --  guardWithMsg
      --    (uDisjoint (TyIs a1 a2))
      --    ("Not uDisjoint: " ++ show (TyIs a1 a2))
       return (TyIs a1 a2, Target.ExMerge v1 v2)
-- -- T-RCD
-- inferenceWithContext c (ExRec l e)
--   = do (a, v) <- inferenceWithContext c e
--        return (TyRec l a, Target.TmRecCon l v)
-- failing case
inferenceWithContext _ ExAbs {} = Left "inferenceWithContext: ExAbs"


-- | Checking
checking :: TypeContext -> Expression -> Type -> TcM Target.Expression
-- T-ABS
checking c (ExAbs x e) (TyArr a b)
  = do v <- checking (VarSnoc c x a) e b
       return (Target.ExAbs x (elabType a) v)
-- T-SUB
checking c e a
  = do (b, v) <- inferenceWithContext c e
       co <- subtype b a
       return (Target.ExCoApp co v)

topArrows :: Queue -> Target.Coercion
topArrows Null = Target.CoTop (elabMono TyTop)
topArrows (ExtraType l a) = Target.CoComp (Target.CoArr (Target.CoTop a') (topArrows l)) Target.CoTopArr
  where a' = elabType a


-- | Convert a queue to a type. (Definition 24)
queueToType :: Queue -> Type -> Type
queueToType Null a = a
queueToType (ExtraType q b) a = queueToType q (TyArr b a)
-- queueToType (ExtraLabel q l) a = queueToType q (TyRec l a)


distArrows' :: Queue -> Target.Coercion -> Type -> Type -> Target.Coercion
distArrows' Null k _ _ = k
distArrows' (ExtraType q t) k a b = Target.CoComp (Target.CoArr (Target.CoId t') (distArrows' q k a b)) (Target.CoDistArr t' a' b')
  where t' = elabType t
        a' = elabType $ queueToType q a
        b' = elabType $ queueToType q b

distArrows :: Queue -> Type -> Type -> Target.Coercion
distArrows Null t1 t2 = Target.CoId t'
  where t' = elabType (TyIs t1 t2)
distArrows (ExtraType q t) t1 t2 = Target.CoComp (Target.CoArr (Target.CoId t') (distArrows q t1 t2)) (Target.CoDistArr t' t1' t2')
  where t' = elabType t
        t1' = elabType $ queueToType q t1
        t2' = elabType $ queueToType q t2


data CallStack
  = EmptyStack
  | Add Type Type CallStack


stackContains :: CallStack -> Type -> Type -> Bool
stackContains EmptyStack _ _ = False
stackContains (Add a' t' s) a t = (eqTypes t t' && eqTypes a a') || stackContains s a t


data XEnv
  = XHole
  | XCoArr XEnv Type Type Target.Coercion
  | XProjLeft XEnv Type Type
  | XProjRight XEnv Type Type
  | XModPon Queue Target.Coercion Target.Coercion Type Type


xSem :: XEnv -> Target.Coercion -> Target.Coercion
xSem XHole k                 = k
xSem (XCoArr x _ _ k1) k     = xSem x (Target.CoArr k1 k)
xSem (XProjLeft x a b) k     = xSem x (Target.CoComp k (Target.CoPr1 a' b'))
  where a' = elabType a
        b' = elabType b
xSem (XProjRight x a b) k    = xSem x (Target.CoComp k (Target.CoPr2 a' b'))
  where a' = elabType a
        b' = elabType b


subtype :: Type -> Type -> TcM Target.Coercion
subtype a b = sub1 EmptyStack Null a b


sub1 :: CallStack -> Queue -> Type -> Type -> TcM Target.Coercion
sub1 s l a (TyMono TyNat) = do
  x <- sub2 s l Null a XHole a (TyMono TyNat)
  return (xSem x (Target.CoId (elabType (TyMono TyNat))))
sub1 s l a (TyArr b1 b2) = sub1 s (appendType l b1) a b2
sub1 s l a (TyIs b1 b2) = do
  k1 <- sub1 s l a b1
  k2 <- sub1 s l a b2
  return (Target.CoComp (distArrows l b1 b2) (Target.CoPair k1 k2))
sub1 _ l a (TyMono TyTop) = let a' = elabType a in do
  return (Target.CoComp (topArrows l) (Target.CoTop a'))


sub2 :: CallStack -> Queue -> Queue -> Type -> XEnv -> Type -> Type -> TcM XEnv
sub2 _ Null _ _ x (TyMono TyNat)  (TyMono TyNat)  = return x
sub2 s l m a0 x (TyArr a1 a2) (TyMono TyNat) = case l of
    Null -> sub2ModPon
    (ExtraType l' b1) -> sub2Arr l' b1 <|> sub2ModPon
  where
    sub2Arr l' b1 = do
      k <- sub1 s Null b1 a1
      sub2 s l' (appendType m b1) a0 (XCoArr x b1 a1 k) a2 (TyMono TyNat)

    sub2ModPon = do
      let arr = elabType (TyArr a1 a2)
          t   = (queueToType m a1)
          s'  = Add a0 t s
      guardWithMsg
        (not (stackContains s a0 t))
        ("loop detected: " ++ show a0 ++ " < " ++ show t)
      k1 <- sub1 s' Null a0 t
      sub2 s l m a0 (XModPon m (xSem x (Target.CoId arr)) k1 a1 a2) a2 (TyMono TyNat)

sub2 _ Null             _ _ _ (TyMono TyNat)       (TyMono TyTop)       = Left "sub2 ... Null ... (TyMono TyNat)       TyTop      "
sub2 _ Null             _ _ _ (TyMono TyNat)       (TyArr _ _) = Left "sub2 ... Null ... (TyMono TyNat)       (TyArr _ _)"
sub2 _ Null             _ _ _ (TyMono TyNat)       (TyIs _ _)  = Left "sub2 ... Null ... (TyMono TyNat)       (TyIs _ _) "
sub2 _ (ExtraType _ _)  _ _ _ (TyMono TyNat)       _           = Left "sub2 ... (ExtraType _ _) ... (TyMono TyNat) "

sub2 _ Null             _ _ _ (TyMono TyTop)       _           = Left "sub2 ... Null            ... TyTop"
sub2 _ (ExtraType _ _)  _ _ _ (TyMono TyTop)       _           = Left "sub2 ... (ExtraType _ _) ... TyTop"

sub2 _ Null             _ _ _ (TyArr _ _) (TyMono TyTop)       = Left "sub2 ... (TyArr _ _) TyTop      "
sub2 _ (ExtraType _ _)  _ _ _ (TyArr _ _) (TyMono TyTop)       = Left "sub2 ... (TyArr _ _) TyTop      "
sub2 _ Null             _ _ _ (TyArr _ _) (TyArr _ _) = Left "sub2 ... (TyArr _ _) (TyArr _ _)"
sub2 _ (ExtraType _ _)  _ _ _ (TyArr _ _) (TyArr _ _) = Left "sub2 ... (TyArr _ _) (TyArr _ _)"
sub2 _ Null             _ _ _ (TyArr _ _) (TyIs _ _)  = Left "sub2 ... (TyArr _ _) (TyIs _ _) "
sub2 _ (ExtraType _ _)  _ _ _ (TyArr _ _) (TyIs _ _)  = Left "sub2 ... (TyArr _ _) (TyIs _ _) "

sub2 _ Null             _ _ _ (TyIs _ _)  (TyMono TyTop)       = Left "sub2 ... (TyIs _ _)  TyTop      "
sub2 _ (ExtraType _ _)  _ _ _ (TyIs _ _)  (TyMono TyTop)       = Left "sub2 ... (TyIs _ _)  TyTop      "
sub2 _ Null             _ _ _ (TyIs _ _)  (TyArr _ _) = Left "sub2 ... (TyIs _ _)  (TyArr _ _)"
sub2 _ (ExtraType _ _)  _ _ _ (TyIs _ _)  (TyArr _ _) = Left "sub2 ... (TyIs _ _)  (TyArr _ _)"
sub2 _ Null             _ _ _ (TyIs _ _)  (TyIs _ _)  = Left "sub2 ... (TyIs _ _)  (TyIs _ _) "
sub2 _ (ExtraType _ _)  _ _ _ (TyIs _ _)  (TyIs _ _)  = Left "sub2 ... (TyIs _ _)  (TyIs _ _) "

