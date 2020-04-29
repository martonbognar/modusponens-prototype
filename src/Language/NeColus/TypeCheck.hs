{-# OPTIONS_GHC -Wall #-}

module Language.NeColus.TypeCheck (inference, checking) where

import qualified Language.LambdaC as Target

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Variable
import Data.Label
import Data.Maybe

import Language.NeColus.Syntax

type TcM a = Either String a

-- * New code from here
-- ----------------------------------------------------------------------------

data AlgContext
  = Hole
  | ContextAbs Variable AlgContext
  | ExprApp AlgContext Expression
  | ContextApp Expression AlgContext
  | ContextPair AlgContext Expression
  | ExprPair Expression AlgContext
  | ContextRec Label AlgContext
  | ContextAll Variable Type AlgContext
  | ContextType AlgContext Target.Type

data BaseType
  = BaseNat
  | BaseTop
  | BaseVar Variable
  | BaseSubstVar Variable


typeToBase :: Type -> Maybe BaseType
typeToBase (TyMono (TyNat)) = Just BaseNat
typeToBase (TyMono (TyTop)) = Just BaseTop
typeToBase (TyMono (TyVar v)) = Just (BaseVar v)
typeToBase (TySubstVar v) = Just (BaseSubstVar v)
typeToBase _ = Nothing

baseToType :: BaseType -> Type
baseToType BaseNat = TyMono TyNat
baseToType BaseTop = TyMono TyTop
baseToType (BaseVar v) = TyMono (TyVar v)
baseToType (BaseSubstVar v) = TySubstVar v


-- | For a NeColus type, get the corresponding LambdaC type.
elabType :: Type -> Target.Type
elabType (TyMono m) = elabMono m
elabType (TyArr a b) = Target.TyArr (elabType a) (elabType b)
elabType (TyIs a b)  = Target.TyTup (elabType a) (elabType b)
-- elabType (TyRec l a) = Target.TyRec l (elabType a)

elabMono :: Monotype -> Target.Type
elabMono TyNat = Target.TyNat
elabMono TyTop = Target.TyTop


appendSubst :: Substitution -> Substitution -> Substitution
appendSubst s1 s2 = undefined


-- TODO: apply substitutions recursively
substType :: Substitution -> Type -> Type
substType EmptySubst t                       = t

substType sub@(SVar ap t s) (TyMono TyNat)   = TyMono TyNat
substType sub@(SVar ap t s) (TyMono TyTop)   = TyMono TyTop
substType sub@(SVar ap t s) (TyMono (TyVar v))
  | ap == v = t
  | otherwise = (TyMono (TyVar v))
substType sub@(SVar ap t s) (TySubstVar ap') = TySubstVar ap'
substType sub@(SVar ap t s) (TyArr a b)      = TyArr (substType sub a) (substType sub b)
substType sub@(SVar ap t s) (TyIs a b)       = TyIs (substType sub a) (substType sub b)
substType sub@(SVar ap t s) (TyAbs ap' a b)  = TyAbs ap' (substType sub a) (substType sub b)
substType sub@(SVar ap t s) (TyRec l a)      = TyRec l (substType sub a)

substType sub@(SSub ap t s) (TyMono TyNat)   = TyMono TyNat
substType sub@(SSub ap t s) (TyMono TyTop)   = TyMono TyTop
substType sub@(SSub ap t s) (TyMono (TyVar v)) = TyMono (TyVar v)
substType sub@(SSub ap t s) (TySubstVar ap')
  | ap == ap' = t
  | otherwise = TySubstVar ap'
substType sub@(SSub ap t s) (TyArr a b)      = TyArr (substType sub a) (substType sub b)
substType sub@(SSub ap t s) (TyIs a b)       = TyIs (substType sub a) (substType sub b)
substType sub@(SSub ap t s) (TyAbs ap' a b)  = TyAbs ap' (substType sub a) (substType sub b)
substType sub@(SSub ap t s) (TyRec l a)      = TyRec l (substType sub a)


substExpr :: Substitution -> Expression -> Expression
substExpr EmptySubst e = e

substExpr sub@(SVar ap t s) (ExLit i)         = ExLit i
substExpr sub@(SVar ap t s) (ExTop)           = ExTop
substExpr sub@(SVar ap t s) (ExTrue)          = ExTrue
substExpr sub@(SVar ap t s) (ExFalse)         = ExFalse
substExpr sub@(SVar ap t s) (ExVar x)         = ExVar x
substExpr sub@(SVar ap t s) (ExAbs x e)       = ExAbs x (substExpr sub e)
substExpr sub@(SVar ap t s) (ExApp e1 e2)     = ExApp (substExpr sub e1) (substExpr sub e2)
substExpr sub@(SVar ap t s) (ExMerge e1 e2)   = ExMerge (substExpr sub e1) (substExpr sub e2)
substExpr sub@(SVar ap t s) (ExAnn e a)       = ExAnn (substExpr sub e) (substType sub a)
substExpr sub@(SVar ap t s) (ExTyAbs ap' a e) = ExTyAbs ap' (substType sub a) (substExpr sub e)
substExpr sub@(SVar ap t s) (ExTyApp e a)     = ExTyApp (substExpr sub e) (substType sub a)
substExpr sub@(SVar ap t s) (ExRec l e)       = ExRec l (substExpr sub e)
substExpr sub@(SVar ap t s) (ExRecFld e l)    = ExRecFld (substExpr sub e) l

substExpr sub@(SSub ap t s) (ExLit i)         = ExLit i
substExpr sub@(SSub ap t s) (ExTop)           = ExTop
substExpr sub@(SSub ap t s) (ExTrue)          = ExTrue
substExpr sub@(SSub ap t s) (ExFalse)         = ExFalse
substExpr sub@(SSub ap t s) (ExVar x)         = ExVar x
substExpr sub@(SSub ap t s) (ExAbs x e)       = ExAbs x (substExpr sub e)
substExpr sub@(SSub ap t s) (ExApp e1 e2)     = ExApp (substExpr sub e1) (substExpr sub e2)
substExpr sub@(SSub ap t s) (ExMerge e1 e2)   = ExMerge (substExpr sub e1) (substExpr sub e2)
substExpr sub@(SSub ap t s) (ExAnn e a)       = ExAnn (substExpr sub e) (substType sub a)
substExpr sub@(SSub ap t s) (ExTyAbs ap' a e) = ExTyAbs ap' (substType sub a) (substExpr sub e)
substExpr sub@(SSub ap t s) (ExTyApp e a)     = ExTyApp (substExpr sub e) (substType sub a)
substExpr sub@(SSub ap t s) (ExRec l e)       = ExRec l (substExpr sub e)
substExpr sub@(SSub ap t s) (ExRecFld e l)    = ExRecFld (substExpr sub e) l


substContext :: Substitution -> TypeContext -> TypeContext
substContext EmptySubst c = c

substContext sub@(SVar ap t s) Empty                 = Empty
substContext sub@(SVar ap t s) (VarSnoc ctx ap' a)
  | ap == ap' = substContext sub ctx
  | otherwise = (VarSnoc (substContext sub ctx) ap' (substType sub a))
substContext sub@(SVar ap t s) (SubstSnoc ctx ap' a) = (VarSnoc (substContext sub ctx) ap' (substType sub a))

substContext sub@(SSub ap t s) Empty                 = Empty
substContext sub@(SSub ap t s) (VarSnoc ctx ap' a)   = (VarSnoc (substContext sub ctx) ap' (substType sub a))
substContext sub@(SSub ap t s) (SubstSnoc ctx ap' a)
  | ap == ap' = substContext sub ctx
  | otherwise = (VarSnoc (substContext sub ctx) ap' (substType sub a))


substQueue :: Substitution -> Queue -> Queue
substQueue EmptySubst q = q

substQueue sub@(SVar ap t s) Null = Null
substQueue sub@(SVar ap t s) (ExtraType m a) = ExtraType (substQueue sub m) (substType sub a)

substQueue sub@(SSub ap t s) Null = Null
substQueue sub@(SSub ap t s) (ExtraType m a) = ExtraType (substQueue sub m) (substType sub a)


wellFormedSubst :: TypeContext -> Substitution -> Maybe Substitution
-- WFS-nil
wellFormedSubst _ EmptySubst = Just EmptySubst
-- ?
wellFormedSubst (VarSnoc ctx ap b) (SVar ap' a sub)
  | ap == ap'  = wellFormedSubst ctx (SVar ap' a sub)
wellFormedSubst (SubstSnoc ctx ap b) (SVar ap' a sub)
-- WFS-next
  | ap == ap' = do
    s1 <- wellFormedSubst ctx sub
    ds <- disjoint ctx a b
    let s2 = appendSubst s1 (appendSubst sub ds)
      in return $ appendSubst s1 s2
  | otherwise = wellFormedSubst ctx (SVar ap' a sub)


unify :: TypeContext -> BaseType -> BaseType -> Maybe Substitution
-- U-refl
unify ctx BaseNat BaseNat = Just EmptySubst
unify ctx BaseTop BaseTop = Just EmptySubst
unify ctx (BaseVar a) (BaseVar b)
  | a == b = Just EmptySubst
unify ctx (BaseSubstVar a) (BaseSubstVar b)
  | a == b = Just EmptySubst
-- U-NatV
unify ctx BaseNat (BaseSubstVar ap) = let nat = baseToType BaseNat in do
  sub <- wellFormedSubst ctx (SVar ap nat EmptySubst)
  return $ (SVar ap nat sub)
-- U-VNat
unify ctx (BaseSubstVar ap) BaseNat = let nat = baseToType BaseNat in do
  sub <- wellFormedSubst ctx (SVar ap nat EmptySubst)
  return $ (SVar ap nat sub)
-- U-VC
unify ctx (BaseSubstVar ap) (BaseVar ap')
  | ap == ap' = let var = baseToType (BaseVar ap') in do
    sub <- wellFormedSubst ctx (SVar ap var EmptySubst)
    return $ (SVar ap var sub)
-- U-CV
unify ctx (BaseVar ap) (BaseSubstVar ap')
  | ap == ap' = let var = baseToType (BaseVar ap) in do
    sub <- wellFormedSubst ctx (SVar ap var EmptySubst)
    return $ (SVar ap var sub)


disjoint :: TypeContext -> Type -> Type -> Maybe Substitution
-- AD-TopL
disjoint ctx (TyMono TyTop)         a
  = Just EmptySubst
-- AD-TopR
disjoint ctx a                      (TyMono TyTop)
  = Just EmptySubst
-- AD-VarL
disjoint ctx (TyMono (TyVar ap))     b
  = do a <- typeFromContext ctx ap
       (c, s) <- subRight ctx Null a b
       return s
-- AD-VarR
disjoint ctx a                      (TyMono (TyVar bt))
  = do b <- typeFromContext ctx bt
       (c, s) <- subRight ctx Null b a
       return s
-- AD-Arr
disjoint ctx (TyArr a1 a2) (TyArr b1 b2)
  = disjoint ctx a2 b2
-- AD-ArrL
disjoint ctx (TyArr a1 a2)          b
  -- B not arrow type is implicitly covered by AD-Arr
  = disjoint ctx a2 b
-- AD-ArrR
disjoint ctx a                      (TyArr b1 b2)
  -- A not arrow type is implicitly covered by AD-Arr
  = disjoint ctx a b2
-- AD-AndL
disjoint ctx (TyIs a1 a2)           b
  -- B not arrow type is implicitly covered by AD-ArrR
  = do
    s1 <- disjoint ctx a1 b
    s2 <- disjoint ctx a2 b
    if s1 == s2 then return s2 else Nothing
-- AD-AndR
disjoint ctx a                      (TyIs b1 b2)
  -- A not arrow type is implicitly covered by AD-ArrL
  = do
    s1 <- disjoint ctx a b1
    s2 <- disjoint ctx a b2
    if s1 == s2 then return s2 else Nothing
-- AD-All
disjoint ctx (TyAbs ap a1 a2)        (TyAbs ap' b1 b2)
  | ap == ap' = disjoint (SubstSnoc ctx ap (TyIs a1 b1)) (substType (SVar ap (TySubstVar ap) EmptySubst) a2) (substType (SVar ap (TySubstVar ap) EmptySubst) b2)
-- AD-AllL
disjoint ctx (TyAbs ap a b1)        b2
  = disjoint (SubstSnoc ctx ap a) (substType (SVar ap (TySubstVar ap) EmptySubst) b1) b2
-- AD-AllR
disjoint ctx b1        (TyAbs ap a b2)
  = disjoint (SubstSnoc ctx ap a) b1 (substType (SVar ap (TySubstVar ap) EmptySubst) b2)
-- AD-Ax
disjoint ctx a                      b
  = if disjointAx a b then return EmptySubst else Nothing


disjointAx :: Type -> Type -> Bool
disjointAx (TyMono TyNat) (TyMono TyBool) = True
disjointAx (TyMono TyBool) (TyMono TyNat) = True
disjointAx _ _ = False


subtyping :: Type -> Type -> Maybe (Target.Coercion, Substitution)
subtyping = subRight Empty Null


queueToCoercion :: Queue -> Type -> Target.Coercion
queueToCoercion = undefined


subRight :: TypeContext -> Queue -> Type -> Type -> Maybe (Target.Coercion, Substitution)
-- ?
subRight ctx l a (TyMono TyTop) =
  return (
    Target.CoComp
      (queueToCoercion l (TyMono TyTop))
      (Target.CoTop (elabType a)),
    EmptySubst
    )
-- AR-and
subRight ctx l a (TyIs b1 b2) = do
  (c1, s1) <- subRight ctx l a b1
  (c2, s2) <- subRight ctx l a b2
  guard (s1 == s2)
  return (
    Target.CoComp
      (queueToCoercion l (TyIs b1 b2))
      (Target.CoPair c1 c2),
    s1
    )
-- ?
subRight ctx l a (TyArr b1 b2) = subRight ctx (ExtraType l b1) a b2
-- AR-all
subRight ctx l a (TyAbs ap b1 b2) = do
  (c, s) <- subRight (VarSnoc ctx ap b1) l a b2
  return (Target.CoTyAbs ap c, s)
-- AR-base
subRight ctx l a b = case typeToBase b of
  Nothing -> Nothing
  Just bb -> do
    (ac, s) <- subLeft ctx l Null a (ContextAbs _ _) a bb  -- TODO: where are the coercion contexts? how do we represent the id context?
    return (_, s)  -- TODO: what are the rules for algorithmic context application?


freshVar :: Maybe Variable
freshVar = undefined


subLeft :: TypeContext -> Queue -> Queue -> Type -> AlgContext -> Type -> BaseType -> Maybe (AlgContext, Substitution)
-- AL-Base
subLeft ctx Null m a0 c e1 e2 = case typeToBase e1 of  -- TODO: switch case to pattern matching to avoid false enters
  Nothing -> Nothing
  Just bb ->  do
    sub <- unify ctx bb e2
    return (c, sub)
-- AL-VarArr
subLeft ctx (ExtraType l b1) m a0 c (TySubstVar ap) e = do
  ap1 <- freshVar
  ap2 <- freshVar
  let sub' = (SVar ap (TyArr (TySubstVar ap1) (TySubstVar ap2)) EmptySubst) in do
    (c1, sub1) <- subRight (substContext sub' ctx) Null (substType sub' b1) (TySubstVar ap1)
    (c', sub) <- subLeft ctx l (ExtraType m b1) a0 (ContextAbs _ _) (TySubstVar ap2) e
    return (c', appendSubst sub' (appendSubst sub1 sub))
-- AL-AndL & AL-AndR
subLeft ctx l m a0 c (TyIs a1 a2) e = andL ctx l m a0 c (TyIs a1 a2) e <|> andR ctx l m a0 c (TyIs a1 a2) e
  where
    andL ctx l m a0 c (TyIs a1 a2) e = subLeft ctx l m a0 (ContextAbs _ _) a1 e
    andR ctx l m a0 c (TyIs a1 a2) e = subLeft ctx l m a0 (ContextAbs _ _) a1 e
-- AL-Arr & AL-MP
subLeft ctx l m a0 c (TyArr a1 a2) e = arr ctx l m a0 c (TyArr a1 a2) e <|> mp ctx l m a0 c (TyArr a1 a2) e
  where
    arr ctx (ExtraType l b1) m a0 c (TyArr a1 a2) e = do
      (c1, sub1) <- subRight ctx Null b1 a1
      (c', sub) <- subLeft ctx l (ExtraType m b1) a0 (ContextAbs _ _) a2 e
      return (c', appendSubst _ sub1)
    mp ctx l m a0 c (TyArr a1 a2) e = do
      (c1, sub1) <- subRight ctx Null a0 (queueToType m a1)
      (c'', sub2) <- subLeft ctx l m a0 c' a2 e
      let c' = ContextAbs _ _ in
        return (c', appendSubst sub2 sub1)
-- AL-Forall
subLeft ctx l m a0 c (TyAbs ap a b) e = do
  ap <- freshVar
  subLeft (SubstSnoc ctx ap a) l m a0 (ContextAbs _ _) (substType (SVar ap (TySubstVar ap) EmptySubst) b) e





-- * Old code from here
-- ----------------------------------------------------------------------------

inference :: Expression -> Maybe (Type, Target.Expression)
inference = inferenceWithContext Empty


-- | inferenceWithContext
inferenceWithContext :: TypeContext -> Expression -> Maybe (Type, Target.Expression)
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
inferenceWithContext _ ExAbs {} = Nothing


-- | Checking
checking :: TypeContext -> Expression -> Type -> Maybe Target.Expression
-- T-ABS
checking c (ExAbs x e) (TyArr a b)
  = do v <- checking (VarSnoc c x a) e b
       return (Target.ExAbs x (elabType a) v)
-- T-SUB
checking c e a
  = do (b, v) <- inferenceWithContext c e
       (co, _) <- subtyping b a
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


-- data CallStack
--   = EmptyStack
--   | Add Type Type CallStack


-- stackContains :: CallStack -> Type -> Type -> Bool
-- stackContains EmptyStack _ _ = False
-- stackContains (Add a' t' s) a t = (t == t' && a == a') || stackContains s a t


-- data XEnv
--   = XHole
--   | XCoArr XEnv Type Type Target.Coercion
--   | XProjLeft XEnv Type Type
--   | XProjRight XEnv Type Type
--   | XModPon Queue Target.Coercion Target.Coercion Type Type


-- xSem :: XEnv -> Target.Coercion -> Target.Coercion
-- xSem XHole k                 = k
-- xSem (XCoArr x _ _ k1) k     = xSem x (Target.CoArr k1 k)
-- xSem (XProjLeft x a b) k     = xSem x (Target.CoComp k (Target.CoPr1 a' b'))
--   where a' = elabType a
--         b' = elabType b
-- xSem (XProjRight x a b) k    = xSem x (Target.CoComp k (Target.CoPr2 a' b'))
--   where a' = elabType a
--         b' = elabType b
