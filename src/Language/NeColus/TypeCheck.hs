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


elabMono :: Monotype -> Target.Type
elabMono TyNat = Target.TyNat
elabMono TyTop = Target.TyTop


appendSubst :: Substitution -> Substitution -> Substitution
appendSubst s1 s2 = undefined


wellFormedSubst :: TypeContext -> Substitution -> Maybe Substitution
wellFormedSubst _ EmptySubst = Just EmptySubst
wellFormedSubst (VarSnoc ctx ap b) (Cons ap' a sub)
  | ap == ap'  = wellFormedSubst ctx (Cons ap' a sub)
wellFormedSubst (SubstSnoc ctx ap b) (Cons ap' a sub)
  | ap == ap' = do
    s1 <- wellFormedSubst ctx sub
    ds <- disjoint ctx a b
    let s2 = appendSubst s1 (appendSubst sub ds)
      in return $ appendSubst s1 s2


unifyB :: TypeContext -> BaseType -> BaseType -> Maybe Substitution
unifyB ctx e e' = Just EmptySubst
unifyB ctx BaseNat (BaseSubstVar ap) = let nat = baseToType BaseNat in do
  sub <- wellFormedSubst ctx (Cons ap nat EmptySubst)
  return $ (Cons ap nat sub)
unifyB ctx (BaseSubstVar ap) BaseNat = let nat = baseToType BaseNat in do
  sub <- wellFormedSubst ctx (Cons ap nat EmptySubst)
  return $ (Cons ap nat sub)
unifyB ctx (BaseSubstVar ap) (BaseVar ap')
  | ap == ap' = let var = baseToType (BaseVar ap') in do
    sub <- wellFormedSubst ctx (Cons ap var EmptySubst)
    return $ (Cons ap var sub)
unifyB ctx (BaseVar ap) (BaseSubstVar ap')
  | ap == ap' = let var = baseToType (BaseVar ap) in do
    sub <- wellFormedSubst ctx (Cons ap var EmptySubst)
    return $ (Cons ap var sub)


unifyM :: TypeContext -> BaseType -> BaseType -> Maybe Substitution
unifyM = unifyB


substitute :: Substitution -> Type -> Type
substitute = undefined


disjoint :: TypeContext -> Type -> Type -> Maybe Substitution
-- AD-TopL
disjoint ctx (TyMono TyTop)         a
  = Just EmptySubst
-- AD-TopR
disjoint ctx a                      (TyMono TyTop)
  = Just EmptySubst
-- AD-VarL
disjoint ctx (TyMono (TyVar ap))     b
  = case (typeFromContext ctx ap) of
      Left _ -> Nothing
      Right a -> do
        (c, s) <- subRight ctx Null a b
        return s
-- AD-VarR
disjoint ctx a                      (TyMono (TyVar bt))
  = case (typeFromContext ctx bt) of
      Left _ -> Nothing
      Right b -> do
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
  | ap == ap' = disjoint (SubstSnoc ctx ap (TyIs a1 b1)) (substitute (Cons ap (TySubstVar ap) EmptySubst) a2) (substitute (Cons ap (TySubstVar ap) EmptySubst) b2)
-- AD-AllL
disjoint ctx (TyAbs ap a b1)        b2
  = disjoint (SubstSnoc ctx ap a) (substitute (Cons ap (TySubstVar ap) EmptySubst) b1) b2
-- AD-AllR
disjoint ctx b1        (TyAbs ap a b2)
  = disjoint (SubstSnoc ctx ap a) b1 (substitute (Cons ap (TySubstVar ap) EmptySubst) b2)
-- AD-Ax
disjoint ctx a                      b
  = disjointAx a b


disjointAx :: Type -> Type -> Maybe Substitution
disjointAx = undefined


subtyping :: Type -> Type -> Maybe (Target.Coercion, Substitution)
subtyping = subRight Empty Null


queueToCoercion :: Queue -> Type -> Target.Coercion
queueToCoercion = undefined


subRight :: TypeContext -> Queue -> Type -> Type -> Maybe (Target.Coercion, Substitution)
-- ?
subRight ctx l a (TyMono TyTop) = return (Target.CoComp (queueToCoercion l (TyMono TyTop)) (Target.CoTop (elabType a)), EmptySubst)
-- AR-and
subRight ctx l a (TyIs b1 b2) = do
  (c1, s1) <- subRight ctx l a b1
  (c2, s2) <- subRight ctx l a b2
  guard (s1 == s2)
  return (Target.CoComp (queueToCoercion l (TyIs b1 b2)) (Target.CoPair c1 c2), s1)
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
    (s, ac) <- subLeft ctx l Null a (ContextAbs _ _) a bb
    return (_, s)


subLeft :: TypeContext -> Queue -> Queue -> Type -> AlgContext -> Type -> BaseType -> Maybe (Substitution, AlgContext)
-- AL-Base
subLeft ctx Null m a0 c e1 e2 = undefined
-- AL-VarArr
subLeft ctx (ExtraType l b1) m a0 c (TySubstVar ap) e = undefined
-- AL-AndL
subLeft ctx l m a0 c (TyIs a1 a2) e = undefined
-- AL-AndR
subLeft ctx l m a0 c (TyIs a1 a2) e = undefined  -- TODO: when does this apply?
-- AL-Arr
subLeft ctx (ExtraType l b1) m a0 c (TyArr a1 a2) e = undefined
-- AL-MP
subLeft ctx l m a0 c (TyArr a1 a2) e = undefined  -- TODO: same question
-- AL-Forall
subLeft ctx l m a0 c (TyAbs ap a b) e = undefined

-- * Old code from here
-- ----------------------------------------------------------------------------

guardWithMsg :: Bool -> String -> TcM ()
guardWithMsg True  _ = return ()
guardWithMsg False s = Left s

-- * NeColus Typing
-- ----------------------------------------------------------------------------




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
stackContains (Add a' t' s) a t = (t == t' && a == a') || stackContains s a t


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

