{-# OPTIONS_GHC -Wall #-}

module Language.Source.TypeCheck (inference, checking) where

import qualified Language.Target as Target

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Variable
import Data.Label
import Data.Maybe

import Language.Source.Syntax


-- * Algorithmic typing
-- ----------------------------------------------------------------------------

data BaseType
  = BaseNat
  | BaseBool
  | BaseTop
  | BaseVar Variable
  | BaseSubstVar Variable


typeToBase :: Type -> Maybe BaseType
typeToBase (TyMono TyNat) = Just BaseNat
typeToBase (TyMono TyTop) = Just BaseTop
typeToBase (TyMono (TyVar v)) = Just (BaseVar v)
typeToBase (TyMono (TySubstVar v)) = Just (BaseSubstVar v)
typeToBase _ = Nothing

baseToMono :: BaseType -> Monotype
baseToMono BaseNat = TyNat
baseToMono BaseTop = TyTop
baseToMono (BaseVar v) = TyVar v
baseToMono (BaseSubstVar v) = TySubstVar v


-- | For a Source type, get the corresponding Target type.
elabType :: Type -> Target.Type
elabType (TyMono m) = elabMono m
elabType (TyArr a b) = Target.TyArr (elabType a) (elabType b)
elabType (TyIs a b)  = Target.TyTup (elabType a) (elabType b)
-- elabType (TyRec l a) = Target.TyRec l (elabType a)

elabMono :: Monotype -> Target.Type
elabMono TyNat = Target.TyNat
elabMono TyTop = Target.TyTop

-- * Coercion contexts
-- ----------------------------------------------------------------------------

data CoContext
  = Hole
  | XCoArr Target.Coercion CoContext
  | XCoPr1 Type Type CoContext
  | XCoPr2 Type Type CoContext
  | XCoMP Queue Target.Coercion Type Type CoContext
  | XCoAt Type CoContext
  | XCoLabel Label CoContext


completeCoercion :: CoContext -> Target.Coercion -> Target.Coercion
completeCoercion Hole c = c
completeCoercion (XCoArr c' ctx) c = completeCoercion ctx (Target.CoArr c' c)
completeCoercion (XCoPr1 a b ctx) c = let
  a' = elabType a
  b' = elabType b
  in completeCoercion ctx (Target.CoComp c (Target.CoPr1 a' b'))
completeCoercion (XCoPr2 a b ctx) c =  let
  a' = elabType a
  b' = elabType b
  in completeCoercion ctx (Target.CoComp c (Target.CoPr2 a' b'))
completeCoercion (XCoMP m c1 a b ctx) c = let
  a' = elabType a
  b' = elabType b
  pr1 = Target.CoPr1 (Target.TyArr a' b') a'
  pr2 = Target.CoPr2 (Target.TyArr a' b') a'
  mp = Target.CoMP pr1 pr2
  comp1 = queueToCoercion m (Target.CoComp c mp) (TyArr a b) a
  idc = Target.CoId (Target.TyArr a' b')
  comp2 = Target.CoComp (completeCoercion ctx idc) c1
  in Target.CoComp comp1 comp2
completeCoercion (XCoAt t ctx) c = completeCoercion ctx (Target.CoAt c (elabType t))
completeCoercion (XCoLabel l ctx) c = completeCoercion ctx (Target.CoRec l c)

-- * Substitutions
-- ----------------------------------------------------------------------------

appendSubst :: Substitution -> Substitution -> Substitution
appendSubst EmptySubst s    = s
appendSubst (SVar ap t f) s = (SVar ap t (appendSubst f s))
appendSubst (SSub ap t f) s = (SSub ap t (appendSubst f s))


substType :: Substitution -> Type -> Type
substType EmptySubst t = t
substType sub@(SVar _ _ s) t = let t' = substType s t in goT sub t'
substType sub@(SSub _ _ s) t = let t' = substType s t in goT sub t'

goT sub@(SVar ap t s) (TyMono TyNat)   = TyMono TyNat
goT sub@(SVar ap t s) (TyMono TyTop)   = TyMono TyTop
goT sub@(SVar ap t s) (TyMono (TyVar v))
  | ap == v = TyMono t
  | otherwise = (TyMono (TyVar v))
goT sub@(SVar ap t s) (TyMono (TySubstVar ap')) = TyMono (TySubstVar ap')
goT sub@(SVar ap t s) (TyArr a b)      = TyArr (goT sub a) (goT sub b)
goT sub@(SVar ap t s) (TyIs a b)       = TyIs (goT sub a) (goT sub b)
goT sub@(SVar ap t s) (TyAbs ap' a b)  = TyAbs ap' (goT sub a) (goT sub b)
goT sub@(SVar ap t s) (TyRec l a)      = TyRec l (goT sub a)

goT sub@(SSub ap t s) (TyMono TyNat)   = TyMono TyNat
goT sub@(SSub ap t s) (TyMono TyTop)   = TyMono TyTop
goT sub@(SSub ap t s) (TyMono (TyVar v)) = TyMono (TyVar v)
goT sub@(SSub ap t s) (TyMono (TySubstVar ap'))
  | ap == ap' = TyMono t
  | otherwise = TyMono (TySubstVar ap')
goT sub@(SSub ap t s) (TyArr a b)      = TyArr (goT sub a) (goT sub b)
goT sub@(SSub ap t s) (TyIs a b)       = TyIs (goT sub a) (goT sub b)
goT sub@(SSub ap t s) (TyAbs ap' a b)  = TyAbs ap' (goT sub a) (goT sub b)
goT sub@(SSub ap t s) (TyRec l a)      = TyRec l (goT sub a)


substExpr :: Substitution -> Expression -> Expression
substExpr EmptySubst e = e
substExpr sub@(SVar _ _ s) e = let e' = substExpr s e in goE sub e'
substExpr sub@(SSub _ _ s) e = let e' = substExpr s e in goE sub e'

goE sub@(SVar ap t s) (ExLit i)         = ExLit i
goE sub@(SVar ap t s) (ExTop)           = ExTop
goE sub@(SVar ap t s) (ExTrue)          = ExTrue
goE sub@(SVar ap t s) (ExFalse)         = ExFalse
goE sub@(SVar ap t s) (ExVar x)         = ExVar x
goE sub@(SVar ap t s) (ExAbs x e)       = ExAbs x (goE sub e)
goE sub@(SVar ap t s) (ExApp e1 e2)     = ExApp (goE sub e1) (goE sub e2)
goE sub@(SVar ap t s) (ExMerge e1 e2)   = ExMerge (goE sub e1) (goE sub e2)
goE sub@(SVar ap t s) (ExAnn e a)       = ExAnn (goE sub e) (substType sub a)
goE sub@(SVar ap t s) (ExTyAbs ap' a e) = ExTyAbs ap' (substType sub a) (goE sub e)
goE sub@(SVar ap t s) (ExTyApp e a)     = ExTyApp (goE sub e) (substType sub a)
goE sub@(SVar ap t s) (ExRec l e)       = ExRec l (goE sub e)
goE sub@(SVar ap t s) (ExRecFld e l)    = ExRecFld (goE sub e) l

goE sub@(SSub ap t s) (ExLit i)         = ExLit i
goE sub@(SSub ap t s) (ExTop)           = ExTop
goE sub@(SSub ap t s) (ExTrue)          = ExTrue
goE sub@(SSub ap t s) (ExFalse)         = ExFalse
goE sub@(SSub ap t s) (ExVar x)         = ExVar x
goE sub@(SSub ap t s) (ExAbs x e)       = ExAbs x (goE sub e)
goE sub@(SSub ap t s) (ExApp e1 e2)     = ExApp (goE sub e1) (goE sub e2)
goE sub@(SSub ap t s) (ExMerge e1 e2)   = ExMerge (goE sub e1) (goE sub e2)
goE sub@(SSub ap t s) (ExAnn e a)       = ExAnn (goE sub e) (substType sub a)
goE sub@(SSub ap t s) (ExTyAbs ap' a e) = ExTyAbs ap' (substType sub a) (goE sub e)
goE sub@(SSub ap t s) (ExTyApp e a)     = ExTyApp (goE sub e) (substType sub a)
goE sub@(SSub ap t s) (ExRec l e)       = ExRec l (goE sub e)
goE sub@(SSub ap t s) (ExRecFld e l)    = ExRecFld (goE sub e) l


substContext :: Substitution -> TypeContext -> TypeContext
substContext EmptySubst c = c
substContext sub@(SVar _ _ s) c = let c' = substContext s c in goC sub c'
substContext sub@(SSub _ _ s) c = let c' = substContext s c in goC sub c'

goC sub@(SVar ap t s) EmptyCtx                 = EmptyCtx
goC sub@(SVar ap t s) (CVar ctx ap' a)
  | ap == ap' = goC sub ctx
  | otherwise = (CVar (goC sub ctx) ap' (substType sub a))
goC sub@(SVar ap t s) (CSub ctx ap' a) = (CVar (goC sub ctx) ap' (substType sub a))

goC sub@(SSub ap t s) EmptyCtx                 = EmptyCtx
goC sub@(SSub ap t s) (CVar ctx ap' a)   = (CVar (goC sub ctx) ap' (substType sub a))
goC sub@(SSub ap t s) (CSub ctx ap' a)
  | ap == ap' = goC sub ctx
  | otherwise = (CVar (goC sub ctx) ap' (substType sub a))


substQueue :: Substitution -> Queue -> Queue
substQueue EmptySubst q = q
substQueue sub@(SVar _ _ s) q = let q' = substQueue s q in goQ sub q'
substQueue sub@(SSub _ _ s) q = let q' = substQueue s q in goQ sub q'

goQ sub@(SVar ap t s) Null = Null
goQ sub@(SVar ap t s) (ExtraType m a) = ExtraType (goQ sub m) (substType sub a)
goQ sub@(SVar ap t s) (ExtraLabel m l) = ExtraLabel (goQ sub m) l

goQ sub@(SSub ap t s) Null = Null
goQ sub@(SSub ap t s) (ExtraType m a) = ExtraType (goQ sub m) (substType sub a)
goQ sub@(SSub ap t s) (ExtraLabel m l) = ExtraLabel (goQ sub m) l


substCoercion = undefined


substCoCtx :: Substitution -> CoContext -> CoContext
substCoCtx EmptySubst cx = cx
substCoCtx sub@(SVar _ _ s) cx = let cx' = substCoCtx s cx in goCx sub cx'
substCoCtx sub@(SSub _ _ s) cx = let cx' = substCoCtx s cx in goCx sub cx'

goCx sub@(SVar ap t s) Hole = Hole
goCx sub@(SVar ap t s) (XCoArr c ctx) = XCoArr (substCoercion sub c) (substCoCtx sub ctx)
goCx sub@(SVar ap t s) (XCoPr1 a b ctx) = XCoPr1 (substType sub a) (substType sub b) (substCoCtx sub ctx)
goCx sub@(SVar ap t s) (XCoPr2 a b ctx) = XCoPr2 (substType sub a) (substType sub b) (substCoCtx sub ctx)
goCx sub@(SVar ap t s) (XCoMP m c1 a b ctx) = XCoMP (substQueue sub m) (substCoercion sub c1) (substType sub a) (substType sub b) (substCoCtx sub ctx)
goCx sub@(SVar ap t s) (XCoAt t' ctx) = undefined
goCx sub@(SVar ap t s) (XCoLabel l ctx) = undefined

-- * Well-formedness
-- ----------------------------------------------------------------------------

wellFormedSubst :: TypeContext -> Substitution -> Maybe Substitution
-- WFS-nil
wellFormedSubst _ EmptySubst = Just EmptySubst
-- ?
wellFormedSubst (CVar ctx ap b) (SVar ap' a sub)
  | ap == ap'  = wellFormedSubst ctx (SVar ap' a sub)
  | otherwise = Nothing  -- TODO: ?
wellFormedSubst (CSub ctx ap b) (SVar ap' a sub)
-- WFS-next
  | ap == ap' = do
    s1 <- wellFormedSubst ctx sub
    let app = appendSubst s1 sub in do
      s2 <- disjoint (substContext app ctx) (substType app (TyMono a)) (substType app b)
      return $ appendSubst s2 s1
  | otherwise = wellFormedSubst ctx (SVar ap' a sub)

-- * Unification
-- ----------------------------------------------------------------------------

unify :: TypeContext -> BaseType -> BaseType -> Maybe Substitution
-- U-refl
unify ctx BaseNat BaseNat = Just EmptySubst
unify ctx BaseBool BaseBool = Just EmptySubst
unify ctx BaseTop BaseTop = Just EmptySubst

unify ctx (BaseVar a) (BaseVar b)
  | a == b = Just EmptySubst
  | otherwise = Nothing  -- TODO: ?
unify ctx (BaseSubstVar a) (BaseSubstVar b)
  | a == b = Just EmptySubst
  | otherwise = vvl <|> vvr where
    -- U-VVL
    vvl = do
      sub <- wellFormedSubst ctx (SVar a (TySubstVar b) EmptySubst)
      return $ SVar a (TySubstVar b) sub
    -- U-VVR
    vvr = do
      sub <- wellFormedSubst ctx (SVar b (TySubstVar a) EmptySubst)
      return $ SVar b (TySubstVar a) sub

-- U-NatV
unify ctx BaseNat (BaseSubstVar ap) = let nat = baseToMono BaseNat in do
  sub <- wellFormedSubst ctx (SVar ap nat EmptySubst)
  return $ SVar ap nat sub
-- U-VNat
unify ctx (BaseSubstVar ap) BaseNat = let nat = baseToMono BaseNat in do
  sub <- wellFormedSubst ctx (SVar ap nat EmptySubst)
  return $ SVar ap nat sub

-- U-VC
unify ctx (BaseSubstVar ap') (BaseVar ap)
  | ap == ap' = let var = baseToMono (BaseVar ap) in do
    sub <- wellFormedSubst ctx (SVar ap' var EmptySubst)
    return $ SVar ap' var sub
  | otherwise = Nothing  -- TODO: ?
-- U-CV
unify ctx (BaseVar ap) (BaseSubstVar ap')
  | ap == ap' = let var = baseToMono (BaseVar ap) in do
    sub <- wellFormedSubst ctx (SVar ap' var EmptySubst)
    return $ SVar ap' var sub
  | otherwise = Nothing  -- TODO: ?

-- * Disjointness
-- ----------------------------------------------------------------------------

disjoint :: TypeContext -> Type -> Type -> Maybe Substitution
-- AD-TopL
disjoint ctx (TyMono TyTop)         a              = Just EmptySubst
-- AD-TopR
disjoint ctx a                      (TyMono TyTop) = Just EmptySubst
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
-- AD-UVarL
disjoint ctx (TyMono (TySubstVar ap)) b
  = do a <- typeFromContext ctx ap  -- TODO: this might be wrong
       (c, s) <- subRight ctx Null a b
       return s
-- AD-UVarR
disjoint ctx a                      (TyMono (TySubstVar bt))
  = do b <- typeFromContext ctx bt  -- TODO: same as above
       (c, s) <- subRight ctx Null b a
       return s
disjoint ctx (TyRec l1 a) (TyRec l2 b)
-- AD-Rcd
  | l1 == l2 = disjoint ctx a b
-- AD-Nrcd
  | otherwise = Just EmptySubst
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
    if s1 == s2 then return s2 else Nothing  -- TODO: ?
-- AD-AndR
disjoint ctx a                      (TyIs b1 b2)
  -- A not arrow type is implicitly covered by AD-ArrL
  = do
    s1 <- disjoint ctx a b1
    s2 <- disjoint ctx a b2
    if s1 == s2 then return s2 else Nothing  -- TODO: ?
-- AD-All
disjoint ctx (TyAbs ap a1 a2)        (TyAbs ap' b1 b2)
  | ap == ap' = disjoint
                  (CSub ctx ap (TyIs a1 b1))
                  (substType (SVar ap (TySubstVar ap) EmptySubst) b1)
                  (substType (SVar ap (TySubstVar ap) EmptySubst) b2)
  | otherwise = Nothing  -- TODO: ?
-- AD-AllL
disjoint ctx (TyAbs ap a b1)        b2
  = disjoint
      (CSub ctx ap a)
      (substType (SVar ap (TySubstVar ap) EmptySubst) b1)
      b2
-- AD-AllR
disjoint ctx b1        (TyAbs ap a b2)
  = disjoint
      (CSub ctx ap a)
      b1
      (substType (SVar ap (TySubstVar ap) EmptySubst) b2)
-- AD-Ax
disjoint ctx a                      b
  = if disjointAx a b then return EmptySubst else Nothing


disjointAx :: Type -> Type -> Bool
-- AX-NatBool
disjointAx (TyMono TyNat) (TyMono TyBool) = True
-- AX-BoolNat
disjointAx (TyMono TyBool) (TyMono TyNat) = True
-- AX-RcdNat
disjointAx (TyRec l a) (TyMono TyNat) = True
-- AX-NatRcd
disjointAx (TyMono TyNat) (TyRec l a) = True
-- AX-RcdBool
disjointAx (TyRec l a) (TyMono TyBool) = True
-- AX-BoolRcd
disjointAx (TyMono TyBool) (TyRec l a) = True

disjointAx _ _ = False

-- * Subtyping
-- ----------------------------------------------------------------------------

subtyping :: Type -> Type -> Maybe (Target.Coercion, Substitution)
subtyping = subRight EmptyCtx Null


queueToCoercion :: Queue -> Target.Coercion -> Type -> Type -> Target.Coercion
queueToCoercion = undefined


subRight :: TypeContext -> Queue -> Type -> Type -> Maybe (Target.Coercion, Substitution)
-- ?
subRight ctx l a (TyMono TyTop) =
  return (
    Target.CoComp
      (queueToCoercion l Target.CoTopAll (TyMono TyTop) (TyMono TyTop))  -- TODO: incorrect
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
      (queueToCoercion l (Target.CoId (Target.TyTup (elabType b1) (elabType b2)))  b1 b2)
      (Target.CoPair c1 c2),
    s1
    )
-- ?
subRight ctx l a (TyArr b1 b2) = subRight ctx (ExtraType l b1) a b2
-- AR-all
subRight ctx l a (TyAbs ap b1 b2) = do
  (c, s) <- subRight (CVar ctx ap b1) l a b2
  return (Target.CoTyAbs ap c, s)
-- AR-base
subRight ctx l a b = case typeToBase b of
  Nothing -> Nothing
  Just bb -> do
    (ac, s) <- subLeft ctx l Null a Hole a bb
    return (completeCoercion ac (Target.CoId (elabType a)), s)


freshVar :: Maybe Variable
freshVar = undefined


subLeft :: TypeContext -> Queue -> Queue -> Type -> CoContext -> Type -> BaseType -> Maybe (CoContext, Substitution)
-- AL-Base
subLeft ctx Null m a0 c e1 e2 = case typeToBase e1 of  -- TODO: switch case to pattern matching to avoid false enters
  Nothing -> Nothing
  Just bb ->  do
    sub <- unify ctx bb e2
    return (c, sub)
-- AL-VarArr
subLeft ctx (ExtraType l b1) m a0 c (TyMono (TySubstVar ap)) e = do
  ap1 <- freshVar
  ap2 <- freshVar
  let sub' = (SVar ap (TyMonoArr (TySubstVar ap1) (TySubstVar ap2)) EmptySubst) in do
    (c1, sub1) <- subRight (substContext sub' ctx) Null (substType sub' b1) (TyMono (TySubstVar ap1))
    (c', sub) <- subLeft ctx l (ExtraType m b1) a0 (XCoArr c1 c) (TyMono (TySubstVar ap2)) e
    return (c', appendSubst sub' (appendSubst sub1 sub))
-- AL-AndL & AL-AndR
subLeft ctx l m a0 c (TyIs a1 a2) e = andL ctx l m a0 c (TyIs a1 a2) e <|> andR ctx l m a0 c (TyIs a1 a2) e
  where
    andL ctx l m a0 c (TyIs a1 a2) e = subLeft ctx l m a0 (XCoPr1 a1 a2 c) a1 e
    andR ctx l m a0 c (TyIs a1 a2) e = subLeft ctx l m a0 (XCoPr2 a1 a2 c) a1 e
-- AL-Arr & AL-MP
subLeft ctx l m a0 c (TyArr a1 a2) e = arr ctx l m a0 c (TyArr a1 a2) e <|> mp ctx l m a0 c (TyArr a1 a2) e
  where
    arr ctx (ExtraType l b1) m a0 c (TyArr a1 a2) e = do
      (c1, sub1) <- subRight ctx Null b1 a1
      (c', sub) <- subLeft ctx l (ExtraType m b1) a0 (XCoArr c1 c) a2 e
      return (c', appendSubst sub sub1)
    mp ctx l m a0 c (TyArr a1 a2) e = do
      (c1, sub1) <- subRight ctx Null a0 (queueToType m a1)
      (c', sub2) <- subLeft
                      (substContext sub1 ctx)
                      (substQueue sub1 l)
                      (substQueue sub1 m)
                      (substType sub1 a0)
                      (substCoCtx sub1 (XCoMP m c1 a1 a2 c))
                      (substType sub1 a2)
                      (substType sub1 e)
      return (c', appendSubst sub2 sub1)
-- AL-Forall
subLeft ctx l m a0 c (TyAbs ap a b) e = do
  ap' <- freshVar
  subLeft (CSub ctx ap a) l m a0 (XCoAt (TyMono (TySubstVar ap')) c) (substType (SVar ap (TySubstVar ap') EmptySubst) b) e





-- * Old code from here
-- ----------------------------------------------------------------------------

inference :: Expression -> Maybe (Type, Target.Expression)
inference = inferenceWithContext EmptyCtx


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
  = do v <- checking (CVar c x a) e b
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
