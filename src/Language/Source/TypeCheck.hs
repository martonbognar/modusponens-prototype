{-# OPTIONS_GHC -Wall #-}

module Language.Source.TypeCheck (inference, checking) where

import qualified Language.Target as Target

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Control.Monad.Renamer
import Control.Monad.Except
import Data.Variable
import Data.Label

import Language.Source.Syntax


queueToType :: Queue -> Type -> Type
queueToType Null a = a
queueToType (ExtraType q b) a = queueToType q (TyArr b a)
queueToType (ExtraLabel q l) a = queueToType q (TyRec l a)

queueToCoercion :: Queue -> Target.Coercion -> Type -> Type -> Target.Coercion
queueToCoercion Null c _ _ = c
queueToCoercion (ExtraType q t) k a b = Target.CoComp (Target.CoArr (Target.CoId t') (queueToCoercion q k a b)) (Target.CoDistArr t' a' b')
  where t' = elabType t
        a' = elabType $ queueToType q a
        b' = elabType $ queueToType q b
queueToCoercion (ExtraLabel _q _l) _k _a _b = undefined  -- TODO: ?

queueTop :: Queue -> Target.Coercion
queueTop Null = Target.CoTop (elabType ( TyTop))
queueTop (ExtraType t a) = Target.CoComp (Target.CoArr (Target.CoTop a') (queueTop t)) Target.CoTopArr
  where a' = elabType a
queueTop (ExtraLabel _q _l) = undefined  -- TODO: ?

-- * Algorithmic typing
-- ----------------------------------------------------------------------------

data BaseType
  = BaseNat
  | BaseBool
  | BaseTop
  | BaseVar Variable
  | BaseSubstVar Variable


typeToBase :: Type -> SubM BaseType
typeToBase TyNat = return BaseNat
typeToBase TyTop = return BaseTop
typeToBase (TyVar v) = return (BaseVar v)
typeToBase (TySubstVar v) = return (BaseSubstVar v)
typeToBase _ = throwError ""

baseToType :: BaseType -> Type
baseToType BaseNat          = TyNat
baseToType BaseBool         = TyBool
baseToType BaseTop          = TyTop
baseToType (BaseVar v)      = TyVar v
baseToType (BaseSubstVar v) = TySubstVar v


-- | For a Source type, get the corresponding Target type.
elabType :: Type -> Target.Type
elabMono TyNat = Target.TyNat
elabMono TyTop = Target.TyTop
elabMono TyBool = Target.TyBool
elabMono (TyVar v) = Target.TyVar v
elabMono (TySubstVar _v) = undefined  -- TODO: ?
elabType (TyArr a b) = Target.TyArr (elabType a) (elabType b)
elabType (TyIs a b)  = Target.TyTup (elabType a) (elabType b)
elabType (TyRec l a) = Target.TyRec l (elabType a)
elabType (TyAbs _v _a _b) = undefined  -- TODO: ?

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

goT :: Substitution -> Type -> Type
goT _sub@(SVar _ap _t _s) ( TyNat)   =  TyNat
goT _sub@(SVar _ap _t _s) ( TyTop)   =  TyTop
goT _sub@(SVar ap t _s) ( (TyVar v))
  | ap == v =  t
  | otherwise = ( (TyVar v))
goT _sub@(SVar _ap _t _s) ( (TySubstVar ap')) =  (TySubstVar ap')
goT sub@(SVar _ap _t _s) (TyArr a b)      = TyArr (goT sub a) (goT sub b)
goT sub@(SVar _ap _t _s) (TyIs a b)       = TyIs (goT sub a) (goT sub b)
goT sub@(SVar _ap _t _s) (TyAbs ap' a b)  = TyAbs ap' (goT sub a) (goT sub b)
goT sub@(SVar _ap _t _s) (TyRec l a)      = TyRec l (goT sub a)

goT _sub@(SSub _ap _t _s) ( TyNat)   =  TyNat
goT _sub@(SSub _ap _t _s) ( TyTop)   =  TyTop
goT _sub@(SSub _ap _t _s) ( (TyVar v)) =  (TyVar v)
goT _sub@(SSub ap t _s) ( (TySubstVar ap'))
  | ap == ap' =  t
  | otherwise =  (TySubstVar ap')
goT sub@(SSub _ap _t _s) (TyArr a b)      = TyArr (goT sub a) (goT sub b)
goT sub@(SSub _ap _t _s) (TyIs a b)       = TyIs (goT sub a) (goT sub b)
goT sub@(SSub _ap _t _s) (TyAbs ap' a b)  = TyAbs ap' (goT sub a) (goT sub b)
goT sub@(SSub _ap _t _s) (TyRec l a)      = TyRec l (goT sub a)


substExpr :: Substitution -> Expression -> Expression
substExpr EmptySubst e = e
substExpr sub@(SVar _ _ s) e = let e' = substExpr s e in goE sub e'
substExpr sub@(SSub _ _ s) e = let e' = substExpr s e in goE sub e'

goE :: Substitution -> Expression -> Expression
goE _sub@(SVar _ap _t _s) (ExLit i)         = ExLit i
goE _sub@(SVar _ap _t _s) (ExTop)           = ExTop
goE _sub@(SVar _ap _t _s) (ExTrue)          = ExTrue
goE _sub@(SVar _ap _t _s) (ExFalse)         = ExFalse
goE _sub@(SVar _ap _t _s) (ExVar x)         = ExVar x
goE sub@(SVar _ap _t _s) (ExAbs x e)       = ExAbs x (goE sub e)
goE sub@(SVar _ap _t _s) (ExApp e1 e2)     = ExApp (goE sub e1) (goE sub e2)
goE sub@(SVar _ap _t _s) (ExMerge e1 e2)   = ExMerge (goE sub e1) (goE sub e2)
goE sub@(SVar _ap _t _s) (ExAnn e a)       = ExAnn (goE sub e) (goT sub a)
goE sub@(SVar _ap _t _s) (ExTyAbs ap' a e) = ExTyAbs ap' (goT sub a) (goE sub e)
goE sub@(SVar _ap _t _s) (ExTyApp e a)     = ExTyApp (goE sub e) (goT sub a)
goE sub@(SVar _ap _t _s) (ExRec l e)       = ExRec l (goE sub e)
goE sub@(SVar _ap _t _s) (ExRecFld e l)    = ExRecFld (goE sub e) l

goE _sub@(SSub _ap _t _s) (ExLit i)         = ExLit i
goE _sub@(SSub _ap _t _s) (ExTop)           = ExTop
goE _sub@(SSub _ap _t _s) (ExTrue)          = ExTrue
goE _sub@(SSub _ap _t _s) (ExFalse)         = ExFalse
goE _sub@(SSub _ap _t _s) (ExVar x)         = ExVar x
goE sub@(SSub _ap _t _s) (ExAbs x e)       = ExAbs x (goE sub e)
goE sub@(SSub _ap _t _s) (ExApp e1 e2)     = ExApp (goE sub e1) (goE sub e2)
goE sub@(SSub _ap _t _s) (ExMerge e1 e2)   = ExMerge (goE sub e1) (goE sub e2)
goE sub@(SSub _ap _t _s) (ExAnn e a)       = ExAnn (goE sub e) (goT sub a)
goE sub@(SSub _ap _t _s) (ExTyAbs ap' a e) = ExTyAbs ap' (goT sub a) (goE sub e)
goE sub@(SSub _ap _t _s) (ExTyApp e a)     = ExTyApp (goE sub e) (goT sub a)
goE sub@(SSub _ap _t _s) (ExRec l e)       = ExRec l (goE sub e)
goE sub@(SSub _ap _t _s) (ExRecFld e l)    = ExRecFld (goE sub e) l


substContext :: Substitution -> TypeContext -> TypeContext
substContext EmptySubst c = c
substContext sub@(SVar _ _ s) c = let c' = substContext s c in goC sub c'
substContext sub@(SSub _ _ s) c = let c' = substContext s c in goC sub c'

goC :: Substitution -> TypeContext -> TypeContext
goC _sub@(SVar _ap _t _s) EmptyCtx                 = EmptyCtx
goC sub@(SVar ap _t _s) (CVar ctx ap' a)
  | ap == ap' = goC sub ctx
  | otherwise = (CVar (goC sub ctx) ap' (goT sub a))
goC sub@(SVar _ap _t _s) (CSub ctx ap' a) = (CVar (goC sub ctx) ap' (goT sub a))

goC _sub@(SSub _ap _t _s) EmptyCtx                 = EmptyCtx
goC sub@(SSub _ap _t _s) (CVar ctx ap' a)   = (CVar (goC sub ctx) ap' (goT sub a))
goC sub@(SSub ap _t _s) (CSub ctx ap' a)
  | ap == ap' = goC sub ctx
  | otherwise = (CVar (goC sub ctx) ap' (goT sub a))


substQueue :: Substitution -> Queue -> Queue
substQueue EmptySubst q = q
substQueue sub@(SVar _ _ s) q = let q' = substQueue s q in goQ sub q'
substQueue sub@(SSub _ _ s) q = let q' = substQueue s q in goQ sub q'

goQ :: Substitution -> Queue -> Queue
goQ _sub@(SVar _ap _t _s) Null = Null
goQ sub@(SVar _ap _t _s) (ExtraType m a) = ExtraType (goQ sub m) (goT sub a)
goQ sub@(SVar _ap _t _s) (ExtraLabel m l) = ExtraLabel (goQ sub m) l

goQ _sub@(SSub _ap _t _s) Null = Null
goQ sub@(SSub _ap _t _s) (ExtraType m a) = ExtraType (goQ sub m) (goT sub a)
goQ sub@(SSub _ap _t _s) (ExtraLabel m l) = ExtraLabel (goQ sub m) l


substCoercion = undefined


substCoCtx :: Substitution -> CoContext -> CoContext
substCoCtx EmptySubst cx = cx
substCoCtx sub@(SVar _ _ s) cx = let cx' = substCoCtx s cx in goCx sub cx'
substCoCtx sub@(SSub _ _ s) cx = let cx' = substCoCtx s cx in goCx sub cx'

goCx :: Substitution -> CoContext -> CoContext
goCx _sub@(SVar _ap _t _s) Hole = Hole
goCx sub@(SVar _ap _t _s) (XCoArr c ctx) = XCoArr (substCoercion sub c) (goCx sub ctx)
goCx sub@(SVar _ap _t _s) (XCoPr1 a b ctx) = XCoPr1 (goT sub a) (goT sub b) (goCx sub ctx)
goCx sub@(SVar _ap _t _s) (XCoPr2 a b ctx) = XCoPr2 (goT sub a) (goT sub b) (goCx sub ctx)
goCx sub@(SVar _ap _t _s) (XCoMP m c1 a b ctx) = XCoMP (goQ sub m) (substCoercion sub c1) (goT sub a) (goT sub b) (goCx sub ctx)
goCx _sub@(SVar _ap _t _s) (XCoAt _t' _ctx) = undefined
goCx _sub@(SVar _ap _t _s) (XCoLabel _l _ctx) = undefined

-- * Well-formedness
-- ----------------------------------------------------------------------------

wellFormedSubst :: TypeContext -> Substitution -> SubM Substitution
-- WFS-nil
wellFormedSubst _ EmptySubst = return EmptySubst
-- ?
wellFormedSubst (CVar ctx ap _b) (SVar ap' a sub)
  | ap == ap'  = wellFormedSubst ctx (SVar ap' a sub)
  | otherwise = throwError ""  -- TODO: ?
wellFormedSubst (CSub ctx ap b) (SVar ap' a sub)
-- WFS-next
  | ap == ap' = do
    s1 <- wellFormedSubst ctx sub
    let app = appendSubst s1 sub in do
      s2 <- disjoint (substContext app ctx) (substType app ( a)) (substType app b)
      return $ appendSubst s2 s1
  | otherwise = wellFormedSubst ctx (SVar ap' a sub)

-- * Unification
-- ----------------------------------------------------------------------------

unify :: TypeContext -> BaseType -> BaseType -> SubM Substitution
-- U-refl
unify _ctx BaseNat BaseNat = return EmptySubst
unify _ctx BaseBool BaseBool = return EmptySubst
unify _ctx BaseTop BaseTop = return EmptySubst

unify _ctx (BaseVar a) (BaseVar b)
  | a == b = return EmptySubst
  | otherwise = throwError ""  -- TODO: ?
unify ctx (BaseSubstVar a) (BaseSubstVar b)
  | a == b = return EmptySubst
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
unify ctx BaseNat (BaseSubstVar ap) = let nat = baseToType BaseNat in do
  sub <- wellFormedSubst ctx (SVar ap nat EmptySubst)
  return $ SVar ap nat sub
-- U-VNat
unify ctx (BaseSubstVar ap) BaseNat = let nat = baseToType BaseNat in do
  sub <- wellFormedSubst ctx (SVar ap nat EmptySubst)
  return $ SVar ap nat sub

-- U-VC
unify ctx (BaseSubstVar ap') (BaseVar ap)
  | ap == ap' = let var = baseToType (BaseVar ap) in do
    sub <- wellFormedSubst ctx (SVar ap' var EmptySubst)
    return $ SVar ap' var sub
  | otherwise = throwError ""  -- TODO: ?
-- U-CV
unify ctx (BaseVar ap) (BaseSubstVar ap')
  | ap == ap' = let var = baseToType (BaseVar ap) in do
    sub <- wellFormedSubst ctx (SVar ap' var EmptySubst)
    return $ SVar ap' var sub
  | otherwise = throwError ""  -- TODO: ?

-- * Disjointness
-- ----------------------------------------------------------------------------

disjoint :: TypeContext -> Type -> Type -> SubM Substitution
-- AD-TopL
disjoint _ctx ( TyTop)         _a              = return EmptySubst
-- AD-TopR
disjoint _ctx _a                      ( TyTop) = return EmptySubst
-- AD-VarVar
disjoint ctx ( (TyVar ap))     ( (TyVar bt)) = varL <|> varR where
  varL = do
    a <- typeFromContext ctx ap
    (_c, s) <- subRight ctx Null a ( (TyVar bt))
    return s
  varR = do
    b <- typeFromContext ctx bt
    (_c, s) <- subRight ctx Null b ( (TyVar ap))
    return s
-- AD-VarL
disjoint ctx ( (TyVar ap))     b
  = do a <- typeFromContext ctx ap
       (_c, s) <- subRight ctx Null a b
       return s
-- AD-VarR
disjoint ctx a                      ( (TyVar bt))
  = do b <- typeFromContext ctx bt
       (_c, s) <- subRight ctx Null b a
       return s
-- AD-UVarL
disjoint ctx ( (TySubstVar ap)) b
  = do a <- typeFromContext ctx ap  -- TODO: this might be wrong
       (_c, s) <- subRight ctx Null a b
       return s
-- AD-UVarR
disjoint ctx a                      ( (TySubstVar bt))
  = do b <- typeFromContext ctx bt  -- TODO: same as above
       (_c, s) <- subRight ctx Null b a
       return s
disjoint ctx (TyRec l1 a) (TyRec l2 b)
-- AD-Rcd
  | l1 == l2 = disjoint ctx a b
-- AD-Nrcd
  | otherwise = return EmptySubst
-- AD-Arr
disjoint ctx (TyArr _a1 a2) (TyArr _b1 b2)
  = disjoint ctx a2 b2
-- AD-ArrL
disjoint ctx (TyArr _a1 a2)          b
  -- B not arrow type is implicitly covered by AD-Arr
  = disjoint ctx a2 b
-- AD-ArrR
disjoint ctx a                      (TyArr _b1 b2)
  -- A not arrow type is implicitly covered by AD-Arr
  = disjoint ctx a b2
-- AD-AndL
disjoint ctx (TyIs a1 a2)           b
  -- B not arrow type is implicitly covered by AD-ArrR
  = do
    s1 <- disjoint ctx a1 b
    s2 <- disjoint ctx a2 b
    if s1 == s2 then return s2 else throwError ""  -- TODO: ?
-- AD-AndR
disjoint ctx a                      (TyIs b1 b2)
  -- A not arrow type is implicitly covered by AD-ArrL
  = do
    s1 <- disjoint ctx a b1
    s2 <- disjoint ctx a b2
    if s1 == s2 then return s2 else throwError ""  -- TODO: ?
-- AD-All
disjoint ctx (TyAbs ap a1 _a2)        (TyAbs ap' b1 b2)
  | ap == ap' = disjoint
                  (CSub ctx ap (TyIs a1 b1))
                  (substType (SVar ap (TySubstVar ap) EmptySubst) b1)
                  (substType (SVar ap (TySubstVar ap) EmptySubst) b2)
  | otherwise = throwError ""  -- TODO: ?
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
disjoint _ctx a                      b
  = if disjointAx a b then return EmptySubst else throwError ""


disjointAx :: Type -> Type -> Bool
-- AX-NatBool
disjointAx ( TyNat) ( TyBool) = True
-- AX-BoolNat
disjointAx ( TyBool) ( TyNat) = True
-- AX-RcdNat
disjointAx (TyRec _l _a) ( TyNat) = True
-- AX-NatRcd
disjointAx ( TyNat) (TyRec _l _a) = True
-- AX-RcdBool
disjointAx (TyRec _l _a) ( TyBool) = True
-- AX-BoolRcd
disjointAx ( TyBool) (TyRec _l _a) = True

disjointAx _ _ = False

disjointI :: TypeContext -> Type -> SubM Substitution
-- UD-Nat
disjointI ctx ( TyNat) = return EmptySubst
-- UD-Bool
disjointI ctx ( TyBool) = return EmptySubst
-- UD-Top
disjointI ctx ( TyTop) = return EmptySubst
-- UD-Var
disjointI ctx ( (TyVar v)) = do
  t <- typeFromContext ctx v
  return EmptySubst
-- UD-UVar
disjointI ctx ( (TySubstVar v)) = do
  t <- typeFromContext ctx v
  return EmptySubst
-- UD-Rcd
disjointI ctx (TyRec l a) = disjointI ctx a
-- UD-Arr
disjointI ctx (TyArr a b) = disjointI ctx b
-- UD-And
disjointI ctx (TyIs a b) = do
  sub <- disjoint ctx a b
  sub1 <- disjointI (substContext sub ctx) (substType sub a)
  sub2 <- disjointI (substContext sub ctx) (substType sub b)
  return $ appendSubst sub1 (appendSubst sub2 sub)
-- UD-All
disjointI ctx (TyAbs ap a b) = disjointI (CVar ctx ap a) b

-- * Subtyping
-- ----------------------------------------------------------------------------

subtyping :: Type -> Type -> SubM (Target.Coercion, Substitution)
subtyping = subRight EmptyCtx Null

subRight :: TypeContext -> Queue -> Type -> Type -> SubM (Target.Coercion, Substitution)
-- AR-top
subRight _ctx l a ( TyTop) = let
  qc = queueTop l
  top = Target.CoTop (elabType a)
  in return (Target.CoComp qc top, EmptySubst)
-- AR-rcd
subRight ctx q a (TyRec l b) = subRight ctx (ExtraLabel q l) a b
-- AR-and
subRight ctx l a (TyIs b1 b2) = do
  (c1, s1) <- subRight ctx l a b1
  (c2, s2) <- subRight ctx l a b2
  guard (s1 == s2)
  let qc = queueToCoercion l (Target.CoId (Target.TyTup (elabType b1) (elabType b2))) b1 b2
    in return (Target.CoComp qc (Target.CoPair c1 c2), s1)
-- AR-arr
subRight ctx l a (TyArr b1 b2) = subRight ctx (ExtraType l b1) a b2
-- AR-all
subRight ctx l a (TyAbs ap b1 b2) = do
  (c, s) <- subRight (CVar ctx ap b1) l a b2
  return (Target.CoTyAbs ap c, s)
-- AR-base
subRight ctx l a b = do
  bb <- typeToBase b
  (ac, s) <- subLeft ctx l Null a Hole a bb
  return (completeCoercion ac (Target.CoId (elabType a)), s)

subLeft :: TypeContext -> Queue -> Queue -> Type -> CoContext -> Type -> BaseType -> SubM (CoContext, Substitution)
-- AL-Base
subLeft ctx Null _m _a0 c e1@( TyNat) e2 = do
  e1' <- typeToBase e1
  sub <- unify ctx e1' e2
  return (c, sub)
subLeft ctx Null _m _a0 c e1@( TyBool) e2 = do
  e1' <- typeToBase e1
  sub <- unify ctx e1' e2
  return (c, sub)
subLeft ctx Null _m _a0 c e1@( TyTop) e2 = do
  e1' <- typeToBase e1
  sub <- unify ctx e1' e2
  return (c, sub)
subLeft ctx Null _m _a0 c e1@( (TyVar _x)) e2 = do
  e1' <- typeToBase e1
  sub <- unify ctx e1' e2
  return (c, sub)
subLeft ctx Null _m _a0 c e1@( (TySubstVar _x)) e2 = do
  e1' <- typeToBase e1
  sub <- unify ctx e1' e2
  return (c, sub)
-- AL-VarArr
subLeft ctx (ExtraType l b1) m a0 c ( (TySubstVar ap)) e = do
  ap1 <- freshVar
  ap2 <- freshVar
  (ctx1, a, ctx2) <- slicesFromContext ctx ap EmptyCtx
  let sub = (SVar ap (TyArr (TySubstVar ap1) (TySubstVar ap2)) EmptySubst) in do
    (c1, sub1) <- subRight
                    (appendContext (substContext sub ctx2) (CSub (CSub ctx1 ap1 ( TyTop)) ap2 a))  -- TODO: probably incorrect
                    Null
                    (substType sub b1)
                    ( (TySubstVar ap1))
    (c', sub2) <- subLeft
                    ctx
                    l
                    (ExtraType m b1)
                    a0
                    (XCoArr c1 c)
                    ( (TySubstVar ap2))
                    e
    return (c', appendSubst sub2 (appendSubst sub1 sub))
-- AL-AndL & AL-AndR
subLeft ctx l m a0 c (TyIs a1 a2) e = andL <|> andR
  where
    andL = subLeft ctx l m a0 (XCoPr1 a1 a2 c) a1 e
    andR = subLeft ctx l m a0 (XCoPr2 a1 a2 c) a1 e
-- AL-Rcd
subLeft ctx (ExtraLabel q l) m a0 c (TyRec _l' a) e = subLeft ctx q (ExtraLabel m l) a0 (XCoLabel l c) a e  -- TODO: label order incorrect, is l==l'?
-- AL-Arr & AL-MP
subLeft ctx l m a0 c (TyArr a1 a2) e
  = arr <|> mp
  where
    arr = case l of
      (ExtraType q b1) -> do
        (c1, sub1) <- subRight ctx Null b1 a1
        e' <- typeToBase (substType sub1 ( (baseToType e)))
        (c', sub2) <- subLeft
                        (substContext sub1 ctx)
                        (substQueue sub1 q)
                        (substQueue sub1 (ExtraType m b1))
                        (substType sub1 a0)
                        (substCoCtx sub1 (XCoArr c1 c))
                        (substType sub1 a2)
                        e'
        return (c', appendSubst sub2 sub1)
      _ -> throwError ""

    mp = do
      (c1, sub1) <- subRight ctx Null a0 (queueToType m a1)
      e' <- typeToBase (substType sub1 ( (baseToType e)))
      (c', sub2) <- subLeft
                      (substContext sub1 ctx)
                      (substQueue sub1 l)
                      (substQueue sub1 m)
                      (substType sub1 a0)
                      (substCoCtx sub1 (XCoMP m c1 a1 a2 c))
                      (substType sub1 a2)
                      e'
      return (c', appendSubst sub2 sub1)
-- AL-Forall
subLeft ctx l m a0 c (TyAbs ap a b) e = do
  ap' <- freshVar
  subLeft
    (CSub ctx ap a)
    l
    m
    a0
    (XCoAt ( (TySubstVar ap')) c)
    (substType (SVar ap (TySubstVar ap') EmptySubst) b)
    e


-- * Old code from here
-- ----------------------------------------------------------------------------

inference :: Expression -> Integer -> Eith ((Type, Target.Expression), Integer)
inference expr maxVar = runState (inferenceWithContext EmptyCtx expr) maxVar


-- | inferenceWithContext
inferenceWithContext :: TypeContext -> Expression -> SubM (Type, Target.Expression)
-- T-TOP
inferenceWithContext _ ExTop = return (( TyTop), Target.ExTop)
-- T-LIT
inferenceWithContext _ (ExLit i) = return (( TyNat), Target.ExLit i)
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
inferenceWithContext _ ExAbs {} = throwError ""


-- | Checking
checking :: TypeContext -> Expression -> Type -> SubM Target.Expression
-- T-ABS
checking c (ExAbs x e) (TyArr a b)
  = do v <- checking (CVar c x a) e b
       return (Target.ExAbs x (elabType a) v)
-- T-SUB
checking c e a
  = do (b, v) <- inferenceWithContext c e
       (co, _) <- subtyping b a
       return (Target.ExCoApp co v)
