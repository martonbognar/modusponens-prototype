{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE LambdaCase #-}

module Language.LambdaC where

import Prelude hiding ((<>))

import Control.Monad (guard)
import Control.Monad.Renamer
import Data.Label
import Data.Variable
import Text.PrettyPrint

import PrettyPrinter

-- * Main LambdaC types
-- ----------------------------------------------------------------------------

-- | Target types
data Type
  = TyNat
  | TyBool
  | TyTop
  | TyTup Type Type
  | TyArr Type Type
  | TyRec Label Type

-- | Typing contexts
data Context
  = Empty
  | Snoc Context Variable Type

-- | Target terms
data Term
  = TmVar Variable
  | TmLit Integer
  | TmBool Bool
  | TmTop
  | TmAbs Variable Type Term
  | TmApp Term Term
  | TmTup Term Term
  | TmRecCon Label Term
  | TmRecFld Term Label
  | TmCast Coercion Term

-- | Coercions
data Coercion
  = CoRefl Type
  | CoTrans Coercion Coercion
  | CoAnyTop Type
  | CoTopArr
  | CoTopRec Label
  | CoArr Coercion Coercion
  | CoPair Coercion Coercion
  | CoLeft Type Type
  | CoRight Type Type
  | CoRec Label Coercion
  | CoDistRec Label Type Type
  | CoDistArr Type Type Type
  | CoMP Coercion Coercion

-- | Determine equality between two types.
eqTypes :: Type -> Type -> Bool
eqTypes TyNat  TyNat                = True
eqTypes TyBool TyBool               = True
eqTypes TyTop  TyTop                = True
eqTypes (TyTup t1 t2) (TyTup t3 t4) = eqTypes t1 t3 && eqTypes t2 t4
eqTypes (TyArr t1 t2) (TyArr t3 t4) = eqTypes t1 t3 && eqTypes t2 t4
eqTypes (TyRec l1 t1) (TyRec l2 t2) = eqTypes t1 t2 && l1 == l2
eqTypes _ _                         = False

-- * Pretty Printing
-- ----------------------------------------------------------------------------

instance PrettyPrint Type where
  ppr TyNat         = ppr "Nat"
  ppr TyBool        = ppr "Bool"
  ppr TyTop         = ppr "Unit"
  ppr (TyTup t1 t2) = parens $ hsep [ppr t1, ppr "✕", ppr t2]
  ppr (TyArr t1 t2) = parens $ hsep [ppr t1, arrow, ppr t2]
  ppr (TyRec l t)   = braces $ hsep [ppr l, colon, ppr t]

instance PrettyPrint Context where
  ppr Empty        = ppr "•"
  ppr (Snoc c v t) = hcat [ppr c, comma, ppr v, colon, ppr t]

instance PrettyPrint Term where
  ppr (TmVar v)      = ppr v
  ppr (TmLit i)      = ppr i
  ppr (TmBool b)     = ppr b
  ppr TmTop          = parens empty
  ppr (TmAbs v vt t)
    = hcat [ppr "\\", parens $ hsep [ppr v, colon, ppr vt], ppr t]
  ppr (TmApp t1 t2)  = parens $ hsep [ppr t1, ppr t2]
  ppr (TmTup t1 t2)  = parensList [ppr t1, ppr t2]
  ppr (TmRecCon l t) = braces $ hsep [ppr l, equals, ppr t]
  ppr (TmRecFld t l) = hcat [ppr t, dot, ppr l]
  ppr (TmCast c t)   = parens $ hsep [ppr c, ppr t]

instance PrettyPrint Coercion where
  ppr (CoRefl t)           = ppr "id" <> braces (ppr t)
  ppr (CoTrans c1 c2)      = parens $ hsep [ppr c1, dot, ppr c2]
  ppr (CoAnyTop t)         = ppr "top" <> braces (ppr t)
  ppr CoTopArr             = ppr "top" <> arrow
  ppr (CoTopRec l)         = ppr "top" <> braces (ppr l)
  ppr (CoArr c1 c2)        = parens $ hsep [ppr c1, arrow, ppr c2]
  ppr (CoPair c1 c2)       = parensList [ppr c1, ppr c2]
  ppr (CoLeft t1 t2)       = hcat [ppr "π₁", parensList [ppr t1, ppr t2]]
  ppr (CoRight t1 t2)      = hcat [ppr "π₂", parensList [ppr t1, ppr t2]]
  ppr (CoRec l c)          = braces $ hsep [ppr l, colon, ppr c]
  ppr (CoDistRec l t1 t2)
    = hsep [ppr "dist", braces $ hcat [
        ppr l,
        parensList [ppr t1, ppr t2]
      ]]
  ppr (CoDistArr t1 t2 t3)
    = hcat [ppr "dist" <> arrow, parensList [
        hcat [ppr t1, arrow, ppr t2],
        hcat [ppr t1, arrow, ppr t3]
      ]]
  ppr (CoMP c1 c2) = hcat [ppr c1, ppr "MP", ppr c2]

instance Show Type where
  show = render . ppr

instance Show Context where
  show = render . ppr

instance Show Term where
  show = render . ppr

instance Show Coercion where
  show = render . ppr

-- * LambdaC Operational Semantics
-- ----------------------------------------------------------------------------

-- | Determine whether a term is a target value.
isValue :: Term -> Bool
isValue TmAbs{}                  = True
isValue TmTop                    = True
isValue (TmLit _)                = True
isValue (TmBool _)               = True
isValue (TmTup v1 v2)            = isValue v1 && isValue v2
isValue (TmCast CoArr{} v)       = isValue v
isValue (TmCast CoDistArr{} v)   = isValue v
isValue (TmCast CoTopArr v)      = isValue v
isValue _                        = False


data RefreshEnv
  = EmptyRefreshEnv
  | SnocRnEnv RefreshEnv Variable Variable


rnLookup :: Variable -> RefreshEnv -> Maybe Variable
rnLookup _ EmptyRefreshEnv = Nothing
rnLookup v (SnocRnEnv env v' x)
  | v == v'   = Just x
  | otherwise = rnLookup v env


-- | Replace a variable in a term with a fresh one.
refreshTerm :: Term -> RnM Term
refreshTerm = go EmptyRefreshEnv
  where
    go :: RefreshEnv -> Term -> RnM Term
    go _ (TmLit i)  = return (TmLit i)
    go _ (TmBool b) = return (TmBool b)
    go _ TmTop      = return TmTop
    go env (TmVar x) = case rnLookup x env of
      Nothing -> return (TmVar x)
      Just x' -> return (TmVar x')
    go env (TmAbs b t e) = do
      b' <- freshVar
      e' <- go (SnocRnEnv env b b') e
      return (TmAbs b' t e')
    go env (TmApp e1 e2) = do
      e1' <- go env e1
      e2' <- go env e2
      return (TmApp  e1' e2')
    go env (TmTup e1 e2) = do
      e1' <- go env e1
      e2' <- go env e2
      return (TmTup e1' e2')
    go env (TmRecCon l e) = do
      e' <- go env e
      return (TmRecCon l e')
    go env (TmRecFld e l) = do
      e' <- go env e
      return (TmRecFld e' l)
    go env (TmCast c e) = do
      e' <- go env e
      return (TmCast c e')


subst :: Term -> Variable -> Term -> RnM Term
subst orig var term
  = do term' <- refreshTerm term
       go orig var term'
    where
      go :: Term -> Variable -> Term -> RnM Term
      go expr x v = case expr of
        TmVar x' | x' == x   -> return v
                 | otherwise -> return (TmVar x')
        TmLit i        -> return (TmLit i)
        TmBool b       -> return (TmBool b)
        TmTop          -> return TmTop
        TmAbs b t e -> do
          e' <- go e x v
          return (TmAbs b t e')
        TmApp e1 e2    -> do
          e1' <- go e1 x v
          e2' <- go e2 x v
          return (TmApp  e1' e2')
        TmTup e1 e2    -> do
          e1' <- go e1 x v
          e2' <- go e2 x v
          return (TmTup e1' e2')
        TmRecCon l e   -> do
          e' <- go e x v
          return (TmRecCon l e')
        TmRecFld e l   -> do
          e' <- go e x v
          return (TmRecFld e' l)
        TmCast c e     -> do
          e' <- go e x v
          return (TmCast c e')


-- | Evaluate a term given the current maximal variable.
eval :: Integer -> Term -> (Term, Integer)
eval state0 t = runState (evalM t) state0


-- | Fully evaluate a term in signle steps.
evalM :: Term -> RnM Term
evalM t = step t >>= \case
  Just st -> evalM st
  Nothing -> return t


-- | Execute small-step reduction on a term.
step :: Term -> RnM (Maybe Term)
-- STEP-TOPARR
step (TmApp (TmCast CoTopArr TmTop) TmTop) = return (Just TmTop)
-- STEP-ARR
step (TmApp (TmCast (CoArr c1 c2) v1) e2)
  | isValue v1
  , isValue e2
  = return (Just (TmCast c2 (TmApp v1 (TmCast c1 e2))))
-- STEP-DISTARR
step (TmApp (TmCast CoDistArr{} (TmTup v1 v2)) e2)
  | isValue v1
  , isValue v2
  , isValue e2
  = return (Just (TmTup (TmApp v1 e2) (TmApp v2 e2)))
-- STEP-BETA
step (TmApp (TmAbs x _ e) e2)
  | isValue e2
  = do
    t <- subst e x e2
    return (Just t)

step (TmApp e1 e2) =
  step e1 >>= \case
-- STEP-APP1
    Just e1' -> return (Just (TmApp e1' e2))
    Nothing -> step e2 >>= \case
-- STEP-APP2
      Just e2' -> if isValue e1
        then return (Just (TmApp e1 e2'))
        else return Nothing
      _                -> return Nothing

-- STEP-PAIR1 & STEP-PAIR2
step (TmTup e1 e2) =
  step e1 >>= \case
    Just e1' -> return (Just (TmTup e1' e2))
    Nothing  -> step e2 >>= \case
      Just e2' -> if isValue e1
        then return (Just (TmTup e1 e2'))
        else return Nothing
      _                -> return Nothing

-- STEP-PROJRCD
step (TmRecFld (TmRecCon l v) l1)
  | l == l1
  , isValue v
  = return (Just v)

-- STEP-RCD1
step (TmRecCon l e) =
  step e >>= \case
    Just e' -> return (Just (TmRecCon l e'))
    _       -> return Nothing

-- STEP-RCD2
step (TmRecFld e l) =
  step e >>= \case
    Just e' -> return (Just (TmRecFld e' l))
    _       -> return Nothing

  -- STEP-ID
step (TmCast (CoRefl _) e)
  | isValue e
  = return (Just e)
-- STEP-TRANS
step (TmCast (CoTrans c1 c2) e)
  | isValue e
  = return (Just (TmCast c1 (TmCast c2 e)))
-- SET-TOP
step (TmCast (CoAnyTop _) e)
  | isValue e
  = return (Just TmTop)
-- STEP-TOPRCD
step (TmCast (CoTopRec l) TmTop)
  = return (Just (TmRecCon l TmTop))
-- STEP-PAIR
step (TmCast (CoPair c1 c2) e)
  | isValue e
  = return (Just (TmTup (TmCast c1 e) (TmCast c2 e)))
-- STEP-DISTRCD
step (TmCast (CoDistRec l _ _) (TmTup (TmRecCon l1 v1) (TmRecCon l2 v2)))
  | isValue v1
  , isValue v2
  = if l == l1 && l1 == l2
      then return (Just (TmRecCon l (TmTup v1 v2)))
      else return Nothing
-- STEP-PROJL
step (TmCast (CoLeft _ _) (TmTup v1 v2))
  | isValue v1
  , isValue v2
  = return (Just v1)
-- STEP-PROJR
step (TmCast (CoRight _ _) (TmTup v1 v2))
  | isValue v1
  , isValue v2
  = return (Just v2)
-- STEP-CRCD
step (TmCast (CoRec l co) (TmRecCon l1 v))
  | isValue v
  = if l == l1
      then return (Just (TmRecCon l (TmCast co v)))
      else return Nothing
-- STEP-MP
step (TmCast (CoMP c1 c2) e)
  | isValue e
  = return (Just (TmApp (TmCast c1 e) (TmCast c2 e)))

-- STEP-CAPP
step (TmCast c e) =
  step e >>= \case
    Just e' -> return (Just (TmCast c e'))
    _       -> return Nothing

step _ = return Nothing

-- * LambdaC Typing
-- ----------------------------------------------------------------------------

-- | Get the type of a variable from a context.
typeFromContext :: Context -> Variable -> Maybe Type
typeFromContext Empty _ = fail "Variable not in context"
typeFromContext (Snoc c v vt) x
  | v == x    = return vt
  | otherwise = typeFromContext c x


-- | In a given context, determine the type of a term.
tcTerm :: Term -> Maybe Type
tcTerm = go Empty
  where
    go :: Context -> Term -> Maybe Type
    -- TYP-UNIT
    go _ TmTop = return TyTop
    -- TYP-LIT
    go _ (TmLit _) = return TyNat
    -- TYP-BOOL
    go _ (TmBool _) = return TyBool
    -- TYP-TmVar
    go c (TmVar x) = typeFromContext c x
    -- TYP-ABS
    go c (TmAbs x t1 e) = do
      t2 <- go (Snoc c x t1) e
      return (TyArr t1 t2)
    -- TYP-APP
    go c (TmApp e1 e2) = do
      (TyArr t1 t2) <- go c e1
      t3            <- go c e2
      guard (eqTypes t1 t3)
      return t2
    -- TYP-PAIR
    go c (TmTup e1 e2) = do
      t1 <- go c e1
      t2 <- go c e2
      return (TyTup t1 t2)
    -- TYP-CAPP
    go c (TmCast co e) = do
      t         <- go c e
      (t1, t1') <- tcCoercion co
      guard (eqTypes t t1)
      return t1'
    -- TYP-RCD
    go c (TmRecCon l e) = do
      t <- go c e
      return (TyRec l t)
    -- TYP--PROJ
    go c (TmRecFld e l) = do
      (TyRec l1 t) <- go c e
      guard (l == l1)
      return t


-- | Determine the type of a coercion.
tcCoercion :: Coercion -> Maybe (Type, Type)
-- COTYP-REFL
tcCoercion (CoRefl t)
  = return (t, t)
-- COTYP-TRANS
tcCoercion (CoTrans c1 c2)
  = do (t2, t3)  <- tcCoercion c1
       (t1, t2') <- tcCoercion c2
       guard (eqTypes t2 t2')
       return (t1, t3)
-- COTYP-CoAnyTop
tcCoercion (CoAnyTop t) = return (t, TyTop)
-- COTYP-TOPARR
tcCoercion CoTopArr
  = return (TyTop, TyArr TyTop TyTop)
-- COTYP-TOPRCD
tcCoercion (CoTopRec l)
  = return (TyTop, TyRec l TyTop)
-- COTYP-ARR
tcCoercion (CoArr c1 c2)
  = do (t1', t1) <- tcCoercion c1
       (t2, t2') <- tcCoercion c2
       return (TyArr t1 t2, TyArr t1' t2')
-- COTYP-PAIR
tcCoercion (CoPair c1 c2)
  = do (t1, t2)  <- tcCoercion c1
       (t1', t3) <- tcCoercion c2
       guard (eqTypes t1 t1')
       return (t1, TyTup t2 t3)
-- COTYP-PROJL
tcCoercion (CoLeft t1 t2)
  = return (TyTup t1 t2, t1)
-- COTYP-PROJR
tcCoercion (CoRight t1 t2)
  = return (TyTup t1 t2, t2)
-- COTYP-RCD
tcCoercion (CoRec l c)
  = do (t1, t2) <- tcCoercion c
       return (TyRec l t1, TyRec l t2)
-- COTYP-DISTRCD
tcCoercion (CoDistRec l t1 t2)
  = return (TyTup (TyRec l t1) (TyRec l t2), TyRec l (TyTup t1 t2))
-- COTYP-DISTARR
tcCoercion (CoDistArr t1 t2 t3)
  = return (TyTup (TyArr t1 t2) (TyArr t1 t3), TyArr t1 (TyTup t2 t3))
-- COPYT-MODUSPONENS
tcCoercion (CoMP c1 c2)
  = do (t, TyArr t1 t2) <- tcCoercion c1
       (t', t1') <- tcCoercion c2
       guard (eqTypes t t' && eqTypes t1 t1')
       return (t, t2)
