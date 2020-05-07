{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE LambdaCase #-}

module Language.Target where

import Prelude hiding ((<>))

import Control.Monad (guard)
import Control.Monad.Renamer
import Data.Label
import Data.Variable
import Text.PrettyPrint

import PrettyPrinter

-- * Main Target types
-- ----------------------------------------------------------------------------

-- | Target types
data Type
  = TyNat
  | TyTop
  | TyBool
  | TyArr Type Type
  | TyTup Type Type
  | TyVar Variable
  | TyAll Variable Type
  | TyRec Label Type

instance Eq Type where
  TyNat       == TyNat       = True
  TyTop       == TyTop       = True
  TyBool      == TyBool      = True
  TyTup t1 t2 == TyTup t3 t4 = t1 == t3 && t2 == t4
  TyArr t1 t2 == TyArr t3 t4 = t1 == t3 && t2 == t4
  TyRec l1 t1 == TyRec l2 t2 = t1 == t2 && l1 == l2
  _           == _           = False

-- | Target terms
data Expression
  = ExLit Integer
  | ExTop
  | ExVar Variable
  | ExAbs Variable Type Expression
  | ExApp Expression Expression
  | ExMerge Expression Expression
  | ExCoApp Coercion Expression
  | ExTyAbs Variable Expression
  | ExTyApp Expression Type
  | ExRec Label Expression
  | ExRecFld Expression Label

-- | Coercions
data Coercion
  = CoId Type
  | CoTop Type
  | CoTopArr
  | CoTopAll
  | CoDistArr Type Type Type
  | CoDistLabel Label Type Type
  | CoPr1 Type Type
  | CoPr2 Type Type
  | CoMP Coercion Coercion
  | CoComp Coercion Coercion
  | CoPair Coercion Coercion
  | CoArr Coercion Coercion
  | CoAt Coercion Type
  | CoTyAbs Variable Coercion
  | CoRec Label Coercion


data TermContext
  = TermEmpty
  | TermSnoc TermContext Variable Type

data TypeContext
  = TypeEmpty
  | TypeSnoc TypeContext Variable

-- * Pretty Printing
-- ----------------------------------------------------------------------------

instance PrettyPrint Type where
  ppr TyNat         = ppr "Nat"
  ppr TyTop         = ppr "Top"
  ppr TyBool        = ppr "Bool"
  ppr (TyArr t1 t2) = parens $ hsep [ppr t1, arrow, ppr t2]
  ppr (TyTup t1 t2) = parens $ hsep [ppr t1, ppr "✕", ppr t2]
  ppr (TyVar v)     = ppr v
  ppr (TyAll v t)   = parens $ hcat [ppr "\\/", ppr v, dot, ppr t]
  ppr (TyRec l t)   = braces $ hsep [ppr l, colon, ppr t]

instance PrettyPrint Expression where
  ppr (ExLit i)       = ppr i
  ppr (ExTop)         = parens empty
  ppr (ExVar v)       = ppr v
  ppr (ExAbs v t e)     = hcat [ppr "\\", parens $ hsep $ [ppr v, colon, ppr t, dot, ppr e]]
  ppr (ExApp e1 e2)   = parens $ hsep [ppr e1, ppr e2]
  ppr (ExMerge e1 e2) = parens $ hcat [ppr e1, ppr ",,", ppr e2]
  ppr (ExCoApp c e)   = parens $ hsep [ppr c, ppr e]
  ppr (ExTyAbs v e)   = parens $ hcat [ppr "/\\", ppr v, dot, ppr e]
  ppr (ExTyApp e t)   = parens $ hsep [ppr e, ppr t]
  ppr (ExRec l e)     = braces $ hsep [ppr l, equals, ppr e]
  ppr (ExRecFld e l)  = hcat [ppr e, dot, ppr l]

instance PrettyPrint Coercion where
  ppr (CoId t)           = ppr "id" <> braces (ppr t)
  ppr (CoTop t)         = ppr "top" <> braces (ppr t)
  ppr CoTopArr             = ppr "top" <> arrow
  ppr CoTopAll             = ppr "top" <> ppr "\\/"
  ppr (CoDistArr t1 t2 t3)
    = hcat [ppr "dist" <> arrow, parensList [
        hcat [ppr t1, arrow, ppr t2],
        hcat [ppr t1, arrow, ppr t3]
      ]]
  ppr (CoDistLabel l t1 t2) = hcat [ppr "dist", braces (ppr l), parensList [ppr t1, ppr t2]]
  ppr (CoPr1 t1 t2)       = hcat [ppr "π₁", parensList [ppr t1, ppr t2]]
  ppr (CoPr2 t1 t2)      = hcat [ppr "π₂", parensList [ppr t1, ppr t2]]
  ppr (CoMP c1 c2)      = hsep [ppr c1, ppr "MP", ppr c2]
  ppr (CoComp c1 c2)      = parens $ hsep [ppr c1, dot, ppr c2]
  ppr (CoPair c1 c2)       = parensList [ppr c1, ppr c2]
  ppr (CoArr c1 c2)        = parens $ hsep [ppr c1, arrow, ppr c2]
  ppr (CoAt c t) = hcat [ppr c, ppr "@", ppr t]
  ppr (CoTyAbs v c)   = parens $ hcat [ppr "/\\", ppr v, dot, ppr c]
  ppr (CoRec l c) = braces (hsep [ppr l, colon, ppr c])

instance PrettyPrint TypeContext where
  ppr TypeEmpty        = ppr "•"
  ppr (TypeSnoc c v) = hcat [ppr c, comma, ppr v]

instance PrettyPrint TermContext where
  ppr TermEmpty        = ppr "•"
  ppr (TermSnoc c v t) = hcat [ppr c, comma, ppr v, colon, ppr t]

instance Show Type where
  show = render . ppr

instance Show TypeContext where
  show = render . ppr

instance Show TermContext where
  show = render . ppr

instance Show Expression where
  show = render . ppr

instance Show Coercion where
  show = render . ppr

-- * Target Operational Semantics
-- ----------------------------------------------------------------------------

-- | Determine whether a term is a target value.
isValue :: Expression -> Bool
isValue ExAbs{}                  = True
isValue ExTop                    = True
isValue (ExLit _)                = True
isValue (ExMerge v1 v2)            = isValue v1 && isValue v2
isValue (ExCoApp CoArr{} v)       = isValue v
isValue (ExCoApp CoDistArr{} v)   = isValue v
isValue (ExCoApp CoTopArr v)      = isValue v
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
refreshTerm :: Expression -> SubM Expression
refreshTerm = go EmptyRefreshEnv
  where
    go :: RefreshEnv -> Expression -> SubM Expression
    go _ (ExLit i)  = return (ExLit i)
    go _ ExTop      = return ExTop
    go env (ExVar x) = case rnLookup x env of
      Nothing -> return (ExVar x)
      Just x' -> return (ExVar x')
    go env (ExAbs b t e) = do
      b' <- freshVar
      e' <- go (SnocRnEnv env b b') e
      return (ExAbs b' t e')
    go env (ExApp e1 e2) = do
      e1' <- go env e1
      e2' <- go env e2
      return (ExApp  e1' e2')
    go env (ExMerge e1 e2) = do
      e1' <- go env e1
      e2' <- go env e2
      return (ExMerge e1' e2')
    go _env (ExTyAbs _v _e) = undefined
    go _env (ExTyApp _e _t) = undefined
    go env (ExRec l e) = do
      e' <- go env e
      return (ExRec l e')
    go env (ExRecFld e l) = do
      e' <- go env e
      return (ExRecFld e' l)
    go env (ExCoApp c e) = do
      e' <- go env e
      return (ExCoApp c e')


subst :: Expression -> Variable -> Expression -> SubM Expression
subst orig var term
  = do term' <- refreshTerm term
       go orig var term'
    where
      go :: Expression -> Variable -> Expression -> SubM Expression
      go expr x v = case expr of
        ExVar x' | x' == x   -> return v
                 | otherwise -> return (ExVar x')
        ExLit i        -> return (ExLit i)
        ExTop          -> return ExTop
        ExAbs b t e -> do
          e' <- go e x v
          return (ExAbs b t e')
        ExApp e1 e2    -> do
          e1' <- go e1 x v
          e2' <- go e2 x v
          return (ExApp  e1' e2')
        ExMerge e1 e2    -> do
          e1' <- go e1 x v
          e2' <- go e2 x v
          return (ExMerge e1' e2')
        ExTyAbs _v _e -> undefined
        ExTyApp _e _t -> undefined
        ExRec l e   -> do
          e' <- go e x v
          return (ExRec l e')
        ExRecFld e l   -> do
          e' <- go e x v
          return (ExRecFld e' l)
        ExCoApp c e     -> do
          e' <- go e x v
          return (ExCoApp c e')


-- | Evaluate a term given the current maximal variable.
eval :: Integer -> Expression -> Eith (Expression, Integer)
eval state0 t = runState (evalM t) state0


-- | Fully evaluate a term in signle steps.
evalM :: Expression -> SubM Expression
evalM t = step t >>= \case
  Just st -> evalM st
  Nothing -> return t


-- | Execute small-step reduction on a term.
step :: Expression -> SubM (Maybe Expression)
-- STEP-TOPARR
step (ExApp (ExCoApp CoTopArr ExTop) ExTop) = return (Just ExTop)
-- STEP-ARR
step (ExApp (ExCoApp (CoArr c1 c2) v1) e2)
  | isValue v1
  , isValue e2
  = return (Just (ExCoApp c2 (ExApp v1 (ExCoApp c1 e2))))
-- STEP-DISTARR
step (ExApp (ExCoApp CoDistArr{} (ExMerge v1 v2)) e2)
  | isValue v1
  , isValue v2
  , isValue e2
  = return (Just (ExMerge (ExApp v1 e2) (ExApp v2 e2)))
-- STEP-BETA
step (ExApp (ExAbs x _ e) e2)
  | isValue e2
  = do
    t <- subst e x e2
    return (Just t)

step (ExApp e1 e2) =
  step e1 >>= \case
-- STEP-APP1
    Just e1' -> return (Just (ExApp e1' e2))
    Nothing -> step e2 >>= \case
-- STEP-APP2
      Just e2' -> if isValue e1
        then return (Just (ExApp e1 e2'))
        else return Nothing
      _                -> return Nothing

-- STEP-PAIR1 & STEP-PAIR2
step (ExMerge e1 e2) =
  step e1 >>= \case
    Just e1' -> return (Just (ExMerge e1' e2))
    Nothing  -> step e2 >>= \case
      Just e2' -> if isValue e1
        then return (Just (ExMerge e1 e2'))
        else return Nothing
      _                -> return Nothing

-- STEP-PROJRCD
step (ExRecFld (ExRec l v) l1)
  | l == l1
  , isValue v
  = return (Just v)


step (ExTyAbs _v _e) = undefined
step (ExTyApp _e _t) = undefined

-- STEP-RCD1
step (ExRec l e) =
  step e >>= \case
    Just e' -> return (Just (ExRec l e'))
    _       -> return Nothing

-- STEP-RCD2
step (ExRecFld e l) =
  step e >>= \case
    Just e' -> return (Just (ExRecFld e' l))
    _       -> return Nothing

  -- STEP-ID
step (ExCoApp (CoId _) e)
  | isValue e
  = return (Just e)
-- STEP-TRANS
step (ExCoApp (CoComp c1 c2) e)
  | isValue e
  = return (Just (ExCoApp c1 (ExCoApp c2 e)))
-- SET-TOP
step (ExCoApp (CoTop _) e)
  | isValue e
  = return (Just ExTop)
-- STEP-PAIR
step (ExCoApp (CoPair c1 c2) e)
  | isValue e
  = return (Just (ExMerge (ExCoApp c1 e) (ExCoApp c2 e)))
-- STEP-PROJL
step (ExCoApp (CoPr1 _ _) (ExMerge v1 v2))
  | isValue v1
  , isValue v2
  = return (Just v1)
-- STEP-PROJR
step (ExCoApp (CoPr2 _ _) (ExMerge v1 v2))
  | isValue v1
  , isValue v2
  = return (Just v2)

-- STEP-CAPP
step (ExCoApp c e) =
  step e >>= \case
    Just e' -> return (Just (ExCoApp c e'))
    _       -> return Nothing

step (ExLit _) = return Nothing
step ExTop = return Nothing
step (ExVar _) = return Nothing
step (ExAbs _ _ _) = return Nothing


-- * Target Typing
-- ----------------------------------------------------------------------------

-- | Get the type of a variable from a context.
typeFromContext :: TermContext -> Variable -> Maybe Type
typeFromContext TermEmpty _ = fail "Variable not in context"
typeFromContext (TermSnoc c v vt) x
  | v == x    = return vt
  | otherwise = typeFromContext c x


-- | In a given context, determine the type of a term.
tcTerm :: Expression -> Maybe Type
tcTerm = go TermEmpty
  where
    go :: TermContext -> Expression -> Maybe Type
    -- TYP-UNIT
    go _ ExTop = return TyTop
    -- TYP-LIT
    go _ (ExLit _) = return TyNat
    -- TYP-ExVar
    go c (ExVar x) = typeFromContext c x
    -- TYP-ABS
    go c (ExAbs x t1 e) = do
      t2 <- go (TermSnoc c x t1) e
      return (TyArr t1 t2)
    -- TYP-APP
    go c (ExApp e1 e2) = do
      (TyArr t1 t2) <- go c e1
      t3            <- go c e2
      guard (t1 == t3)
      return t2
    -- TYP-PAIR
    go c (ExMerge e1 e2) = do
      t1 <- go c e1
      t2 <- go c e2
      return (TyTup t1 t2)
    -- TYP-CAPP
    go c (ExCoApp co e) = do
      t         <- go c e
      (t1, t1') <- tcCoercion co
      guard (t == t1)
      return t1'
    go _c (ExTyAbs _v _e) = undefined
    go _c (ExTyApp _e _t) = undefined
    -- TYP-RCD
    go c (ExRec l e) = do
      t <- go c e
      return (TyRec l t)
    -- TYP--PROJ
    go c (ExRecFld e l) = do
      (TyRec l1 t) <- go c e
      guard (l == l1)
      return t


-- | Determine the type of a coercion.
tcCoercion :: Coercion -> Maybe (Type, Type)
-- COTYP-REFL
tcCoercion (CoId t)
  = return (t, t)
-- COTYP-CoTop
tcCoercion (CoTop t) = return (t, TyTop)
-- COTYP-TOPARR
tcCoercion CoTopArr
  = return (TyTop, TyArr TyTop TyTop)
tcCoercion CoTopAll = undefined
-- COTYP-DISTARR
tcCoercion (CoDistArr t1 t2 t3)
  = return (TyTup (TyArr t1 t2) (TyArr t1 t3), TyArr t1 (TyTup t2 t3))
tcCoercion (CoDistLabel _l _t1 _t2) = undefined
-- COTYP-PROJL
tcCoercion (CoPr1 t1 t2)
  = return (TyTup t1 t2, t1)
-- COTYP-PROJR
tcCoercion (CoPr2 t1 t2)
  = return (TyTup t1 t2, t2)
tcCoercion (CoMP _c1 _c2) = undefined
-- COTYP-TRANS
tcCoercion (CoComp c1 c2)
  = do (t2, t3)  <- tcCoercion c1
       (t1, t2') <- tcCoercion c2
       guard (t2 == t2')
       return (t1, t3)
-- COTYP-PAIR
tcCoercion (CoPair c1 c2)
  = do (t1, t2)  <- tcCoercion c1
       (t1', t3) <- tcCoercion c2
       guard (t1 == t1')
       return (t1, TyTup t2 t3)
-- COTYP-ARR
tcCoercion (CoArr c1 c2)
  = do (t1', t1) <- tcCoercion c1
       (t2, t2') <- tcCoercion c2
       return (TyArr t1 t2, TyArr t1' t2')
tcCoercion (CoAt _c _t) = undefined
tcCoercion (CoTyAbs _v _c) = undefined
tcCoercion (CoRec _l _c) = undefined
