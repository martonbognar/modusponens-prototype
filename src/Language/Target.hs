{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveDataTypeable
           , DeriveGeneric
           , MultiParamTypeClasses
           , LambdaCase
  #-}

module Language.Target where

import Prelude hiding ((<>))

import Control.Applicative ((<|>))
import Control.Monad (guard, mzero)
import Control.Monad.Renamer
import Control.Monad.Trans.Maybe
import Data.Label
import Text.PrettyPrint

import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import PrettyPrinter

-- * Main Target types
-- ----------------------------------------------------------------------------

type TypeVar = Name Type

-- | Target types
data Type
  = TyNat
  | TyTop
  | TyBool
  | TyArr Type Type
  | TyTup Type Type
  | TyVar TypeVar
  | TyAll (Bind TypeVar Type)
  | TyRec Label Type
  deriving (Generic)

instance Eq Type where
  TyNat       == TyNat       = True
  TyTop       == TyTop       = True
  TyBool      == TyBool      = True
  TyTup t1 t2 == TyTup t3 t4 = t1 == t3 && t2 == t4
  TyArr t1 t2 == TyArr t3 t4 = t1 == t3 && t2 == t4
  TyRec l1 t1 == TyRec l2 t2 = t1 == t2 && l1 == l2
  _           == _           = False


type TermVar = Name Expression

-- | Target terms
data Expression
  = ExLit Integer
  | ExTop
  | ExVar TermVar
  | ExAbs (Bind TermVar Expression) Type
  | ExApp Expression Expression
  | ExMerge Expression Expression
  | ExCoApp Coercion Expression
  | ExTyAbs (Bind TypeVar Expression)
  | ExTyApp Expression Type
  | ExRec Label Expression
  | ExRecFld Expression Label
  deriving (Generic)

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
  | CoTyAbs (Bind TypeVar Coercion)
  | CoRec Label Coercion
  deriving (Generic)

instance Alpha Type
instance Alpha Expression
instance Alpha Coercion

instance Subst Expression Expression where
  isvar (ExVar v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst Expression Type
instance Subst Expression Coercion
instance Subst Expression Label

data TermContext
  = TermEmpty
  | TermSnoc TermContext TermVar Type

data TypeContext
  = TypeEmpty
  | TypeSnoc TypeContext TypeVar

-- * Pretty Printing
-- ----------------------------------------------------------------------------

instance PrettyPrint Type where
  ppr TyNat         = ppr "Nat"
  ppr TyTop         = ppr "Top"
  ppr TyBool        = ppr "Bool"
  ppr (TyArr t1 t2) = parens $ hsep [ppr t1, arrow, ppr t2]
  ppr (TyTup t1 t2) = parens $ hsep [ppr t1, ppr "✕", ppr t2]
  ppr (TyVar v)     = ppr (name2String v)
  -- ppr (TyAll b)   = ppr b  -- TODO
  ppr (TyRec l t)   = braces $ hsep [ppr l, colon, ppr t]

instance PrettyPrint Expression where
  ppr (ExLit i)       = ppr i
  ppr (ExTop)         = parens empty
  ppr (ExVar v)       = ppr (name2String v)
  -- ppr (ExAbs b t)     = hcat [ppr "\\", parens $ hsep $ [ppr b, colon, ppr t, dot]]  -- TODO
  ppr (ExApp e1 e2)   = parens $ hsep [ppr e1, ppr e2]
  ppr (ExMerge e1 e2) = parens $ hcat [ppr e1, ppr ",,", ppr e2]
  ppr (ExCoApp c e)   = parens $ hsep [ppr c, ppr e]
  -- ppr (ExTyAbs b)   = ppr b  -- TODO
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
  -- ppr (CoTyAbs b)   = ppr b  -- TODO
  ppr (CoRec l c) = braces (hsep [ppr l, colon, ppr c])

instance PrettyPrint TypeContext where
  ppr TypeEmpty        = ppr "•"
  ppr (TypeSnoc c v) = hcat [ppr c, comma, ppr (name2String v)]

instance PrettyPrint TermContext where
  ppr TermEmpty        = ppr "•"
  ppr (TermSnoc c v t) = hcat [ppr c, comma, ppr (name2String v), colon, ppr t]

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


-- | Evaluate a term given the current maximal variable.
eval :: Expression -> Expression
eval t = runFreshM (evalM t)


-- | Fully evaluate a term in signle steps.
evalM :: Expression -> FreshM Expression
evalM t = runMaybeT (step t) >>= \case
  Just st -> evalM st
  Nothing -> return t


-- | Execute small-step reduction on a term.
step :: Expression -> MaybeT FreshM Expression
-- STEP-TOPARR
step (ExApp (ExCoApp CoTopArr ExTop) ExTop) = return ( ExTop)
-- STEP-ARR
step (ExApp (ExCoApp (CoArr c1 c2) v1) e2)
  | isValue v1
  , isValue e2
  = return ( (ExCoApp c2 (ExApp v1 (ExCoApp c1 e2))))
-- STEP-DISTARR
step (ExApp (ExCoApp CoDistArr{} (ExMerge v1 v2)) e2)
  | isValue v1
  , isValue v2
  , isValue e2
  = return ( (ExMerge (ExApp v1 e2) (ExApp v2 e2)))
-- STEP-BETA
step (ExApp (ExAbs b _) e2)
  | isValue e2
  = do
    (x, e) <- unbind b
    return $ subst x e2 e

step (ExApp e1 e2) = app1 <|> app2 where
  app1 = do
    e1' <- step e1
    return ( (ExApp e1' e2))
  app2 = do
    e2' <- step e2
    return ( (ExApp e1 e2'))

-- STEP-PAIR1 & STEP-PAIR2
step (ExMerge e1 e2) = pair1 <|> pair2 where
  pair1 = do
    e1' <- step e1
    return ( (ExMerge e1' e2))
  pair2 = do
    e2' <- step e2
    guard (isValue e1)
    return ( (ExMerge e1 e2'))

-- STEP-PROJRCD
step (ExRecFld (ExRec l v) l1)
  | l == l1
  , isValue v
  = return ( v)


step (ExTyAbs _b) = undefined
step (ExTyApp _e _t) = undefined

-- STEP-RCD1
step (ExRec l e) = do
  e' <- step e
  return ( (ExRec l e'))

-- STEP-RCD2
step (ExRecFld e l) = do
  e' <- step e
  return ( (ExRecFld e' l))

  -- STEP-ID
step (ExCoApp (CoId _) e)
  | isValue e
  = return ( e)
-- STEP-TRANS
step (ExCoApp (CoComp c1 c2) e)
  | isValue e
  = return ( (ExCoApp c1 (ExCoApp c2 e)))
-- SET-TOP
step (ExCoApp (CoTop _) e)
  | isValue e
  = return ( ExTop)
-- STEP-PAIR
step (ExCoApp (CoPair c1 c2) e)
  | isValue e
  = return ( (ExMerge (ExCoApp c1 e) (ExCoApp c2 e)))
-- STEP-PROJL
step (ExCoApp (CoPr1 _ _) (ExMerge v1 v2))
  | isValue v1
  , isValue v2
  = return ( v1)
-- STEP-PROJR
step (ExCoApp (CoPr2 _ _) (ExMerge v1 v2))
  | isValue v1
  , isValue v2
  = return ( v2)

-- STEP-CAPP
step (ExCoApp c e) = do
  e' <- step e
  return ( (ExCoApp c e'))

step (ExLit _) = mzero
step ExTop = mzero
step (ExVar _) = mzero
step (ExAbs _ _) = mzero


-- * Target Typing
-- ----------------------------------------------------------------------------

-- | Get the type of a variable from a context.
typeFromContext :: TermContext -> TermVar -> MaybeT FreshM Type
typeFromContext TermEmpty _ = fail "Variable not in context"
typeFromContext (TermSnoc c v vt) x
  | v == x    = return vt
  | otherwise = typeFromContext c x


-- | In a given context, determine the type of a term.
tcTerm :: Expression -> Maybe Type
tcTerm ex = runFreshM $ runMaybeT (go TermEmpty ex)
  where
    go :: TermContext -> Expression -> MaybeT FreshM Type
    -- TYP-UNIT
    go _ ExTop = return TyTop
    -- TYP-LIT
    go _ (ExLit _) = return TyNat
    -- TYP-ExVar
    go c (ExVar x) = do
      t <- typeFromContext c x
      return t
    -- TYP-ABS
    go c (ExAbs b t1) = do
      (x, e) <- unbind b
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
    go _c (ExTyAbs _b) = undefined
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
tcCoercion :: Coercion -> MaybeT FreshM (Type, Type)
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
tcCoercion (CoTyAbs _b) = undefined
tcCoercion (CoRec _l _c) = undefined
