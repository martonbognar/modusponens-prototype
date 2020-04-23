{-# OPTIONS_GHC -Wall #-}

module Language.NeColus.Syntax where

import Prelude hiding ((<>))

import Data.Label
import Data.Variable
import Text.PrettyPrint

import PrettyPrinter

-- * Main NeColus types
-- ----------------------------------------------------------------------------

data Monotype
  = TyNat
  | TyTop
  | TyVar Variable
  | TyMonoArr Monotype Monotype
  | TyMonoIs Monotype Monotype

data Type
  = TyMono Monotype
  | TyArr Type Type
  | TyIs Type Type
  | TyAbs Variable Type Type
  | TyRec Label Type
  | TySubstVar Variable -- should only be used during typechecking

data Expression
  = ExLit Integer
  | ExTop
  | ExVar Variable
  | ExAbs Variable Expression
  | ExApp Expression Expression
  | ExMerge Expression Expression
  | ExAnn Expression Type
  | ExTyAbs Variable Type Expression
  | ExTyApp Expression Type
  | ExRec Label Expression
  | ExRecFld Expression Label

-- data SubstitutionVariable = SubstVar Variable

data TypeContext
  = Empty
  | VarSnoc TypeContext Variable Type
  | SubstSnoc TypeContext Variable Type


-- | The queue for implementing algorithmic subtyping rules.
data Queue
  = Null
  -- | ExtraLabel Queue Label
  | ExtraType Queue Type


data Substitution
  = EmptySubst
  | Cons Variable Type Substitution


-- | Check whether a queue is empty.
isNullQueue :: Queue -> Bool
isNullQueue Null = True
isNullQueue _    = False
{-# INLINE isNullQueue #-}

-- | Get the first element and the tail of the queue as a tuple.
viewL :: Queue -> Maybe (Either Label Type, Queue)
viewL Null = Nothing
-- viewL (ExtraLabel q l)
--   | isNullQueue q = return (Left l, Null)
--   | otherwise     = do (res, queue) <- viewL q
--                        return (res, ExtraLabel queue l)
viewL (ExtraType q t)
  | isNullQueue q = return (Right t, Null)
  | otherwise     = do (res, queue) <- viewL q
                       return (res, ExtraType queue t)

-- appendLabel :: Queue -> Label -> Queue
-- appendLabel Null l = ExtraLabel Null l
-- appendLabel (ExtraLabel q l') l = ExtraLabel (appendLabel q l) l'
-- appendLabel (ExtraType q t) l = ExtraType (appendLabel q l) t

appendType :: Queue -> Type -> Queue
appendType Null t = ExtraType Null t
-- appendType (ExtraLabel q l) t = ExtraLabel (appendType q t) l
appendType (ExtraType q t') t = ExtraType (appendType q t) t'

-- * Pretty Printing
-- ----------------------------------------------------------------------------

instance PrettyPrint Monotype where
  ppr TyNat             = ppr "Nat"
  ppr TyTop             = ppr "Top"
  ppr (TyVar v)         = ppr v
  ppr (TyMonoArr t1 t2) = parens $ hsep [ppr t1, arrow, ppr t2]
  ppr (TyMonoIs t1 t2)  = parens $ hsep [ppr t1, ppr "&", ppr t2]

instance PrettyPrint Type where
  ppr (TyMono t)      = ppr t
  ppr (TyArr t1 t2)   = parens $ hsep [ppr t1, arrow, ppr t2]
  ppr (TyIs t1 t2)    = parens $ hsep [ppr t1, ppr "&", ppr t2]
  ppr (TyAbs v t1 t2) = parens $ hcat [ppr "\\/", parens (hsep [ppr v, ppr "*", ppr t1]), dot, ppr t2]
  ppr (TyRec l t)     = braces $ hsep [ppr l, colon, ppr t]

instance PrettyPrint Expression where
  ppr (ExLit i)       = ppr i
  ppr ExTop           = parens empty
  ppr (ExVar v)       = ppr v
  ppr (ExAbs v e)     = parens $ hcat [ppr "\\", ppr v, dot, ppr e]
  ppr (ExApp e1 e2)   = parens $ hsep [ppr e1, ppr e2]
  ppr (ExMerge e1 e2) = parens $ hsep [ppr e1, comma <> comma, ppr e2]
  ppr (ExAnn e t)     = parens $ hsep [ppr e, colon, ppr t]
  ppr (ExTyAbs v t e) = parens $ hcat [ppr "/\\", parens (hsep [ppr v, ppr "*", ppr t]), dot, ppr e]
  ppr (ExTyApp e t)   = parens $ hsep [ppr e, ppr t]
  ppr (ExRec l e)     = braces $ hsep [ppr l, equals, ppr e]
  ppr (ExRecFld e l)  = hcat [ppr e, dot, ppr l]

instance PrettyPrint TypeContext where
  ppr Empty        = ppr "•"
  ppr (VarSnoc c v t) = hcat [ppr c, comma, ppr v, colon, ppr t]

instance Show Type where
  show = render . ppr

instance Show Expression where
  show = render . ppr

instance Show TypeContext where
  show = render . ppr
