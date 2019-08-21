{-# OPTIONS_GHC -Wall #-}

module NeColus where

import Text.PrettyPrint
import PrettyPrinter

type Variable = String
type Label    = String

-- * Main NeColus types
-- ----------------------------------------------------------------------------

data Type
  = TyNat
  | TyTop
  | TyArr Type Type
  | TyIs Type Type
  | TyRec Label Type

data Expression
  = ExVar Variable
  | ExLit Int
  | ExTop
  | ExAbs Variable Expression
  | ExApp Expression Expression
  | ExMerge Expression Expression
  | ExAnn Expression Type
  | ExRec Label Expression
  | ExRecFld Expression Label

data Context
  = Empty
  | Snoc Context Variable Type


-- | Determine equality between two types.
eqTypes :: Type -> Type -> Bool
eqTypes TyNat TyNat                 = True
eqTypes TyTop TyTop                 = True
eqTypes (TyArr t1 t2) (TyArr t3 t4) = eqTypes t1 t3 && eqTypes t2 t4
eqTypes (TyIs t1 t2) (TyIs t3 t4)   = eqTypes t1 t3 && eqTypes t2 t4
eqTypes (TyRec l1 t1) (TyRec l2 t2) = eqTypes t1 t2 && l1 == l2
eqTypes _ _                         = False

-- * Pretty Printing
-- ----------------------------------------------------------------------------

prLabel :: Label -> Doc
prLabel = text


prVariable :: Variable -> Doc
prVariable = text


prType :: Type -> Doc
prType TyNat         = text "Nat"
prType TyTop         = text "Unit"
prType (TyArr t1 t2) = hsep [prType t1, arrow, prType t2]
prType (TyIs t1 t2)  = hsep [prType t1, text "&", prType t2]
prType (TyRec l t)   = braces $ hsep [prLabel l, colon, prType t]


prExp :: Expression -> Doc
prExp (ExVar v)       = prVariable v
prExp (ExLit i)       = int i
prExp ExTop           = parens empty
prExp (ExAbs v e)     = hcat [text "\\", prVariable v, dot, prExp e]
prExp (ExApp e1 e2)   = prExp e1 <+> prExp e2
prExp (ExMerge e1 e2) = hsep [prExp e1, comma, comma, prExp e2]
prExp (ExAnn e t)     = hsep [prExp e, colon, prType t]
prExp (ExRec l e)     = braces $ hsep [prLabel l, equals, prExp e]
prExp (ExRecFld e l)  = hcat [prExp e, dot, prLabel l]


prContext :: Context -> Doc
prContext Empty = text "•"
prContext (Snoc c v t)
  = hcat [prContext c, comma, prVariable v, colon, prType t]

instance Show Type where
  show = render . prType

instance Show Expression where
  show = render . prExp

instance Show Context where
  show = render . prContext
