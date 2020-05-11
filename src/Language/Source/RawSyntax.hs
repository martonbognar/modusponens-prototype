{-# OPTIONS_GHC -Wall #-}

module Language.Source.RawSyntax where

import Prelude hiding ((<>))

import Data.Function (on)
import Data.Label
import Text.PrettyPrint

import PrettyPrinter

newtype RawVariable = MkRawVar { unRawVar :: String }

eqRawVariable :: RawVariable -> RawVariable -> Bool
eqRawVariable = (==) `on` unRawVar

-- * Main Source types
-- ----------------------------------------------------------------------------

data Type
  = TyNat
  | TyTop
  | TyBool
  | TyVar RawVariable
  | TyArr Type Type
  | TyIs Type Type
  | TyAbs RawVariable Type Type
  | TyRec Label Type

data Expression
  = ExLit Integer
  | ExTop
  | ExTrue
  | ExFalse
  | ExVar RawVariable
  | ExAbs RawVariable Expression
  | ExApp Expression Expression
  | ExMerge Expression Expression
  | ExAnn Expression Type
  | ExRec Label Expression
  | ExRecFld Expression Label
  | ExTyAbs RawVariable Type Expression
  | ExTyApp Expression Type

-- * Pretty Printing
-- ----------------------------------------------------------------------------

instance PrettyPrint RawVariable where
  ppr (MkRawVar v) = ppr v

instance PrettyPrint Type where
  ppr TyNat         = ppr "Nat"
  ppr TyTop         = ppr "Unit"
  ppr TyBool        = ppr "Bool"
  ppr (TyVar x)     = ppr x
  ppr (TyArr t1 t2) = parens $ hsep [ppr t1, arrow, ppr t2]
  ppr (TyIs t1 t2)  = parens $ hsep [ppr t1, ppr "&", ppr t2]
  ppr (TyAbs v a b) = parens $ hcat [ppr "\\/", parens (hsep [ppr v, ppr "*", ppr a]), dot, ppr b]
  ppr (TyRec l t)   = braces $ hsep [ppr l, colon, ppr t]

instance PrettyPrint Expression where
  ppr (ExVar v)       = ppr v
  ppr (ExLit i)       = ppr i
  ppr ExTrue          = ppr "True"
  ppr ExFalse         = ppr "False"
  ppr ExTop           = parens empty
  ppr (ExAbs v e)     = parens $ hcat [ppr "\\", ppr v, dot, ppr e]
  ppr (ExApp e1 e2)   = parens $ hsep [ppr e1, ppr e2]
  ppr (ExMerge e1 e2) = parens $ hsep [ppr e1, comma <> comma, ppr e2]
  ppr (ExAnn e t)     = parens $ hsep [ppr e, colon, ppr t]
  ppr (ExRec l e)     = braces $ hsep [ppr l, equals, ppr e]
  ppr (ExRecFld e l)  = hcat [ppr e, dot, ppr l]
  ppr (ExTyAbs v t e) = parens $ hcat [ppr "/\\", parens (hsep [ppr v, ppr "*", ppr t]), dot, ppr e]
  ppr (ExTyApp e t)   = parens $ hsep [ppr e, ppr t]

instance Show RawVariable where
  show = render . ppr

instance Show Type where
  show = render . ppr

instance Show Expression where
  show = render . ppr
