{-# OPTIONS_GHC -Wall #-}

module Language.NeColus.Syntax where

import Prelude hiding ((<>))

import Control.Monad.Trans.State.Lazy
import Text.PrettyPrint

import PrettyPrinter

-- * Main NeColus types
-- ----------------------------------------------------------------------------

-- | Data type for variables.
newtype Variable = MkVar   Integer deriving (Eq)

-- | Data type for labels.
newtype Label    = MkLabel String  deriving (Eq)


data Type
  = TyNat
  | TyTop
  | TyArr Type Type
  | TyIs Type Type
  | TyRec Label Type

data Expression
  = ExVar Variable
  | ExLit Integer
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


-- | The queue for implementing algorithmic subtyping rules.
data Queue
  = Null
  | ExtraLabel Queue Label
  | ExtraType Queue Type

-- | Check whether a queue is empty.
isNullQueue :: Queue -> Bool
isNullQueue Null = True
isNullQueue _    = False
{-# INLINE isNullQueue #-}

-- | Get the first element and the tail of the queue as a tuple.
viewL :: Queue -> Maybe (Either Label Type, Queue)
viewL Null = Nothing
viewL (ExtraLabel q l)
  | isNullQueue q = return (Left l, Null)
  | otherwise     = do (res, queue) <- viewL q
                       return (res, ExtraLabel queue l)
viewL (ExtraType q t)
  | isNullQueue q = return (Right t, Null)
  | otherwise     = do (res, queue) <- viewL q
                       return (res, ExtraType queue t)

-- * Pretty Printing
-- ----------------------------------------------------------------------------

instance PrettyPrint Variable where
  ppr (MkVar i) = ppr "x" <> ppr i

instance PrettyPrint Label where
  ppr (MkLabel l) = ppr l

instance PrettyPrint Type where
  ppr TyNat         = ppr "Nat"
  ppr TyTop         = ppr "Unit"
  ppr (TyArr t1 t2) = parens $ hsep [ppr t1, arrow, ppr t2]
  ppr (TyIs t1 t2)  = parens $ hsep [ppr t1, ppr "&", ppr t2]
  ppr (TyRec l t)   = braces $ hsep [ppr l, colon, ppr t]

instance PrettyPrint Expression where
  ppr (ExVar v)       = ppr v
  ppr (ExLit i)       = ppr i
  ppr ExTop           = parens empty
  ppr (ExAbs v e)     = parens $ hcat [ppr "\\", ppr v, dot, ppr e]
  ppr (ExApp e1 e2)   = parens $ hsep [ppr e1, ppr e2]
  ppr (ExMerge e1 e2) = parens $ hsep [ppr e1, comma <> comma, ppr e2]
  ppr (ExAnn e t)     = parens $ hsep [ppr e, colon, ppr t]
  ppr (ExRec l e)     = braces $ hsep [ppr l, equals, ppr e]
  ppr (ExRecFld e l)  = hcat [ppr e, dot, ppr l]

instance PrettyPrint Context where
  ppr Empty        = ppr "•"
  ppr (Snoc c v t) = hcat [ppr c, comma, ppr v, colon, ppr t]

instance Show Type where
  show = render . ppr

instance Show Expression where
  show = render . ppr

instance Show Context where
  show = render . ppr
