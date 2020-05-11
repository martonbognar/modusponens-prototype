{-# OPTIONS_GHC -Wall #-}

module Data.Variable where

import Data.Semigroup ((<>))

import PrettyPrinter
import Text.PrettyPrint (render)

-- | Data type for variables.
newtype Variable = MkVar   Integer deriving (Eq)

instance PrettyPrint Variable where
  ppr (MkVar i) = ppr "x" <> ppr i

instance Show Variable where
  show = render . ppr
