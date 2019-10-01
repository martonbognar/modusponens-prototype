{-# OPTIONS_GHC -Wall #-}

module Data.Label where

import PrettyPrinter

-- | Data type for labels.
newtype Label    = MkLabel String  deriving (Eq)

instance PrettyPrint Label where
  ppr (MkLabel l) = ppr l
