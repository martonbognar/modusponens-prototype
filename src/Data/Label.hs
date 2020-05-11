{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveDataTypeable
           , DeriveGeneric
           , MultiParamTypeClasses
  #-}

module Data.Label where

import PrettyPrinter
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless

-- | Data type for labels.
newtype Label    = MkLabel String  deriving (Show, Eq, Generic)

instance PrettyPrint Label where
  ppr (MkLabel l) = ppr l

instance Alpha Label
