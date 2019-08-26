{-# OPTIONS_GHC -Wall #-}

module CommonTypes where

data Variable = MkVar   Integer deriving (Eq)
data Label    = MkLabel String  deriving (Eq)
