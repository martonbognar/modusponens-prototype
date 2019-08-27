{-# OPTIONS_GHC -Wall #-}

module CommonTypes where

import Control.Monad.State.Lazy

newtype Variable = MkVar   Integer deriving (Eq)
newtype Label    = MkLabel String  deriving (Eq)

type RnM a = State Integer a

freshVar :: RnM Variable
freshVar = state (\s -> (MkVar s, s + 1))
