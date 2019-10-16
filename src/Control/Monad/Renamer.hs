{-# OPTIONS_GHC -Wall #-}

module Control.Monad.Renamer where

import qualified Control.Monad.State.Lazy as SM

import Data.Variable

type RnM a = SM.State Integer a

-- | Generate a new, fresh variable.
freshVar :: RnM Variable
freshVar = SM.state (\s -> (MkVar s, s + 1))

runState :: RnM a -> Integer -> (a, Integer)
runState = SM.runState
