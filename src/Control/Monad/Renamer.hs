{-# OPTIONS_GHC -Wall #-}

module Control.Monad.Renamer where

import qualified Control.Monad.State.Lazy as SM
import qualified Control.Monad.Except as EM

import Data.Variable

type Eith = EM.Except String

type SubM = SM.StateT Integer Eith

-- | Generate a new, fresh variable.
freshVar :: SubM Variable
freshVar = SM.state (\s -> (MkVar s, s + 1))

runState :: SubM a -> Integer -> Eith(a, Integer)
runState = SM.runStateT
