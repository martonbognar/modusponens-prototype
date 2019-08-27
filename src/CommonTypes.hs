{-# OPTIONS_GHC -Wall #-}

module CommonTypes where

import Control.Monad.Trans.State.Lazy

-- | Data type for variables in NeColus and LambdaC.
newtype Variable = MkVar   Integer deriving (Eq)

-- | Data type for labels in NeColus and LambdaC.
newtype Label    = MkLabel String  deriving (Eq)

type RnM a = State Integer a

-- | Generate a new, fresh variable.
freshVar :: RnM Variable
freshVar = state (\s -> (MkVar s, s + 1))
