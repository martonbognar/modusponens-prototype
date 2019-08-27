{-# OPTIONS_GHC -Wall #-}

module Renamer where

import Control.Monad.State.Lazy

import CommonTypes
import qualified RawSyntax as Raw
import Syntax

-- | Convert a raw syntax type to a NeColus type.
rnType :: Raw.Type -> Type
rnType Raw.TyNat         = TyNat
rnType Raw.TyTop         = TyTop
rnType (Raw.TyArr t1 t2) = TyArr (rnType t1) (rnType t2)
rnType (Raw.TyIs t1 t2)  = TyIs (rnType t1) (rnType t2)
rnType (Raw.TyRec l t)   = TyRec l (rnType t)

-- | A stack for storing raw - NeColus variable assignments.
data RnEnv = EmptyRnEnv
           | SnocRnEnv RnEnv Raw.RawVariable Variable

-- | Get the NeColus variable for a raw variable in a stack.
rnLookup :: Raw.RawVariable -> RnEnv -> Maybe Variable
rnLookup _ EmptyRnEnv = Nothing
rnLookup v (SnocRnEnv env v' x)
  | Raw.eqRawVariable v v' = Just x
  | otherwise              = rnLookup v env

-- | Covert a full expression from raw syntax to NeColus syntax
-- given an initial stack and state.
rnExpr :: RnEnv -> Integer -> Raw.Expression -> (Expression, Integer)
rnExpr env state0 ex = runState (rnExprM env ex) state0

-- | Convert a raw expression to NeColus syntax.
rnExprM :: RnEnv -> Raw.Expression -> RnM Expression
rnExprM _ (Raw.ExLit i) = return (ExLit i)
rnExprM _ Raw.ExTop     = return ExTop
rnExprM env (Raw.ExVar x) = case rnLookup x env of
  Nothing -> error $ "Unbound variable " ++ show x -- fail miserably here
  Just y  -> return (ExVar y)

rnExprM env (Raw.ExAbs x e) = do
  y  <- freshVar
  e' <- rnExprM (SnocRnEnv env x y) e
  return (ExAbs y e')

rnExprM env (Raw.ExApp e1 e2) = do
  e1' <- rnExprM env e1
  e2' <- rnExprM env e2
  return (ExApp e1' e2')

rnExprM env (Raw.ExMerge e1 e2) = do
  e1' <- rnExprM env e1
  e2' <- rnExprM env e2
  return (ExMerge e1' e2')

rnExprM env (Raw.ExAnn e t) = do
  e' <- rnExprM env e
  return (ExAnn e' (rnType t))

rnExprM env (Raw.ExRec l e) = do
  e' <- rnExprM env e
  return (ExRec l e')

rnExprM env (Raw.ExRecFld e l) = do
  e' <- rnExprM env e
  return (ExRecFld e' l)
