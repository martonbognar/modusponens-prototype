{-# OPTIONS_GHC -Wall #-}

module Renamer where

import Control.Monad.State.Lazy

import CommonTypes
import qualified RawSyntax as Raw
import Syntax

new :: State Integer Integer
new = state (\s -> (s, s + 1))

type RnM a = State Integer a

freshVar :: RnM Variable
freshVar = state (\s -> (MkVar s, s + 1))

translateType :: Raw.Type -> Type
translateType Raw.TyNat         = TyNat
translateType Raw.TyTop         = TyTop
translateType (Raw.TyArr t1 t2) = TyArr (translateType t1) (translateType t2)
translateType (Raw.TyIs t1 t2)  = TyIs (translateType t1) (translateType t2)
translateType (Raw.TyRec l t)   = TyRec l (translateType t)

data RnEnv = EmptyRnEnv
           | SnocRnEnv RnEnv Raw.RawVariable Variable

rnLookup :: Raw.RawVariable -> RnEnv -> Maybe Variable
rnLookup _ EmptyRnEnv = Nothing
rnLookup v (SnocRnEnv env v' x)
  | Raw.eqRawVariable v v' = Just x
  | otherwise              = rnLookup v env

rnFullExpr :: RnEnv -> Integer -> Raw.Expression -> (Expression, Integer)
rnFullExpr env state0 ex = runState (rnExpr env ex) state0

rnExpr :: RnEnv -> Raw.Expression -> RnM Expression
rnExpr _ (Raw.ExLit i) = return (ExLit i)
rnExpr _ Raw.ExTop     = return ExTop
rnExpr env (Raw.ExVar x) = case rnLookup x env of
  Nothing -> error $ "Unbound variable " ++ show x -- fail miserably here
  Just y  -> return (ExVar y)

rnExpr env (Raw.ExAbs x e) = do
  y  <- freshVar
  e' <- rnExpr (SnocRnEnv env x y) e
  return (ExAbs y e')

rnExpr env (Raw.ExApp e1 e2) = do
  e1' <- rnExpr env e1
  e2' <- rnExpr env e2
  return (ExApp e1' e2')

rnExpr env (Raw.ExMerge e1 e2) = do
  e1' <- rnExpr env e1
  e2' <- rnExpr env e2
  return (ExMerge e1' e2')

rnExpr env (Raw.ExAnn e t) = do
  e' <- rnExpr env e
  return (ExAnn e' (translateType t))

rnExpr env (Raw.ExRec l e) = do
  e' <- rnExpr env e
  return (ExRec l e')

rnExpr env (Raw.ExRecFld e l) = do
  e' <- rnExpr env e
  return (ExRecFld e' l)
