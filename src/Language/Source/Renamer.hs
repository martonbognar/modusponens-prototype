{-# OPTIONS_GHC -Wall #-}

module Language.Source.Renamer where

import Control.Monad.Renamer
import Data.Variable

import qualified Language.Source.RawSyntax as Raw
import Language.Source.Syntax

-- | Convert a raw syntax type to a Source type.
rnType :: RnEnv -> Raw.Type -> SubM Type
rnType _ Raw.TyNat         = return $ TyNat
rnType _ Raw.TyTop         = return $ TyTop
rnType _ Raw.TyBool        = return $ TyBool
rnType env (Raw.TyVar x)   = case rnLookup x env of
  Nothing -> error $ "Unbound variable " ++ show x -- fail miserably here
  Just y  -> return (TyVar y)
rnType env (Raw.TyArr t1 t2) = do
  t1' <- rnType env t1
  t2' <- rnType env t2
  return $ TyArr t1' t2'
rnType env (Raw.TyIs t1 t2)  = do
  t1' <- rnType env t1
  t2' <- rnType env t2
  return $ TyIs t1' t2'
rnType env (Raw.TyRec l t)   = do
  t' <- rnType env t
  return $ TyRec l t'
rnType env (Raw.TyAbs x a b) = do
  y <- freshVar
  a' <- rnType env a
  b' <- rnType (SnocRnEnv env x y) b
  return $ TyAbs y a' b'

-- | A stack for storing raw - Source variable assignments.
data RnEnv = EmptyRnEnv  -- possible TODO: treat type/term variables separately?
           | SnocRnEnv RnEnv Raw.RawVariable Variable

-- | Get the Source variable for a raw variable in a stack.
rnLookup :: Raw.RawVariable -> RnEnv -> Maybe Variable
rnLookup _ EmptyRnEnv = Nothing
rnLookup v (SnocRnEnv env v' x)
  | Raw.eqRawVariable v v' = Just x
  | otherwise              = rnLookup v env

-- | Covert a full expression from raw syntax to Source syntax
-- given an initial stack and state.
rnExpr :: Raw.Expression -> Eith (Expression, Integer)
rnExpr ex = runState (rnExprM EmptyRnEnv ex) 0

-- | Convert a raw expression to Source syntax.
rnExprM :: RnEnv -> Raw.Expression -> SubM Expression
rnExprM _ (Raw.ExLit i)  = return (ExLit i)
rnExprM _ Raw.ExTop      = return ExTop
rnExprM _ Raw.ExTrue     = return ExTrue
rnExprM _ Raw.ExFalse    = return ExFalse
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
  t' <- rnType env t
  return (ExAnn e' t')

rnExprM env (Raw.ExRec l e) = do
  e' <- rnExprM env e
  return (ExRec l e')

rnExprM env (Raw.ExRecFld e l) = do
  e' <- rnExprM env e
  return (ExRecFld e' l)

rnExprM env (Raw.ExTyAbs x a e) = do
  y  <- freshVar
  a' <- rnType env a
  e' <- rnExprM (SnocRnEnv env x y) e
  return (ExTyAbs y a' e')

rnExprM env (Raw.ExTyApp e t) = do
  e' <- rnExprM env e
  t' <- rnType env t
  return (ExTyApp e' t')
