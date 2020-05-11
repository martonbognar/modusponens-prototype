{-# OPTIONS_GHC -Wall #-}

module Language.Source.Renamer where

import Control.Monad.Renamer
import Control.Monad.Trans.Maybe
import Data.Variable
import Unbound.Generics.LocallyNameless

import qualified Language.Source.RawSyntax as Raw
import Language.Source.Syntax

-- | Convert a raw syntax type to a Source type.
rnType :: RnEnv -> Raw.Type -> MaybeT FreshM Type
rnType _ Raw.TyNat         = return $ TyNat
rnType _ Raw.TyTop         = return $ TyTop
rnType _ Raw.TyBool        = return $ TyBool
rnType env (Raw.TyVar x)   = case rnLookupTy x env of
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
  y <- fresh (string2Name $ show x)
  a' <- rnType env a
  b' <- rnType (SnocRnTyEnv env x y) b
  return $ TyAbs (bind y b') a'

-- | A stack for storing raw - Source variable assignments.
data RnEnv = EmptyRnEnv  -- possible TODO: treat type/term variables separately?
           | SnocRnTyEnv RnEnv Raw.RawVariable TypeVar
           | SnocRnTmEnv RnEnv Raw.RawVariable TermVar

-- | Get the Source variable for a raw variable in a stack.
rnLookupTm :: Raw.RawVariable -> RnEnv -> Maybe TermVar
rnLookupTm _ EmptyRnEnv = Nothing
rnLookupTm v (SnocRnTmEnv env v' x)
  | Raw.eqRawVariable v v' = Just x
  | otherwise              = rnLookupTm v env

-- | Get the Source variable for a raw variable in a stack.
rnLookupTy :: Raw.RawVariable -> RnEnv -> Maybe TypeVar
rnLookupTy _ EmptyRnEnv = Nothing
rnLookupTy v (SnocRnTyEnv env v' x)
  | Raw.eqRawVariable v v' = Just x
  | otherwise              = rnLookupTy v env

-- | Covert a full expression from raw syntax to Source syntax
-- given an initial stack and state.
rnExpr :: Raw.Expression -> Maybe (Expression)
rnExpr ex = runFreshM $ runMaybeT (rnExprM EmptyRnEnv ex)

-- | Convert a raw expression to Source syntax.
rnExprM :: RnEnv -> Raw.Expression -> MaybeT FreshM Expression
rnExprM _ (Raw.ExLit i)  = return (ExLit i)
rnExprM _ Raw.ExTop      = return ExTop
rnExprM _ Raw.ExTrue     = return ExTrue
rnExprM _ Raw.ExFalse    = return ExFalse
rnExprM env (Raw.ExVar x) = case rnLookupTm x env of
  Nothing -> error $ "Unbound variable " ++ show x -- fail miserably here
  Just y  -> return (ExVar y)

rnExprM env (Raw.ExAbs x e) = do
  y  <- fresh (string2Name $ show x)
  e' <- rnExprM (SnocRnTmEnv env x y) e
  return (ExAbs (bind y e'))

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
  y  <- fresh (string2Name $ show x)
  a' <- rnType env a
  e' <- rnExprM (SnocRnTyEnv env x y) e
  return (ExTyAbs (bind y e') a')

rnExprM env (Raw.ExTyApp e t) = do
  e' <- rnExprM env e
  t' <- rnType env t
  return (ExTyApp e' t')
