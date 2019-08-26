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
rnFullExpr env state0 exp = runState (rnExpr env exp) state0



rnExpr :: RnEnv -> Raw.Expression -> RnM Expression
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

  -- ...add the rest of the cases here




renameH :: Raw.Expression -> Integer -> (Expression, Integer)
renameH fullE s = case fullE of
  (Raw.ExVar (Raw.MkRawVar v))   ->
    (ExVar (MkVar x), s') where
      (x, s') = runState new s
  (Raw.ExLit i)                  ->
    (ExLit i, s)
  Raw.ExTop                      ->
    (ExTop, s)
  (Raw.ExAbs (Raw.MkRawVar v) e) ->
    (ExAbs (MkVar x) e', s'') where
      (x, s')   = runState new s
      (e', s'') = renameH e s'
  (Raw.ExApp e1 e2)              ->
    (ExApp e1' e2', s') where
      (e1', s1') = renameH e1 s
      (e2', s')  = renameH e2 s1'
  (Raw.ExMerge e1 e2)            ->
    (ExMerge e1' e2', s') where
      (e1', s1') = renameH e1 s
      (e2', s')  = renameH e2 s1'
  (Raw.ExAnn e t)                ->
    (ExAnn e' (translateType t), s') where
      (e', s') = renameH e s
  (Raw.ExRec l e)                ->
    (ExRec l e', s') where
      (e', s') = renameH e s
  (Raw.ExRecFld e l)             ->
    (ExRecFld e' l, s') where
      (e', s') = renameH e s

rename :: Raw.Expression -> Expression
rename ex = ex' where (ex', _) = renameH ex 0
