module Renamer where

import Control.Monad

import CommonTypes
import qualified RawSyntax as Raw
import Syntax

newtype State s a = State { runState :: s -> (a, s) }

instance Functor (State s) where
  fmap transform (State stmt) = State $ \oldState ->
    let (result, newState) = stmt oldState
    in  (transform result, newState)

instance Applicative (State s) where
  pure  = return
  (<*>) = ap

instance Monad (State s) where
  return x = State (\s -> (x, s))
  (>>=) (State stmt) f = State $ \oldState ->
          let (x1, midState) = stmt oldState in
          runState (f x1) midState

new :: State Integer Integer
new = State (\s -> (s, s + 1))

translateType :: Raw.Type -> Type
translateType Raw.TyNat         = TyNat
translateType Raw.TyTop         = TyTop
translateType (Raw.TyArr t1 t2) = TyArr (translateType t1) (translateType t2)
translateType (Raw.TyIs t1 t2)  = TyIs (translateType t1) (translateType t2)
translateType (Raw.TyRec l t)   = TyRec l (translateType t)

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
