{-# OPTIONS_GHC -Wall #-}

module Language.Source.Syntax where

import Prelude hiding ((<>))

import Data.Label
import Data.Variable
import Text.PrettyPrint
import Control.Monad.Renamer
import Control.Monad.Except

import PrettyPrinter

-- * Main Source types
-- ----------------------------------------------------------------------------

data Type
  = TyNat
  | TyTop
  | TyBool
  | TyVar Variable
  | TySubstVar Variable  -- should only be used during typechecking
  | TyArr Type Type
  | TyIs Type Type
  | TyAbs Variable Type Type
  | TyRec Label Type

instance Eq Type where
  TyNat           == TyNat            = True
  TyTop           == TyTop            = True
  TyBool          == TyBool           = True
  TyVar v         == TyVar v'         = v == v'
  TySubstVar v    == TySubstVar v'    = v == v'
  TyArr t1 t2     == TyArr t1' t2'    = t1 == t1' && t2 == t2'
  TyIs t1 t2      == TyIs t1' t2'     = t1 == t1' && t2 == t2'
  TyAbs v a1 a2   == TyAbs v' b1 b2   = v == v' && a1 == b1 && a2 == b2
  TyRec l a       == TyRec l' b       = l == l' && a == b
  _               == _                = False

data Expression
  = ExLit Integer
  | ExTop
  | ExTrue
  | ExFalse
  | ExVar Variable
  | ExAbs Variable Expression
  | ExApp Expression Expression
  | ExMerge Expression Expression
  | ExAnn Expression Type
  | ExRec Label Expression
  | ExRecFld Expression Label
  | ExTyAbs Variable Type Expression
  | ExTyApp Expression Type

-- data SubstitutionVariable = SubstVar Variable

data TypeContext
  = EmptyCtx
  | CVar TypeContext Variable Type
  | CSub TypeContext Variable Type


-- | Get the type of a variable from a context.
typeFromContext :: TypeContext -> Variable -> SubM Type
typeFromContext EmptyCtx _ = throwError ""
typeFromContext (CVar c v vt) x
  | v == x    = return vt
  | otherwise = typeFromContext c x
typeFromContext (CSub c v vt) x  -- TODO: is this right?
  | v == x    = return vt
  | otherwise = typeFromContext c x


appendContext :: TypeContext -> TypeContext -> TypeContext
appendContext EmptyCtx c = c
appendContext (CVar ctx v t) c = appendContext ctx (CVar c v t)
appendContext (CSub ctx v t) c = appendContext ctx (CSub c v t)

slicesFromContext :: TypeContext -> Variable -> TypeContext -> SubM (TypeContext, Type, TypeContext)
slicesFromContext EmptyCtx _ _ = throwError ""
slicesFromContext (CVar c v vt) x acc
  | v == x    = return (c, vt, acc)
  | otherwise = slicesFromContext c x (CVar acc v vt)
slicesFromContext (CSub c v vt) x acc  -- TODO: is this right?
  | v == x    = return (c, vt, acc)
  | otherwise = slicesFromContext c x (CSub acc v vt)


-- | The queue for implementing algorithmic subtyping rules.
data Queue
  = Null
  | ExtraLabel Queue Label
  | ExtraType Queue Type


data Substitution
  = EmptySubst
  | SVar Variable Type Substitution
  | SSub Variable Type Substitution
  deriving (Eq)


-- | Check whether a queue is empty.
isNullQueue :: Queue -> Bool
isNullQueue Null = True
isNullQueue _    = False
{-# INLINE isNullQueue #-}

-- | Get the first element and the tail of the queue as a tuple.
viewL :: Queue -> Maybe (Either Label Type, Queue)
viewL Null = Nothing
viewL (ExtraLabel q l)
  | isNullQueue q = return (Left l, Null)
  | otherwise     = do (res, queue) <- viewL q
                       return (res, ExtraLabel queue l)
viewL (ExtraType q t)
  | isNullQueue q = return (Right t, Null)
  | otherwise     = do (res, queue) <- viewL q
                       return (res, ExtraType queue t)

appendLabel :: Queue -> Label -> Queue
appendLabel Null l = ExtraLabel Null l
appendLabel (ExtraLabel q l') l = ExtraLabel (appendLabel q l) l'
appendLabel (ExtraType q t) l = ExtraType (appendLabel q l) t

appendType :: Queue -> Type -> Queue
appendType Null t = ExtraType Null t
appendType (ExtraLabel q l) t = ExtraLabel (appendType q t) l
appendType (ExtraType q t') t = ExtraType (appendType q t) t'

-- * Pretty Printing
-- ----------------------------------------------------------------------------

instance PrettyPrint Type where
  ppr TyNat             = ppr "Nat"
  ppr TyTop             = ppr "Top"
  ppr TyBool            = ppr "Bool"
  ppr (TyVar v)         = ppr v
  ppr (TySubstVar v)    = hcat [ppr v, ppr "^"]
  ppr (TyArr t1 t2)   = parens $ hsep [ppr t1, arrow, ppr t2]
  ppr (TyIs t1 t2)    = parens $ hsep [ppr t1, ppr "&", ppr t2]
  ppr (TyAbs v t1 t2) = parens $ hcat [ppr "\\/", parens (hsep [ppr v, ppr "*", ppr t1]), dot, ppr t2]
  ppr (TyRec l t)     = braces $ hsep [ppr l, colon, ppr t]

instance PrettyPrint Expression where
  ppr (ExLit i)       = ppr i
  ppr ExTop           = parens empty
  ppr ExTrue          = ppr "True"
  ppr ExFalse         = ppr "False"
  ppr (ExVar v)       = ppr v
  ppr (ExAbs v e)     = parens $ hcat [ppr "\\", ppr v, dot, ppr e]
  ppr (ExApp e1 e2)   = parens $ hsep [ppr e1, ppr e2]
  ppr (ExMerge e1 e2) = parens $ hsep [ppr e1, comma <> comma, ppr e2]
  ppr (ExAnn e t)     = parens $ hsep [ppr e, colon, ppr t]
  ppr (ExTyAbs v t e) = parens $ hcat [ppr "/\\", parens (hsep [ppr v, ppr "*", ppr t]), dot, ppr e]
  ppr (ExTyApp e t)   = parens $ hsep [ppr e, ppr t]
  ppr (ExRec l e)     = braces $ hsep [ppr l, equals, ppr e]
  ppr (ExRecFld e l)  = hcat [ppr e, dot, ppr l]

instance PrettyPrint TypeContext where
  ppr EmptyCtx     = ppr "•"
  ppr (CVar c v t) = hcat [ppr c, comma, ppr v, colon, ppr t]
  ppr (CSub c v t) = hcat [ppr c, comma, ppr v, ppr "^", colon, ppr t]

instance Show Type where
  show = render . ppr

instance Show Expression where
  show = render . ppr

instance Show TypeContext where
  show = render . ppr
