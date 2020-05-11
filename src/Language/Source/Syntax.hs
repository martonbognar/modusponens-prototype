{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveDataTypeable
           , DeriveGeneric
           , MultiParamTypeClasses
  #-}

module Language.Source.Syntax where

import Prelude hiding ((<>))

import Data.Label
import Text.PrettyPrint
import Control.Monad.Renamer
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Control.Monad (guard, mzero)

import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import PrettyPrinter

-- * Main Source types
-- ----------------------------------------------------------------------------

type TypeVar = Name Type

data Type
  = TyNat
  | TyTop
  | TyBool
  | TyVar TypeVar
  | TySubstVar TypeVar  -- should only be used during typechecking
  | TyArr Type Type
  | TyIs Type Type
  | TyAbs (Bind TypeVar Type) Type
  | TyRec Label Type
  deriving (Generic)

instance Eq Type where
  TyNat           == TyNat            = True
  TyTop           == TyTop            = True
  TyBool          == TyBool           = True
  TyVar v         == TyVar v'         = v == v'
  TySubstVar v    == TySubstVar v'    = v == v'
  TyArr t1 t2     == TyArr t1' t2'    = t1 == t1' && t2 == t2'
  TyIs t1 t2      == TyIs t1' t2'     = t1 == t1' && t2 == t2'
  TyAbs b t       == TyAbs b' t'      = undefined
  TyRec l a       == TyRec l' b       = l == l' && a == b
  _               == _                = False

type TermVar = Name Expression

data Expression
  = ExLit Integer
  | ExTop
  | ExTrue
  | ExFalse
  | ExVar TermVar
  | ExAbs (Bind TermVar Expression)
  | ExApp Expression Expression
  | ExMerge Expression Expression
  | ExAnn Expression Type
  | ExRec Label Expression
  | ExRecFld Expression Label
  | ExTyAbs (Bind TypeVar Expression) Type
  | ExTyApp Expression Type
  deriving (Generic)

instance Alpha Type
instance Alpha Expression

instance Subst Expression Expression where
  isvar (ExVar v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst Type Type where
  isvar (TyVar v) = Just (SubstName v)
  isvar (TySubstVar v) = Just (SubstName v)  -- TODO: incorrect
  isvar _ = Nothing

instance Subst Expression Type
instance Subst Expression Label
instance Subst Type Label
instance Subst Type TypeContext
instance Subst Type Queue

data TypeContext
  = EmptyCtx
  | CTermVar TypeContext TermVar Type
  | CVar TypeContext TypeVar Type
  | CSub TypeContext TypeVar Type
  deriving (Generic)


termTypeFromContext :: TypeContext -> TermVar -> MaybeT FreshM Type
termTypeFromContext EmptyCtx _ = mzero
termTypeFromContext (CTermVar c v vt) x
  | v == x = return vt
  | otherwise = termTypeFromContext c x
termTypeFromContext (CVar c _ _) x = termTypeFromContext c x
termTypeFromContext (CSub c _ _) x = termTypeFromContext c x


-- | Get the type of a variable from a context.
typeFromContext :: TypeContext -> TypeVar -> MaybeT FreshM Type
typeFromContext EmptyCtx _ = mzero
typeFromContext (CTermVar c _ _) x = typeFromContext c x
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

slicesFromContext :: TypeContext -> TypeVar -> TypeContext -> MaybeT FreshM (TypeContext, Type, TypeContext)
slicesFromContext EmptyCtx _ _ = mzero
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
  deriving (Generic)


data Substitution
  = EmptySubst
  | SVar TypeVar Type Substitution
  | SSub TypeVar Type Substitution
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
  ppr (TyVar v)         = ppr (name2String v)
  ppr (TySubstVar v)    = hcat [ppr (name2String v), ppr "^"]
  ppr (TyArr t1 t2)   = parens $ hsep [ppr t1, arrow, ppr t2]
  ppr (TyIs t1 t2)    = parens $ hsep [ppr t1, ppr "&", ppr t2]
  -- ppr (TyAbs v t1 t2) = parens $ hcat [ppr "\\/", parens (hsep [ppr v, ppr "*", ppr t1]), dot, ppr t2]
  ppr (TyRec l t)     = braces $ hsep [ppr l, colon, ppr t]

instance PrettyPrint Expression where
  ppr (ExLit i)       = ppr i
  ppr ExTop           = parens empty
  ppr ExTrue          = ppr "True"
  ppr ExFalse         = ppr "False"
  ppr (ExVar v)       = ppr (name2String v)
  -- ppr (ExAbs v e)     = parens $ hcat [ppr "\\", ppr v, dot, ppr e]
  ppr (ExApp e1 e2)   = parens $ hsep [ppr e1, ppr e2]
  ppr (ExMerge e1 e2) = parens $ hsep [ppr e1, comma <> comma, ppr e2]
  ppr (ExAnn e t)     = parens $ hsep [ppr e, colon, ppr t]
  -- ppr (ExTyAbs v t e) = parens $ hcat [ppr "/\\", parens (hsep [ppr v, ppr "*", ppr t]), dot, ppr e]
  ppr (ExTyApp e t)   = parens $ hsep [ppr e, ppr t]
  ppr (ExRec l e)     = braces $ hsep [ppr l, equals, ppr e]
  ppr (ExRecFld e l)  = hcat [ppr e, dot, ppr l]

instance PrettyPrint TypeContext where
  ppr EmptyCtx     = ppr "•"
  ppr (CVar c v t) = hcat [ppr c, comma, ppr (name2String v), colon, ppr t]
  ppr (CSub c v t) = hcat [ppr c, comma, ppr (name2String v), ppr "^", colon, ppr t]

instance Show Type where
  show = render . ppr

instance Show Expression where
  show = render . ppr

instance Show TypeContext where
  show = render . ppr
