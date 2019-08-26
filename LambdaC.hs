{-# OPTIONS_GHC -Wall #-}

module LambdaC where

import Control.Monad (guard)
import Text.PrettyPrint
import CommonTypes
import PrettyPrinter

-- * Main LambdaC types
-- ----------------------------------------------------------------------------

-- | Target types
data Type
  = TyNat
  | TyTop
  | TyTup Type Type
  | TyArr Type Type
  | TyRec Label Type

-- | Typing contexts
data Context
  = Empty
  | Snoc Context Variable Type

-- | Target terms
data Term
  = TmVar Variable
  | TmLit Integer
  | TmTop
  | TmAbs Variable Type Term
  | TmApp Term Term
  | TmTup Term Term
  | TmRecCon Label Term
  | TmRecFld Term Label
  | TmCast Coercion Term

-- | Coercions
data Coercion
  = CoRefl Type
  | CoTrans Coercion Coercion
  | CoAnyTop Type
  | CoTopArr
  | CoTopRec Label
  | CoArr Coercion Coercion
  | CoPair Coercion Coercion
  | CoLeft Type Type
  | CoRight Type Type
  | CoRec Label Coercion
  | CoDistRec Label Type Type
  | CoDistArr Type Type Type

-- | Determine equality between two types.
eqTypes :: Type -> Type -> Bool
eqTypes TyNat TyNat                 = True
eqTypes TyTop TyTop                 = True
eqTypes (TyTup t1 t2) (TyTup t3 t4) = eqTypes t1 t3 && eqTypes t2 t4
eqTypes (TyArr t1 t2) (TyArr t3 t4) = eqTypes t1 t3 && eqTypes t2 t4
eqTypes (TyRec l1 t1) (TyRec l2 t2) = eqTypes t1 t2 && l1 == l2
eqTypes _ _                         = False

-- * Pretty Printing
-- ----------------------------------------------------------------------------

instance PrettyPrint Type where
  ppr TyNat         = ppr "Nat"
  ppr TyTop         = ppr "Unit"
  ppr (TyTup t1 t2) = parens $ hsep [ppr t1, ppr "✕", ppr t2]
  ppr (TyArr t1 t2) = parens $ hsep [ppr t1, arrow, ppr t2]
  ppr (TyRec l t)   = braces $ hsep [ppr l, colon, ppr t]

instance PrettyPrint Context where
  ppr Empty        = ppr "•"
  ppr (Snoc c v t) = hcat [ppr c, comma, ppr v, colon, ppr t]

instance PrettyPrint Term where
  ppr (TmVar v)      = ppr v
  ppr (TmLit i)      = ppr i
  ppr TmTop          = parens empty
  ppr (TmAbs v vt t)
    = hcat [ppr "\\", parens $ hsep [ppr v, colon, ppr vt], ppr t]
  ppr (TmApp t1 t2)  = parens $ hsep [ppr t1, ppr t2]
  ppr (TmTup t1 t2)  = parensList [ppr t1, ppr t2]
  ppr (TmRecCon l t) = braces $ hsep [ppr l, equals, ppr t]
  ppr (TmRecFld t l) = hcat [ppr t, dot, ppr l]
  ppr (TmCast c t)   = parens $ hsep [ppr c, ppr t]

instance PrettyPrint Coercion where
  ppr (CoRefl t)           = ppr "id" <> braces (ppr t)
  ppr (CoTrans c1 c2)      = parens $ hsep [ppr c1, dot, ppr c2]
  ppr (CoAnyTop t)         = ppr "top" <> braces (ppr t)
  ppr CoTopArr             = ppr "top" <> arrow
  ppr (CoTopRec l)         = ppr "top" <> braces (ppr l)
  ppr (CoArr c1 c2)        = parens $ hsep [ppr c1, arrow, ppr c2]
  ppr (CoPair c1 c2)       = parensList [ppr c1, ppr c2]
  ppr (CoLeft t1 t2)       = hcat [ppr "π₁", parensList [ppr t1, ppr t2]]
  ppr (CoRight t1 t2)      = hcat [ppr "π₂", parensList [ppr t1, ppr t2]]
  ppr (CoRec l c)          = braces $ hsep [ppr l, colon, ppr c]
  ppr (CoDistRec l t1 t2)
    = hsep [ppr "dist", braces $ hcat [
        ppr l,
        parensList [ppr t1, ppr t2]
      ]]
  ppr (CoDistArr t1 t2 t3)
    = hcat [ppr "dist" <> arrow, parensList [
        hcat [ppr t1, arrow, ppr t2],
        hcat [ppr t1, arrow, ppr t3]
      ]]

instance Show Type where
  show = render . ppr

instance Show Context where
  show = render . ppr

instance Show Term where
  show = render . ppr

instance Show Coercion where
  show = render . ppr

-- Just some notes pasted here

{- putStrLn (map Data.Char.chr [0x03B1 .. (0x03B1 + 25)]) -}
{- αβγδεζηθικλμνξοπρςστυφχψωϊ -}

-- Lookup the UTF 16 Hex for the character you want

{- λ> putStrLn ("x" ++ (map chr [0x2080 .. 0x2089])) -}
{- x₀₁₂₃₄₅₆₇₈₉ -}


-- * LambdaC Operational Semantics
-- ----------------------------------------------------------------------------

-- | Determine whether a term is a target value.
isValue :: Term -> Bool
isValue TmAbs{}                  = True
isValue TmTop                    = True
isValue (TmLit _)                = True
isValue (TmTup v1 v2)            = isValue v1 && isValue v2
isValue (TmCast CoArr{} v)       = isValue v
isValue (TmCast CoDistArr{} v)   = isValue v
isValue (TmCast CoTopArr v)      = isValue v
isValue _                        = False

-- subst :: Term -> Variable -> Term -> RnM Term
--
--   where
--     rnTerm :: (Variable, Term) -> RnM (Variable, Term)


-- | In a given term, substitue a variable with another term.
subst :: Term -> Variable -> Term -> Term
subst expr x v = case expr of
  TmVar x' | x' == x   -> v
           | otherwise -> TmVar x'
  TmLit i        -> TmLit i
  TmTop          -> TmTop
  TmAbs x' x't e -> TmAbs x' x't (subst e x v)
  TmApp e1 e2    -> TmApp (subst e1 x v) (subst e2 x v)
  TmTup e1 e2    -> TmTup (subst e1 x v) (subst e2 x v)
  TmRecCon l e   -> TmRecCon l (subst e x v)
  TmRecFld e l   -> TmRecFld (subst e x v) l
  TmCast c e     -> TmCast c (subst e x v)


-- | Execute small-step reduction on a term.
eval :: Term -> Maybe Term
eval (TmApp e1 e2)
  -- STEP-APP1
  | Just e1' <- eval e1
  = return (TmApp e1' e2)
  -- STEP-APP2
  | Just e2' <- eval e2
  , isValue e1
  = return (TmApp e1 e2')
  -- STEP-TOPARR
  | TmCast CoTopArr TmTop <- e1
  , TmTop <- e2
  = return TmTop
  -- STEP-ARR
  | TmCast (CoArr c1 c2) v1 <- e1
  , isValue v1
  , isValue e2
  = return (TmCast c2 (TmApp v1 (TmCast c1 e2)))
  -- STEP-DISTARR
  | TmCast CoDistArr{} (TmTup v1 v2) <- e1
  , isValue v1
  , isValue v2
  , isValue e2
  = return (TmTup (TmApp v1 e2) (TmApp v2 e2))
  -- STEP-BETA
  | TmAbs x _ e <- e1
  , isValue e2
  = return (subst e x e2)

-- STEP-PAIR1 & STEP-PAIR2
eval (TmTup e1 e2)
  | Just e1' <- eval e1
  = return (TmTup e1' e2)
  | Just e2' <- eval e2
  , isValue e1
  = return (TmTup e1 e2')

-- STEP-PROJRCD
eval (TmRecFld (TmRecCon l v) l1)
  | l == l1
  , isValue v
  = return v

-- STEP-RCD1
eval (TmRecCon l e)
  | Just e' <- eval e
  = return (TmRecCon l e')

-- STEP-RCD2
eval (TmRecFld e l)
  | Just e' <- eval e
  = return (TmRecFld e' l)

-- STEP-CAPP
eval (TmCast c e)
  | Just e' <- eval e
  = return (TmCast c e')
  -- STEP-ID
  | CoRefl _ <- c
  , isValue e
  = return e
-- STEP-TRANS
  | CoTrans c1 c2 <- c
  , isValue e
  = return (TmCast c1 (TmCast c2 e))
-- SET-TOP
  | CoAnyTop _ <- c
  , isValue e
  = return TmTop
-- STEP-TOPRCD
  | CoTopRec l <- c
  , TmTop <- e
  = return (TmRecCon l TmTop)
-- STEP-PAIR
  | CoPair c1 c2 <- c
  , isValue e
  = return (TmTup (TmCast c1 e) (TmCast c2 e))
-- STEP-DISTRCD
  | CoDistRec l _ _ <- c
  , TmTup (TmRecCon l1 v1) (TmRecCon l2 v2) <- e
  , isValue v1
  , isValue v2
  = do guard (l == l1 && l1 == l2)
       return (TmRecCon l (TmTup v1 v2))
-- STEP-PROJL
  | CoLeft _ _ <- c
  , TmTup v1 v2 <- e
  , isValue v1
  , isValue v2
  = return v1
-- STEP-PROJR
  | CoRight _ _ <- c
  , TmTup v1 v2 <- e
  , isValue v1
  , isValue v2
  = return v2
-- STEP-CRCD
  | CoRec l co <- c
  , TmRecCon l1 v <- e
  , isValue v
  = do guard (l == l1)
       return (TmRecCon l (TmCast co v))

eval _ = fail "Evaluation error"


-- | Fully evaluate a term.
fullEval :: Term -> Term
fullEval t = case eval t of
  Just st -> fullEval st
  Nothing -> t

-- * LambdaC Typing
-- ----------------------------------------------------------------------------

-- | Get the type of a variable from a context.
typeFromContext :: Context -> Variable -> Maybe Type
typeFromContext Empty _ = fail "Variable not in context"
typeFromContext (Snoc c v vt) x
  | v == x    = return vt
  | otherwise = typeFromContext c x


-- | In a given context, determine the type of a term.
termType :: Context -> Term -> Maybe Type
-- TYP-UNIT
termType _ TmTop = return TyTop
-- TYP-LIT
termType _ (TmLit _) = return TyNat
-- TYP-TmVar
termType c (TmVar x) = typeFromContext c x
-- TYP-ABS
termType c (TmAbs x t1 e)
  = do t2 <- termType (Snoc c x t1) e
       return (TyArr t1 t2)
-- TYP-APP
termType c (TmApp e1 e2)
  = do (TyArr t1 t2) <- termType c e1
       t3            <- termType c e2
       guard (eqTypes t1 t3)
       return t2
-- TYP-PAIR
termType c (TmTup e1 e2)
  = do t1 <- termType c e1
       t2 <- termType c e2
       return (TyTup t1 t2)
-- TYP-CAPP
termType c (TmCast co e)
  = do t         <- termType c e
       (t1, t1') <- coercionType co
       guard (eqTypes t t1)
       return t1'
-- TYP-RCD
termType c (TmRecCon l e)
  = do t <- termType c e
       return (TyRec l t)
-- TYP--PROJ
termType c (TmRecFld e l)
  = do (TyRec l1 t) <- termType c e
       guard (l == l1)
       return t


-- | Determine the type of a coercion.
coercionType :: Coercion -> Maybe (Type, Type)
-- COTYP-REFL
coercionType (CoRefl t)
  = return (t, t)
-- COTYP-TRANS
coercionType (CoTrans c1 c2)
  = do (t2, t3)  <- coercionType c1
       (t1, t2') <- coercionType c2
       guard (eqTypes t2 t2')
       return (t1, t3)
-- COTYP-CoAnyTop
coercionType (CoAnyTop t) = return (t, TyTop)
-- COTYP-TOPARR
coercionType CoTopArr
  = return (TyTop, TyArr TyTop TyTop)
-- COTYP-TOPRCD
coercionType (CoTopRec l)
  = return (TyTop, TyRec l TyTop)
-- COTYP-ARR
coercionType (CoArr c1 c2)
  = do (t1', t1) <- coercionType c1
       (t2, t2') <- coercionType c2
       return (TyArr t1 t2, TyArr t1' t2')
-- COTYP-PAIR
coercionType (CoPair c1 c2)
  = do (t1, t2)  <- coercionType c1
       (t1', t3) <- coercionType c2
       guard (eqTypes t1 t1')
       return (t1, TyTup t2 t3)
-- COTYP-PROJL
coercionType (CoLeft t1 t2)
  = return (TyTup t1 t2, t1)
-- COTYP-PROJR
coercionType (CoRight t1 t2)
  = return (TyTup t1 t2, t2)
-- COTYP-RCD
coercionType (CoRec l c)
  = do (t1, t2) <- coercionType c
       return (TyRec l t1, TyRec l t2)
-- COTYP-DISTRCD
coercionType (CoDistRec l t1 t2)
  = return (TyTup (TyRec l t1) (TyRec l t2), TyRec l (TyTup t1 t2))
-- COTYP-DISTARR
coercionType (CoDistArr t1 t2 t3)
  = return (TyTup (TyArr t1 t2) (TyArr t1 t3), TyArr t1 (TyTup t2 t3))
