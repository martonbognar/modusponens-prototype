{-# OPTIONS_GHC -Wall #-}

module LambdaC where

import Text.PrettyPrint

type Variable = String
type Label    = String

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
  | TmLit Int
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

arrow :: Doc
arrow = text "→"

dot :: Doc
dot = text "."

commaSep :: [Doc] -> [Doc]
commaSep = punctuate comma

parensList :: [Doc] -> Doc
parensList = parens . hsep . commaSep


prLabel :: Label -> Doc
prLabel = text


prVariable :: Variable -> Doc
prVariable = text


prType :: Type -> Doc
prType TyNat         = text "Nat"
prType TyTop         = text "Unit"
prType (TyTup t1 t2) = hsep [prType t1, text "✕", prType t2]
prType (TyArr t1 t2) = hsep [prType t1, arrow, prType t2]
prType (TyRec l t)   = braces $ hsep [prLabel l, colon, prType t]


prContext :: Context -> Doc
prContext Empty = text "•"
prContext (Snoc c v t)
  = hcat [prContext c, comma, prVariable v, colon, prType t]


prTerm :: Term -> Doc
prTerm (TmVar v)      = prVariable v
prTerm (TmLit i)      = int i
prTerm TmTop          = parens empty
prTerm (TmAbs v vt t)
  = hcat [text "\\", parens $ hsep [prVariable v, colon, prType vt], prTerm t]
prTerm (TmApp t1 t2)  = prTerm t1 <+> prTerm t2
prTerm (TmTup t1 t2)  = parensList [prTerm t1, prTerm t2]
prTerm (TmRecCon l t) = braces $ hsep [prLabel l, equals, prTerm t]
prTerm (TmRecFld t l) = hcat [prTerm t, dot, prLabel l]
prTerm (TmCast c t)   = prCoercion c <+> prTerm t


prCoercion :: Coercion -> Doc
prCoercion (CoRefl t)           = text "id" <> braces (prType t)
prCoercion (CoTrans c1 c2)      = hsep [prCoercion c1, dot, prCoercion c2]
prCoercion (CoAnyTop t)         = text "top" <> braces (prType t)
prCoercion CoTopArr             = text "top" <> arrow
prCoercion (CoTopRec l)         = text "top" <> braces (prLabel l)
prCoercion (CoArr c1 c2)        = hsep [prCoercion c1, arrow, prCoercion c2]
prCoercion (CoPair c1 c2)       = parensList [prCoercion c1, prCoercion c2]
prCoercion (CoLeft t1 t2)
  = hcat [text "π₁", parensList [prType t1, prType t2]]
prCoercion (CoRight t1 t2)
  = hcat [text "π₂", parensList [prType t1, prType t2]]
prCoercion (CoRec l c)          = braces $ hsep [prLabel l, colon, prCoercion c]
prCoercion (CoDistRec l t1 t2)
  = hsep [text "dist", braces $ hcat [
      prLabel l,
      parensList [prType t1, prType t2]
    ]]
prCoercion (CoDistArr t1 t2 t3)
  = hcat [text "dist" <> arrow, parensList [
      hcat [prType t1, arrow, prType t2],
      hcat [prType t1, arrow, prType t3]
    ]]


instance Show Type where
  show = render . prType


instance Show Context where
  show = render . prContext


instance Show Term where
  show = render . prTerm


instance Show Coercion where
  show = render . prCoercion

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
  = Just (TmApp e1' e2)
  -- STEP-APP2
  | Just e2' <- eval e2
  , isValue e1
  = Just (TmApp e1 e2')
  -- STEP-TOPARR
  | TmCast CoTopArr TmTop <- e1
  , TmTop <- e2
  = Just TmTop
  -- STEP-ARR
  | TmCast (CoArr c1 c2) v1 <- e1
  , isValue v1
  , isValue e2
  = Just (TmCast c2 (TmApp v1 (TmCast c1 e2)))
  -- STEP-DISTARR
  | TmCast CoDistArr{} (TmTup v1 v2) <- e1
  , isValue v1
  , isValue v2
  , isValue e2
  = Just (TmTup (TmApp v1 e2) (TmApp v2 e2))
  -- STEP-BETA
  | TmAbs x _ e <- e1
  , isValue e2
  = Just (subst e x e2)

-- STEP-PAIR1 & STEP-PAIR2
eval (TmTup e1 e2)
  | Just e1' <- eval e1
  = Just (TmTup e1' e2)
  | Just e2' <- eval e2
  , isValue e1
  = Just (TmTup e1 e2')

-- STEP-PROJRCD
eval (TmRecFld (TmRecCon l v) l1)
  | l == l1
  , isValue v
  = Just v

-- STEP-RCD1
eval (TmRecCon l e)
  | Just e' <- eval e
  = Just (TmRecCon l e')

-- STEP-RCD2
eval (TmRecFld e l)
  | Just e' <- eval e
  = Just (TmRecFld e' l)

-- STEP-CAPP
eval (TmCast c e)
  | Just e' <- eval e
  = Just (TmCast c e')
  -- STEP-ID
  | CoRefl _ <- c
  , isValue e
  = Just e
-- STEP-TRANS
  | CoTrans c1 c2 <- c
  , isValue e
  = Just (TmCast c1 (TmCast c2 e))
-- SET-TOP
  | CoAnyTop _ <- c
  , isValue e
  = Just TmTop
-- STEP-TOPRCD
  | CoTopRec l <- c
  , TmTop <- e
  = Just (TmRecCon l TmTop)
-- STEP-PAIR
  | CoPair c1 c2 <- c
  , isValue e
  = Just (TmTup (TmCast c1 e) (TmCast c2 e))
-- STEP-DISTRCD
  | CoDistRec l _ _ <- c
  , TmTup (TmRecCon l1 v1) (TmRecCon l2 v2) <- e
  , isValue v1
  , isValue v2
  = if l == l1 && l1 == l2 then Just (TmRecCon l (TmTup v1 v2)) else Nothing
-- STEP-PROJL
  | CoLeft _ _ <- c
  , TmTup v1 v2 <- e
  , isValue v1
  , isValue v2
  = Just v1
-- STEP-PROJR
  | CoRight _ _ <- c
  , TmTup v1 v2 <- e
  , isValue v1
  , isValue v2
  = Just v2
-- STEP-CRCD
  | CoRec l co <- c
  , TmRecCon l1 v <- e
  , isValue v
  = if l == l1 then Just (TmRecCon l (TmCast co v)) else Nothing

eval _ = Nothing


-- | Fully evaluate a term.
fullEval :: Term -> Term
fullEval t = case eval t of
  Just st -> fullEval st
  Nothing -> t

-- * LambdaC Typing
-- ----------------------------------------------------------------------------

-- | Get the type of a variable from a context.
typeFromContext :: Context -> Variable -> Maybe Type
typeFromContext Empty _ = Nothing
typeFromContext (Snoc c v vt) x
  | v == x    = Just vt
  | otherwise = typeFromContext c x


-- | In a given context, determine the type of a term.
termType :: Context -> Term -> Maybe Type
-- TYP-UNIT
termType _ TmTop
  = Just TyTop
-- TYP-LIT
termType _ (TmLit _)
  = Just TyNat
-- TYP-TmVar
termType c (TmVar x)
  = typeFromContext c x
-- TYP-ABS
termType c (TmAbs x t1 e)
  | Just t2 <- termType (Snoc c x t1) e
  = Just (TyArr t1 t2)
-- TYP-APP
termType c (TmApp e1 e2) = do
  (TyArr t1 t2) <- termType c e1
  t3            <- termType c e2
  if eqTypes t1 t3
    then return t2
    else Nothing
-- TYP-PAIR
termType c (TmTup e1 e2) = do
  t1 <- termType c e1
  t2 <- termType c e2
  return (TyTup t1 t2)
-- TYP-CAPP
termType c (TmCast co e) = do
  t         <- termType c e
  (t1, t1') <- coercionType co
  if eqTypes t t1
    then return t1'
    else Nothing
-- TYP-RCD
termType c (TmRecCon l e) = do
  t <- termType c e
  return (TyRec l t)
-- TYP--PROJ
termType c (TmRecFld e l) = do
  (TyRec l1 t) <- termType c e
  if l == l1
    then return t
    else Nothing

termType _ _ = Nothing


-- | Determine the type of a coercion.
coercionType :: Coercion -> Maybe (Type, Type)
-- COTYP-REFL
coercionType (CoRefl t)
  = Just (t, t)
-- COTYP-TRANS
coercionType (CoTrans c1 c2) = do
  (t2, t3)  <- coercionType c1
  (t1, t2') <- coercionType c2
  if eqTypes t2 t2'
    then return (t1, t3)
    else Nothing
-- COTYP-CoAnyTop
coercionType (CoAnyTop t)
  = Just (t, TyTop)
-- COTYP-TOPARR
coercionType CoTopArr
  = Just (TyTop, TyArr TyTop TyTop)
-- COTYP-TOPRCD
coercionType (CoTopRec l)
  = Just (TyTop, TyRec l TyTop)
-- COTYP-ARR
coercionType (CoArr c1 c2) = do
  (t1', t1) <- coercionType c1
  (t2, t2') <- coercionType c2
  return (TyArr t1 t2, TyArr t1' t2')
-- COTYP-PAIR
coercionType (CoPair c1 c2) = do
  (t1, t2)  <- coercionType c1
  (t1', t3) <- coercionType c2
  if eqTypes t1 t1'
    then return (t1, TyTup t2 t3)
    else Nothing
-- COTYP-PROJL
coercionType (CoLeft t1 t2)
  = Just (TyTup t1 t2, t1)
-- COTYP-PROJR
coercionType (CoRight t1 t2)
  = Just (TyTup t1 t2, t2)
-- COTYP-RCD
coercionType (CoRec l c) = do
  (t1, t2) <- coercionType c
  return (TyRec l t1, TyRec l t2)
-- COTYP-DISTRCD
coercionType (CoDistRec l t1 t2)
  = Just (TyTup (TyRec l t1) (TyRec l t2), TyRec l (TyTup t1 t2))
-- COTYP-DISTARR
coercionType (CoDistArr t1 t2 t3)
  = Just (TyTup (TyArr t1 t2) (TyArr t1 t3), TyArr t1 (TyTup t2 t3))
