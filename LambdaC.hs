{-# OPTIONS_GHC -Wall #-}

module LambdaC where

type Variable = String
type Label    = String

-- TODOs:
--   4. Added some comments to separate the sections in the code. Some more
--      top-level comments would be nice to have.

-- * Main LambdaC types
-- ----------------------------------------------------------------------------

data Type
  = TyNat
  | TyTop
  | TyTup Type Type
  | TyArr Type Type
  | TyRec Label Type

eqTypes :: Type -> Type -> Bool
eqTypes TyNat TyNat
  = True
eqTypes TyTop TyTop
  = True
eqTypes (TyTup t1 t2) (TyTup t3 t4)
  = eqTypes t1 t3 && eqTypes t2 t4
eqTypes (TyArr t1 t2) (TyArr t3 t4)
  = eqTypes t1 t3 && eqTypes t2 t4
eqTypes (TyRec l1 t1) (TyRec l2 t2)
  = eqTypes t1 t2 && l1 == l2
eqTypes _ _
  = False


data Context
  = Empty
  | Snoc Context Variable Type


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


instance Show Type where
  show TyNat
    = "Nat"
  show TyTop
    = "Unit"
  show (TyTup t1 t2)
    = show t1 ++ "x" ++ show t2
  show (TyArr t1 t2)
    = show t1 ++ "->" ++ show t2
  show (TyRec l t)
    = "{" ++ show l ++ " : " ++ show t ++ "}"


instance Show Context where
  show Empty
    = "(.)"
  show (Snoc c v t)
    = show c ++ ", " ++ show v ++ " : " ++ show t


instance Show Term where
  show (TmVar v)
    = show v
  show (TmLit i)
    = show i
  show TmTop
    = "()"
  show (TmAbs v vt t)
    = "\\(" ++ show v ++ " : " ++ show vt ++ ")." ++ show t
  show (TmApp t1 t2)
    = show t1 ++ " " ++ show t2
  show (TmTup t1 t2)
    = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (TmRecCon l t)
    = "{" ++ show l ++ " = " ++ show t ++ "}"
  show (TmRecFld t l)
    = show t ++ "." ++ show l
  show (TmCast c t)
    = show c ++ " " ++ show t


instance Show Coercion where
  show (CoRefl t)
    = "CoRefl{" ++ show t ++ "}"
  show (CoTrans c1 c2)
    = show c1 ++ " . " ++ show c2
  show (CoAnyTop t)
    = "CoAnyTop{" ++ show t ++ "}"
  show CoTopArr
    = "CoAnyTop->"
  show (CoTopRec l)
    = "CoAnyTop{" ++ show l ++ "}"
  show (CoArr c1 c2)
    = show c1 ++ " -> " ++ show c2
  show (CoPair c1 c2)
    = "(" ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (CoLeft t1 t2)
    = "PI1 (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (CoRight t1 t2)
    = "PI2 (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (CoRec l c)
    = "{" ++ show l ++ " : " ++ show c ++ "}"
  show (CoDistRec l t1 t2)
    = "dist{" ++ show l ++ "} (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (CoDistArr t1 t2 t3)
    = "dist-> (" ++ show t1 ++ "->" ++ show t2 ++ ", "
      ++ show t1 ++ "->" ++ show t3 ++ ")"

-- * LambdaC Operational Semantics
-- ----------------------------------------------------------------------------

isValue :: Term -> Bool
isValue _ = True

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


eval :: Term -> Maybe Term
eval (TmApp e1 e2)
  -- STEP-APP1
  | Just e1' <- eval e1
  = Just (TmApp e1' e2)
  -- STEP-APP2
  | Just e2' <- eval e2
  = Just (TmApp e1 e2')
  -- STEP-TOPARR
  | TmCast CoTopArr TmTop <- e1
  , TmTop <- e2
  = Just TmTop
  -- STEP-ARR
  | TmCast (CoArr c1 c2) v1 <- e1
  = Just (TmCast c2 (TmApp v1 (TmCast c1 e2)))
  -- STEP-DISTARR
  | TmCast CoDistArr{} (TmTup v1 v2) <- e1
  = Just (TmTup (TmApp v1 e2) (TmApp v2 e2))
  -- STEP-BETA
  | TmAbs x _ e <- e1
  = Just (subst e x e2)

-- STEP-PAIR1 & STEP-PAIR2
eval (TmTup e1 e2)
  | Just e1' <- eval e1
  = Just (TmTup e1' e2)
  | Just e2' <- eval e2
  = Just (TmTup e1 e2')

-- STEP-PROJRCD
eval (TmRecFld (TmRecCon l v) l1)
  | l == l1
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
  = Just e
-- STEP-TRANS
  | CoTrans c1 c2 <- c
  = Just (TmCast c1 (TmCast c2 e))
-- SET-TOP
  | CoAnyTop _ <- c
  = Just TmTop
-- STEP-TOPRCD
  | CoTopRec l <- c
  , TmTop <- e
  = Just (TmRecCon l TmTop)
-- STEP-PAIR
  | CoPair c1 c2 <- c
  = Just (TmTup (TmCast c1 e) (TmCast c2 e))
-- STEP-DISTRCD
  | CoDistRec l _ _ <- c
  , TmTup (TmRecCon l1 v1) (TmRecCon l2 v2) <- e
  = if l == l1 && l1 == l2 then Just (TmRecCon l (TmTup v1 v2)) else Nothing
-- STEP-PROJL
  | CoLeft _ _ <- c
  , TmTup v1 _ <- e
  = Just v1
-- STEP-PROJR
  | CoRight _ _ <- c
  , TmTup _ v2 <- e
  = Just v2
-- STEP-CRCD
  | CoRec l co <- c
  , TmRecCon l1 v <- e
  = if l == l1 then Just (TmRecCon l (TmCast co v)) else Nothing

eval _ = Nothing


-- | Fully evaluate an expression.
fullEval :: Term -> Term
fullEval t = case eval t of
  Just st -> fullEval st
  Nothing -> t

-- * LambdaC Typing
-- ----------------------------------------------------------------------------

typeFromContext :: Context -> Variable -> Maybe Type
typeFromContext Empty _
  = Nothing
typeFromContext (Snoc c v vt) x
  | v == x
  = Just vt
  | otherwise
  = typeFromContext c x


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
termType c (TmApp e1 e2)
  | Just (TyArr t1 t2) <- termType c e1
  , Just t3            <- termType c e2
  = if eqTypes t1 t3 then Just t2 else Nothing
-- TYP-PAIR
termType c (TmTup e1 e2)
  | Just t1 <- termType c e1
  , Just t2 <- termType c e2
  = Just (TyTup t1 t2)
-- TYP-CAPP
termType c (TmCast co e)
  | Just t <- termType c e
  , Just (t1, t1') <- coercionType co
  = if eqTypes t t1 then Just t1' else Nothing
-- TYP-RCD
termType c (TmRecCon l e)
  | Just t <- termType c e
  = Just (TyRec l t)
-- TYP--PROJ
termType c (TmRecFld e l)
  | Just (TyRec l1 t) <- termType c e
  = if l == l1 then Just t else Nothing


coercionType :: Coercion -> Maybe (Type, Type)
-- COTYP-REFL
coercionType (CoRefl t)
  = Just (t, t)
-- COTYP-TRANS
coercionType (CoTrans c1 c2)
  = if eqTypes t2 t2' then Just (t1, t3) else Nothing where
    Just (t2, t3) = coercionType c1
    Just (t1, t2') = coercionType c2
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
coercionType (CoArr c1 c2)
  = Just (TyArr t1 t2, TyArr t1' t2') where
    Just (t1', t1) = coercionType c1
    Just (t2, t2') = coercionType c2
-- COTYP-PAIR
coercionType (CoPair c1 c2)
  = if eqTypes t1 t1' then Just (t1, TyTup t2 t3) else Nothing where
    Just (t1, t2) = coercionType c1
    Just (t1', t3) = coercionType c2
-- COTYP-PROJL
coercionType (CoLeft t1 t2)
  = Just (TyTup t1 t2, t1)
-- COTYP-PROJR
coercionType (CoRight t1 t2)
  = Just (TyTup t1 t2, t2)
-- COTYP-RCD
coercionType (CoRec l c)
  = Just (TyRec l t1, TyRec l t2) where
    Just (t1, t2) = coercionType c
-- COTYP-DISTRCD
coercionType (CoDistRec l t1 t2)
  = Just (TyTup (TyRec l t1) (TyRec l t2), TyRec l (TyTup t1 t2))
-- COTYP-DISTARR
coercionType (CoDistArr t1 t2 t3)
  = Just (TyTup (TyArr t1 t2) (TyArr t1 t3), TyArr t1 (TyTup t2 t3))
