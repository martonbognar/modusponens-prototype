-- {-# OPTIONS_GHC -Wall #-}

module LambdaC where

type Variable = String
type Label    = String

-- TODOs:
--   4. Re-enable -Wall

data Type
  = TyNat
  | TyTop
  | TyTup Type Type
  | TyArr Type Type
  | TyRec Label Type
  deriving (Eq)

data Context
  = Empty
  | Snoc Context Term Type
  deriving (Eq)

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
  deriving (Eq)

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
  deriving (Eq)

instance Show Type where
  show TyNat         = "Nat"
  show TyTop         = "Unit"
  show (TyTup t1 t2) = show t1 ++ "x" ++ show t2
  show (TyArr t1 t2) = show t1 ++ "->" ++ show t2
  show (TyRec l t)   = "{" ++ show l ++ " : " ++ show t ++ "}"

instance Show Context where
  show Empty        = "(.)"
  show (Snoc c v t) = show c ++ ", " ++ show v ++ " : " ++ show t

instance Show Term where
  show (TmVar v)      = show v
  show (TmLit i)      = show i
  show TmTop          = "()"
  show (TmAbs v vt t) = "\\(" ++ show v ++ " : " ++ show vt ++ ")." ++ show t
  show (TmApp t1 t2)  = show t1 ++ " " ++ show t2
  show (TmTup t1 t2)  = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (TmRecCon l t) = "{" ++ show l ++ " = " ++ show t ++ "}"
  show (TmRecFld t l) = show t ++ "." ++ show l
  show (TmCast c t)   = show c ++ " " ++ show t

instance Show Coercion where
  show (CoRefl t)           = "CoRefl{" ++ show t ++ "}"
  show (CoTrans c1 c2)      = show c1 ++ " . " ++ show c2
  show (CoAnyTop t)         = "CoAnyTop{" ++ show t ++ "}"
  show CoTopArr             = "CoAnyTop->"
  show (CoTopRec l)         = "CoAnyTop{" ++ show l ++ "}"
  show (CoArr c1 c2)        = show c1 ++ " -> " ++ show c2
  show (CoPair c1 c2)       = "(" ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (CoLeft t1 t2)       = "PI1 (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (CoRight t1 t2)      = "PI2 (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (CoRec l c)          = "{" ++ show l ++ " : " ++ show c ++ "}"
  show (CoDistRec l t1 t2)  = "dist{" ++ show l ++ "} (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (CoDistArr t1 t2 t3) = "dist-> (" ++ show t1 ++ "->" ++ show t2 ++ ", " ++ show t1 ++ "->" ++ show t3 ++ ")"

replaceVar :: Term -> Variable -> Term -> Term
replaceVar (TmVar v1) v e
  | v == v1 = e
  | otherwise = TmVar v
replaceVar (TmLit i) v e = TmLit i
replaceVar TmTop v e = TmTop
replaceVar (TmAbs v1 v1t t) v e = TmAbs v1 v1t (replaceVar t v e)
replaceVar (TmApp t1 t2) v e = TmApp (replaceVar t1 v e) (replaceVar t2 v e)
replaceVar (TmTup t1 t2) v e = TmTup (replaceVar t1 v e) (replaceVar t2 v e)
replaceVar (TmRecCon l t) v e = TmRecCon l (replaceVar t v e)
replaceVar (TmRecFld t l) v e = TmRecFld (replaceVar t v e) l
replaceVar (TmCast c t) v e = TmCast c (replaceVar t v e)

eval :: Term -> Maybe Term
eval (TmApp e1 e2)
  -- STEP-APP1
  | Just e1' <- eval e1
  = Just (TmApp e1' e2)
  -- STEP-APP2
  | Just e2' <- eval e2
  = Just (TmApp e1 e2')
  -- STEP-TOPARR
  | (TmCast CoTopArr TmTop, TmTop) <- (e1, e2)
  = Just TmTop
  -- STEP-ARR
  | (TmCast (CoArr c1 c2) v1, v2) <- (e1, e2)
  = Just (TmCast c2 (TmApp v1 (TmCast c1 v2)))
  -- STEP-DISTARR
  | (TmCast (CoDistArr _ _ _) (TmTup v1 v2), v3) <- (e1, e2)
  = Just (TmTup (TmApp v1 v3) (TmApp v2 v3))
  -- STEP-BETA
  | (TmAbs x xt e, v) <- (e1, e2)
  = Just (replaceVar e x v)

-- STEP-PAIR1 & STEP-PAIR2
eval (TmTup e1 e2)
  | Just e1' <- eval e1
  = Just (TmTup e1' e2)
  | Just e2' <- eval e2
  = Just (TmTup e1 e2')

-- STEP-PROJRCD
eval (TmRecFld (TmRecCon l v) l1)
  | l == l1 = Just v

-- STEP-RCD1
eval (TmRecCon l e) = Just (TmRecCon l e') where Just e' = eval e

-- STEP-RCD2
eval (TmRecFld e l) = Just (TmRecFld e' l) where Just e' = eval e

-- STEP-CAPP
eval (TmCast c e)
  | Just e' <- eval e
  = Just (TmCast c e')
  -- STEP-ID
  | (CoRefl xt, v) <- (c, e)
  = Just v
-- STEP-TRANS
  | (CoTrans c1 c2, v) <- (c, e)
  = Just (TmCast c1 (TmCast c2 v))
-- SET-TOP
  | (CoAnyTop _, v) <- (c, e)
  = Just TmTop
-- STEP-TOPRCD
  | (CoTopRec l, TmTop) <- (c, e)
  = Just (TmRecCon l TmTop)
-- STEP-PAIR
  | (CoPair c1 c2, v) <- (c, e)
  = Just (TmTup (TmCast c1 v) (TmCast c2 v))
-- STEP-DISTRCD
  | (CoDistRec l _ _, (TmTup (TmRecCon l1 v1) (TmRecCon l2 v2))) <- (c, e)
  = if l == l1 && l1 == l2 then Just (TmRecCon l (TmTup v1 v2)) else Nothing
-- STEP-PROJL
  | (CoLeft _ _, (TmTup v1 v2)) <- (c, e)
  = Just v1
-- STEP-PROJR
  | (CoRight _ _, (TmTup v1 v2)) <- (c, e)
  = Just v2
-- STEP-CRCD
  | (CoRec l c, (TmRecCon l1 v)) <- (c, e)
  = if l == l1 then Just (TmRecCon l (TmCast c v)) else Nothing

eval _ = Nothing

fullEval :: Term -> Term
fullEval t = case eval t of
  Just st -> fullEval st
  Nothing -> t

typeFromContext :: Context -> Term -> Maybe Type
typeFromContext Empty _ = Nothing
typeFromContext (Snoc c te ty) t
  | t == te = Just ty
  | otherwise = typeFromContext c t

termType :: Context -> Term -> Maybe Type
-- TYP-UNIT
termType _ TmTop = Just TyTop
-- TYP-LIT
termType _ (TmLit _) = Just TyNat
-- TYP-TmVar
termType c (TmVar x) = typeFromContext c (TmVar x)
-- TYP-ABS
termType c (TmAbs x xt e) = case typeFromContext (Snoc c (TmVar x) xt) e of
  Just et -> Just (TyArr xt et)
  Nothing -> Nothing
-- TYP-APP
termType c (TmApp e1 e2) = if t1 == t3 then Just t2 else Nothing where
    Just (TyArr t1 t2) = typeFromContext c e1
    Just t3 = typeFromContext c e2
-- TYP-PAIR
termType c (TmTup e1 e2) = Just (TyTup t1 t2) where
  Just t1 = typeFromContext c e1
  Just t2 = typeFromContext c e2
-- TYP-CAPP
termType c (TmCast co e) = if t1 == t2 then Just t' else Nothing where
  Just t1 = typeFromContext c e
  Just (t2, t') = coercionType co
-- TYP-RCD
termType c (TmRecCon l e) = Just (TyRec l t) where
  Just t = typeFromContext c e
-- TYP--PROJ
termType c (TmRecFld e l) = Just t where
  Just (TyRec l t) = typeFromContext c e

coercionType :: Coercion -> Maybe (Type, Type)
-- COTYP-REFL
coercionType (CoRefl t) = Just (t, t)
-- COTYP-TRANS
coercionType (CoTrans c1 c2) = if t2 == t2' then Just (t1, t3) else Nothing where
  Just (t2, t3) = coercionType c1
  Just (t1, t2') = coercionType c2
-- COTYP-CoAnyTop
coercionType (CoAnyTop t) = Just (t, TyTop)
-- COTYP-TOPARR
coercionType CoTopArr = Just (TyTop, TyArr TyTop TyTop)
-- COTYP-TOPRCD
coercionType (CoTopRec l) = Just (TyTop, TyRec l TyTop)
-- COTYP-ARR
coercionType (CoArr c1 c2) = Just (TyArr t1 t2, TyArr t1' t2') where
  Just (t1', t1) = coercionType c1
  Just (t2, t2') = coercionType c2
-- COTYP-PAIR
coercionType (CoPair c1 c2) = if t1 == t1' then Just (t1, TyTup t2 t3) else Nothing where
  Just (t1, t2) = coercionType c1
  Just (t1', t3) = coercionType c2
-- COTYP-PROJL
coercionType (CoLeft t1 t2) = Just (TyTup t1 t2, t1)
-- COTYP-PROJR
coercionType (CoRight t1 t2) = Just (TyTup t1 t2, t2)
-- COTYP-RCD
coercionType (CoRec l c) = Just (TyRec l t1, TyRec l t2) where
  Just (t1, t2) = coercionType c
-- COTYP-DISTRCD
coercionType (CoDistRec l t1 t2) = Just (TyTup (TyRec l t1) (TyRec l t2), TyRec l (TyTup t1 t2))
-- COTYP-DISTARR
coercionType (CoDistArr t1 t2 t3) = Just (TyTup (TyArr t1 t2) (TyArr t1 t3), TyArr t1 (TyTup t2 t3))
