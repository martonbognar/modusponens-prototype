type Variable = String
type Label    = String

data Type = NatType |
            UnitType |
            TupleType Type Type |
            FunctionType Type Type |
            RecordType Label Type
            deriving (Eq)

data Context = Empty |
               Extended Context Term Type
               deriving (Eq)

data Term = Var Variable |
            Num Int |
            UnitTerm |
            LambdaTerm Variable Type Term |
            Application Term Term |
            TupleTerm Term Term |
            Assign Label Term |
            Extract Term Label |
            CoercionTerm Coercion Term
            deriving (Eq)

data Coercion = Id Type |
                Composition Coercion Coercion |
                Top Type |
                TopArrow |
                TopLabel Label |
                Function Coercion Coercion |
                TupleCoercion Coercion Coercion |
                Project1 Type Type |
                Project2 Type Type |
                RecordCoercion Label Coercion |
                DistLabel Label Type Type |
                DistArrow Type Type Type
                deriving (Eq)

data Value = LambdaValue Variable Type Term |
             UnitValue |
             NatValue Int |
             TupleValue Value Value |
             CoercionValue Coercion Coercion Value |
             DistArrowValue Value |
             TopArrowValue Value
             deriving (Eq)

instance Show Type where
  show NatType              = "Nat"
  show UnitType             = "Unit"
  show (TupleType t1 t2)    = show t1 ++ "x" ++ show t2
  show (FunctionType t1 t2) = show t1 ++ "->" ++ show t2
  show (RecordType l t)     = "{" ++ show l ++ " : " ++ show t ++ "}"

instance Show Context where
  show Empty            = "(.)"
  show (Extended c v t) = show c ++ ", " ++ show v ++ " : " ++ show t

instance Show Term where
  show (Var v)             = show v
  show (Num i)             = show i
  show UnitTerm            = "()"
  show (LambdaTerm v vt t) = "\\(" ++ show v ++ " : " ++ show vt ++ ")." ++ show t
  show (Application t1 t2) = show t1 ++ " " ++ show t2
  show (TupleTerm t1 t2)   = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (Assign l t)        = "{" ++ show l ++ " = " ++ show t ++ "}"
  show (Extract t l)       = show t ++ "." ++ show l
  show (CoercionTerm c t)  = show c ++ " " ++ show t

instance Show Coercion where
  show (Id t)                = "id{" ++ show t ++ "}"
  show (Composition c1 c2)   = show c1 ++ " . " ++ show c2
  show (Top t)               = "top{" ++ show t ++ "}"
  show TopArrow              = "top->"
  show (TopLabel l)          = "top{" ++ show l ++ "}"
  show (Function c1 c2)      = show c1 ++ " -> " ++ show c2
  show (TupleCoercion c1 c2) = "(" ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (Project1 t1 t2)      = "PI1 (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (Project2 t1 t2)      = "PI2 (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (RecordCoercion l c)  = "{" ++ show l ++ " : " ++ show c ++ "}"
  show (DistLabel l t1 t2)   = "dist{" ++ show l ++ "} (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (DistArrow t1 t2 t3)  = "dist-> (" ++ show t1 ++ "->" ++ show t2 ++ ", " ++ show t1 ++ "->" ++ show t3 ++ ")"

instance Show Value where
  show (LambdaValue v ty te)   = "\\{" ++ show v ++ " : " ++ show ty ++ "}" ++ "." ++ show te
  show UnitValue               = "()"
  show (NatValue i)            = show i
  show (TupleValue v1 v2)      = "(" ++ show v1 ++ ", " ++ show v2 ++ ")"
  show (CoercionValue c1 c2 v) = "(" ++ show c1 ++ " -> " ++ show c2 ++ ") " ++ show v
  show (DistArrowValue v)      = "dist-> " ++ show v
  show (TopArrowValue v)       = "top-> " ++ show v

replaceVar :: Term -> Variable -> Term -> Term
replaceVar (Var v1) v e
  | v == v1 = e
  | otherwise = Var v
replaceVar (Num i) v e = Num i
replaceVar UnitTerm v e = UnitTerm
replaceVar (LambdaTerm v1 v1t t) v e = LambdaTerm v1 v1t (replaceVar t v e)
replaceVar (Application t1 t2) v e = Application (replaceVar t1 v e) (replaceVar t2 v e)
replaceVar (TupleTerm t1 t2) v e = TupleTerm (replaceVar t1 v e) (replaceVar t2 v e)
replaceVar (Assign l t) v e = Assign l (replaceVar t v e)
replaceVar (Extract t l) v e = Extract (replaceVar t v e) l
replaceVar (CoercionTerm c t) v e = CoercionTerm c (replaceVar t v e)

eval :: Term -> Maybe Term
-- STEP-ID
eval (CoercionTerm (Id xt) t) = Just t
-- STEP-TRANS
eval (CoercionTerm (Composition c1 c2) t) = Just (CoercionTerm c1 (CoercionTerm c2 t))
-- SET-TOP
eval (CoercionTerm (Top xt) t) = Just UnitTerm
-- STEP-TOPARR
eval (Application (CoercionTerm TopArrow UnitTerm) UnitTerm) = Just UnitTerm
-- STEP-TOPRCD
eval (CoercionTerm (TopLabel l) UnitTerm) = Just (Assign l UnitTerm)
-- STEP-ARR
eval (Application (CoercionTerm (Function c1 c2) t1) t2) = Just (CoercionTerm c2 (Application t1 (CoercionTerm c1 t2)))
-- STEP-PAIR
eval (CoercionTerm (TupleCoercion c1 c2) t) = Just (TupleTerm (CoercionTerm c1 t) (CoercionTerm c2 t))
-- STEP-DISTARR
eval (Application (CoercionTerm (DistArrow _ _ _) (TupleTerm t1 t2)) t3) = Just (TupleTerm (Application t1 t3) (Application t2 t3))
-- STEP-DISTRCD
eval (CoercionTerm (DistLabel l _ _) (TupleTerm (Assign l1 t1) (Assign l2 t2)))
  | l == l1 && l1 == l2 = Just (Assign l (TupleTerm t1 t2))
  | otherwise = Nothing
-- STEP-PROJL
eval (CoercionTerm (Project1 _ _) (TupleTerm t1 t2)) = Just t1
-- STEP-PROJR
eval (CoercionTerm (Project2 _ _) (TupleTerm t1 t2)) = Just t2
-- STEP-CRCD
eval (CoercionTerm (RecordCoercion l c) (Assign l1 t))
  | l == l1 = Just (Assign l (CoercionTerm c t))
  | otherwise = Nothing
-- STEP-BETA
eval (Application (LambdaTerm x xt e) t) = Just e' where e' = replaceVar e x t
-- STEP-PROJRCD
eval (Extract (Assign l t) l1)
  | l == l1 = Just t
  | otherwise = Nothing
-- STEP-APP1
eval (Application e1 e2) = Just (Application e1' e2) where Just e1' = eval e1
-- STEP-APP2
eval (Application e1 e2) = Just (Application e1 e2') where Just e2' = eval e2
-- STEP-PAIR1
eval (TupleTerm e1 e2) = Just (TupleTerm e1' e2) where Just e1' = eval e1
-- STEP-PAIR2
eval (TupleTerm e1 e2) = Just (TupleTerm e1 e2') where Just e2' = eval e2
-- STEP-CAPP
eval (CoercionTerm c e) = Just (CoercionTerm c e') where Just e' = eval e
-- STEP-RCD1
eval (Assign l e) = Just (Assign l e') where Just e' = eval e
-- STEP-RCD2
eval (Extract e l) = Just (Extract e' l) where Just e' = eval e

fullEval :: Term -> Term
fullEval t = case eval t of
  Just st -> fullEval st
  Nothing -> t

typeFromContext :: Context -> Term -> Maybe Type
typeFromContext Empty _ = Nothing
typeFromContext (Extended c te ty) t
  | t == te = Just ty
  | otherwise = typeFromContext c t

termType :: Context -> Term -> Maybe Type
-- TYP-UNIT
termType _ UnitTerm = Just UnitType
-- TYP-LIT
termType _ (Num _) = Just NatType
-- TYP-VAR
termType c (Var x) = typeFromContext c (Var x)
-- TYP-ABS
termType c (LambdaTerm x xt e) = case typeFromContext (Extended c (Var x) xt) e of
  Just et -> Just (FunctionType xt et)
  Nothing -> Nothing
-- TYP-APP
termType c (Application e1 e2) = if t1 == t3 then Just t2 else Nothing where
    Just (FunctionType t1 t2) = typeFromContext c e1
    Just t3 = typeFromContext c e2
-- TYP-PAIR
termType c (TupleTerm e1 e2) = Just (TupleType t1 t2) where
  Just t1 = typeFromContext c e1
  Just t2 = typeFromContext c e2
-- TYP-CAPP
termType c (CoercionTerm co e) = if t1 == t2 then Just t' else Nothing where
  Just t1 = typeFromContext c e
  Just (t2, t') = coercionType co
-- TYP-RCD
termType c (Assign l e) = Just (RecordType l t) where
  Just t = typeFromContext c e
-- TYP--PROJ
termType c (Extract e l) = Just t where
  Just (RecordType l t) = typeFromContext c e

coercionType :: Coercion -> Maybe (Type, Type)
-- COTYP-REFL
coercionType (Id t) = Just (t, t)
-- COTYP-TRANS
coercionType (Composition c1 c2) = if t2 == t2' then Just (t1, t3) else Nothing where
  Just (t2, t3) = coercionType c1
  Just (t1, t2') = coercionType c2
-- COTYP-TOP
coercionType (Top t) = Just (t, UnitType)
-- COTYP-TOPARR
coercionType TopArrow = Just (UnitType, FunctionType UnitType UnitType)
-- COTYP-TOPRCD
coercionType (TopLabel l) = Just (UnitType, RecordType l UnitType)
-- COTYP-ARR
coercionType (Function c1 c2) = Just (FunctionType t1 t2, FunctionType t1' t2') where
  Just (t1', t1) = coercionType c1
  Just (t2, t2') = coercionType c2
-- COTYP-PAIR
coercionType (TupleCoercion c1 c2) = if t1 == t1' then Just (t1, TupleType t2 t3) else Nothing where
  Just (t1, t2) = coercionType c1
  Just (t1', t3) = coercionType c2
-- COTYP-PROJL
coercionType (Project1 t1 t2) = Just (TupleType t1 t2, t1)
-- COTYP-PROJR
coercionType (Project2 t1 t2) = Just (TupleType t1 t2, t2)
-- COTYP-RCD
coercionType (RecordCoercion l c) = Just (RecordType l t1, RecordType l t2) where
  Just (t1, t2) = coercionType c
-- COTYP-DISTRCD
coercionType (DistLabel l t1 t2) = Just (TupleType (RecordType l t1) (RecordType l t2), RecordType l (TupleType t1 t2))
-- COTYP-DISTARR
coercionType (DistArrow t1 t2 t3) = Just (TupleType (FunctionType t1 t2) (FunctionType t1 t3), FunctionType t1 (TupleType t2 t3))
