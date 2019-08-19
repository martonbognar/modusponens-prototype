type Variable = String
type Label    = String

data Type = NatType |
            UnitType |
            TupleType Type Type |
            FunctionType Type Type |
            RecordType Label Type

data Context = Empty |
               Extended Context Variable Type

data Term = Var Variable |
            Num Int |
            UnitTerm |
            LambdaTerm Variable Term |
            Consecutive Term Term |
            TupleTerm Term Term |
            Assign Label Term |
            Extract Term Label |
            CoercionTerm Coercion Term

data Coercion = Id |
                Composition Coercion Coercion |
                Top |
                TopArrow |
                TopLabel Label |
                Function Coercion Coercion |
                TupleCoercion Coercion Coercion |
                Project1 |
                Project2 |
                RecordCoercion Label Coercion |
                DistLabel Label |
                DistArrow

data Value = LambdaValue Variable Type Term |
             UnitValue |
             NatValue Int |
             TupleValue Value Value |
             CoercionValue Coercion Coercion Value |
             DistArrowValue Value |
             TopArrowValue Value

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
  show (LambdaTerm v t)    = "\\" ++ show v ++ "." ++ show t
  show (Consecutive t1 t2) = show t1 ++ " " ++ show t2
  show (TupleTerm t1 t2)   = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (Assign l t)        = "{" ++ show l ++ " = " ++ show t ++ "}"
  show (Extract t l)       = show t ++ "." ++ show l
  show (CoercionTerm c t)  = show c ++ " " ++ show t

instance Show Coercion where
  show Id                    = "id"
  show (Composition c1 c2)   = show c1 ++ " . " ++ show c2
  show Top                   = "top"
  show TopArrow              = "top->"
  show (TopLabel l)          = "top{" ++ show l ++ "}"
  show (Function c1 c2)      = show c1 ++ " -> " ++ show c2
  show (TupleCoercion c1 c2) = "(" ++ show c1 ++ ", " ++ show c2 ++ ")"
  show Project1              = "PI1"
  show Project2              = "PI2"
  show (RecordCoercion l c)  = "{" ++ show l ++ " : " ++ show c ++ "}"
  show (DistLabel l)         = "dist{" ++ show l ++ "}"
  show DistArrow             = "dist->"

instance Show Value where
  show (LambdaValue v ty te)   = "\\{" ++ show v ++ " : " ++ show ty ++ "}" ++ "." ++ show te
  show UnitValue               = "()"
  show (NatValue i)            = show i
  show (TupleValue v1 v2)      = "(" ++ show v1 ++ ", " ++ show v2 ++ ")"
  show (CoercionValue c1 c2 v) = "(" ++ show c1 ++ " -> " ++ show c2 ++ ") " ++ show v
  show (DistArrowValue v)      = "dist-> " ++ show v
  show (TopArrowValue v)       = "top-> " ++ show v
