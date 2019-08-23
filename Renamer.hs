module Renamer where

import CommonTypes
import qualified RawSyntax as Raw
import Syntax

translateType :: Raw.Type -> Type
translateType Raw.TyNat         = TyNat
translateType Raw.TyTop         = TyTop
translateType (Raw.TyArr t1 t2) = TyArr (translateType t1) (translateType t2)
translateType (Raw.TyIs t1 t2)  = TyIs (translateType t1) (translateType t2)
translateType (Raw.TyRec l t)   = TyRec l (translateType t)

rename :: Raw.Expression -> Expression
rename (Raw.ExVar (Raw.MkRawVar v))   = ExVar (MkVar 42)
rename (Raw.ExLit i)                  = ExLit i
rename Raw.ExTop                      = ExTop
rename (Raw.ExAbs (Raw.MkRawVar v) e) = ExAbs (MkVar 42) (rename e)
rename (Raw.ExApp e1 e2)              = ExApp (rename e1) (rename e2)
rename (Raw.ExMerge e1 e2)            = ExMerge (rename e1) (rename e2)
rename (Raw.ExAnn e t)                = ExAnn (rename e) (translateType t)
rename (Raw.ExRec l e)                = ExRec l (rename e)
rename (Raw.ExRecFld e l)             = ExRecFld (rename e) l
