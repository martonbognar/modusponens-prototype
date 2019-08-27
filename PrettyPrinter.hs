{-# OPTIONS_GHC -Wall #-}

module PrettyPrinter where

import Text.PrettyPrint
import CommonTypes

arrow :: Doc
arrow = text "→"

dot :: Doc
dot = text "."

-- | Convert a list of elements to comma separated values.
commaSep :: [Doc] -> [Doc]
commaSep = punctuate comma

-- | Convert a list of elements to comma separated values in parentheses.
parensList :: [Doc] -> Doc
parensList = parens . hsep . commaSep

class PrettyPrint a where
  ppr :: a -> Doc

class PrettyPrintList a where
  pprList :: [a] -> Doc

instance PrettyPrintList Char where
  pprList = text

instance PrettyPrintList a => PrettyPrint [a] where
  ppr = pprList

instance PrettyPrint Integer where
  ppr = integer

instance PrettyPrint Variable where
  ppr (MkVar i) = ppr "x" <> ppr i

instance PrettyPrint Label where
  ppr (MkLabel l) = ppr l
