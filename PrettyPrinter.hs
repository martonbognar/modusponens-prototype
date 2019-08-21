{-# OPTIONS_GHC -Wall #-}

module PrettyPrinter where

import Text.PrettyPrint

arrow :: Doc
arrow = text "→"

dot :: Doc
dot = text "."

commaSep :: [Doc] -> [Doc]
commaSep = punctuate comma

parensList :: [Doc] -> Doc
parensList = parens . hsep . commaSep
