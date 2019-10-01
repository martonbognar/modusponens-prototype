module Main where

import CommonTypes
import LambdaC
import Parser
import PrettyPrinter
import RawSyntax
import Renamer
import Syntax
import TypeCheck

main :: IO ()
main = do
  input <- getLine
  let rawExp = parseExpr input
      (renamed, maxVar) = rnExpr rawExp
  case inference renamed of
    Nothing -> print "Inference failed"
    Just (ty, term) -> do
      print ty
      print  term
      print $ fst $ eval maxVar term
      print $ tcTerm term
