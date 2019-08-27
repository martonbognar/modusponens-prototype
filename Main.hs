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
      (renamed, maxVar) = rnFullExpr EmptyRnEnv 0 rawExp
  case inference Syntax.Empty renamed of
    Nothing -> print "Inference failed"
    Just (ty, term) -> do
      print $ fullEval maxVar term
      print $ termType LambdaC.Empty term
