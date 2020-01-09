{-# OPTIONS_GHC -Wall #-}

module Main (main) where

import Language.LambdaC
import Language.NeColus.Parser
import Language.NeColus.Renamer
import Language.NeColus.TypeCheck

main :: IO ()
main = do
  input <- getLine
  let rawExp = parseExpr input
      (renamed, maxVar) = rnExpr rawExp
  case inference renamed of
    Left err -> putStrLn ("Inference failed: " ++ err)
    Right (ty, term) -> do
      print ty
      print term
      print $ fst $ eval maxVar term
      print $ tcTerm term
