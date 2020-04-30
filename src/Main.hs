{-# OPTIONS_GHC -Wall #-}

module Main (main) where

import Language.Target
import Language.Source.Parser
import Language.Source.Renamer
import Language.Source.TypeCheck

main :: IO ()
main = do
  input <- getLine
  let rawExp = parseExpr input
      (renamed, maxVar) = rnExpr rawExp
  case inference renamed of
    Nothing -> putStrLn ("Inference failed")
    Just (ty, term) -> do
      print ty
      print term
      print $ fst $ eval maxVar term
      print $ tcTerm term
