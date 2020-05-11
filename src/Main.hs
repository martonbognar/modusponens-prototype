{-# OPTIONS_GHC -Wall #-}

module Main (main) where

import Language.Target
import Language.Source.Parser
import Language.Source.Renamer
import Language.Source.TypeCheck
import Control.Monad.Except

main :: IO ()
main = do
  input <- getLine
  case runExcept $ rnExpr $ parseExpr input of
    Left err -> print err
    Right (renamed, maxVar) -> do
      print renamed
      case runExcept $ inference renamed maxVar of
        Left err -> print err
        Right ((ty, term), maxVar') -> do
          print ty
          print term
          print $ eval maxVar' term
          print $ tcTerm term
