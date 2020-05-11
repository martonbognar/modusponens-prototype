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
  case rnExpr $ parseExpr input of
    Nothing -> print "error"
    Just renamed -> do
      print renamed
      case inference renamed of
        Nothing -> print "error"
        Just (ty, term) -> do
          print ty
          print term
          print $ eval term
          print $ tcTerm term
