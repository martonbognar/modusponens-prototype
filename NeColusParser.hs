module NeColusParser where

import qualified NeColus as NC

import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

languageDef =
    emptyDef { Token.identStart      = letter
             , Token.identLetter     = alphaNum
             , Token.reservedNames   = ["T", "Nat"]
             , Token.reservedOpNames = [".", "\\", "{", "}", ",,", ":", "=", "->", "&", "[", "]", "/"]
             }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
integer    = Token.integer    lexer

ty :: Parser NC.Type
ty = parens ty
     <|> tyNat
     <|> tyTop
     <|> tyArr
     <|> tyIs
     <|> tyRec

tyNat :: Parser NC.Type
tyNat =
  do reserved "Nat"
     return NC.TyNat

tyTop :: Parser NC.Type
tyTop =
  do reserved "T"
     return NC.TyTop

tyArr :: Parser NC.Type
tyArr =
  do reservedOp "["
     a <- ty
     reservedOp "->"
     b <- ty
     reservedOp "]"
     return $ NC.TyArr a b

tyIs :: Parser NC.Type
tyIs =
  do reservedOp "/"
     a <- ty
     reservedOp "&"
     b <- ty
     reservedOp "/"
     return $ NC.TyIs a b

tyRec :: Parser NC.Type
tyRec =
  do reserved "{"
     l <- identifier
     reservedOp ":"
     a <- ty
     reserved "}"
     return $ NC.TyRec l a

expr :: Parser NC.Expression
expr = parens expr
            <|> exVar
            <|> exLit
            <|> exTop
            <|> exAbs
            <|> exApp
            <|> exMerge
            <|> exAnn
            <|> exRec
            <|> exRecFld

exVar :: Parser NC.Expression
exVar =
  do var <- identifier
     return $ NC.ExVar var

exLit :: Parser NC.Expression
exLit =
  do i <- integer
     return $ NC.ExLit (fromIntegral i)

exTop :: Parser NC.Expression
exTop =
  do reserved "T"
     return NC.ExTop

exAbs :: Parser NC.Expression
exAbs =
  do reserved "\\"
     x <- identifier
     reservedOp "."
     e <- expr
     return $ NC.ExAbs x e

exApp :: Parser NC.Expression
exApp =
  do e1 <- expr
     e2 <- expr
     return $ NC.ExApp e1 e2

exMerge :: Parser NC.Expression
exMerge =
  do e1 <- expr
     reservedOp ",,"
     e2 <- expr
     return $ NC.ExMerge e1 e2

exAnn :: Parser NC.Expression
exAnn =
  do e <- expr
     reservedOp ":"
     t <- ty
     return $ NC.ExAnn e t

exRec :: Parser NC.Expression
exRec =
  do reserved "{"
     l <- identifier
     reservedOp "="
     e <- expr
     reserved "}"
     return $ NC.ExRec l e

exRecFld :: Parser NC.Expression
exRecFld =
  do e <- expr
     reservedOp "."
     l <- identifier
     return $ NC.ExRecFld e l


parseString :: String -> NC.Expression
parseString str =
  case parse expr "" str of
    Left e  -> error $ show e
    Right r -> r
