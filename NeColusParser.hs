-- {-# OPTIONS_GHC -Wall #-}
-- GEORGE: Enable the warnings and add the proper type signatures! :-)

module NeColusParser where

import qualified NeColus as NC

-- GEORGE: These two seem redundant right now
import Control.Monad ()
import Text.ParserCombinators.Parsec.Expr ()

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

languageDef :: LanguageDef st
languageDef =
    emptyDef { Token.identStart      = letter
             , Token.identLetter     = alphaNum
             , Token.reservedNames   = ["T", "Nat"]
             , Token.reservedOpNames = [
                 ".", "\\", "{", "}", ",,", ":",
                 "=", "->", "&", "[", "]", "/", "|", ";", "<-"
               ]
             }

lexer :: Token.TokenParser st
lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
braces     = Token.braces     lexer
integer    = Token.integer    lexer

-- | Parse a type (highest priority).
pPrimTy :: Parser NC.Type
pPrimTy =   tyNat
        <|> tyTop
        <|> tyRec
        <|> parens pType

-- | Parse a type (lowest priority).
pType :: Parser NC.Type
pType = chainr1
          (chainl1 pPrimTy (NC.TyIs <$ reservedOp "&"))
          (NC.TyArr <$ reservedOp "->")

-- ----------------------------------------------------------------------------

-- | Parse a type "Nat".
tyNat :: Parser NC.Type
tyNat = reserved "Nat" *> pure NC.TyNat

-- | Parse the top type "T".
tyTop :: Parser NC.Type
tyTop = reserved "T" *> pure NC.TyTop

-- | Parse a record.
tyRec :: Parser NC.Type
tyRec = braces $ do
  l <- identifier
  reservedOp ":"
  a <- pPrimTy
  return (NC.TyRec l a)

-- ----------------------------------------------------------------------------

-- | Parse a term (highest priority).
pPrimExpr :: Parser NC.Expression
pPrimExpr =   exVar
          <|> exLit
          <|> exTop
          <|> exRec
          <|> parens pExpr

-- | Parse a term variable.
exVar :: Parser NC.Expression
exVar = NC.ExVar <$> identifier

-- | Parse a natural number.
exLit :: Parser NC.Expression
exLit = NC.ExLit . fromIntegral <$> integer

-- | Parse the top expression.
exTop :: Parser NC.Expression
exTop = reserved "T" *> pure NC.ExTop

-- | Parse a record.
exRec :: Parser NC.Expression
exRec = braces $ do
  l <- identifier
  reservedOp "="
  e <- expr1st
  return (NC.ExRec l e)

-- ----------------------------------------------------------------------------

pExpr :: Parser NC.Expression
pExpr = error "Not implemented yet."


-- ----------------------------------------------------------------------------


expr1st :: Parser NC.Expression
expr1st = exVar
          <|> exLit
          <|> exTop
          <|> exRec
          <|> parens expr2nd

expr2nd :: Parser NC.Expression
expr2nd = exAbs
          <|> try exMerge
          <|> try exAnn
          <|> try exRecFld
          <|> exApp

exAbs :: Parser NC.Expression
exAbs =
  do reserved "\\"
     x <- identifier
     reservedOp "."
     e <- expr1st
     return $ NC.ExAbs x e

exApp :: Parser NC.Expression
exApp =
  do e1 <- expr1st
     e2 <- expr1st
     return $ NC.ExApp e1 e2

exMerge :: Parser NC.Expression
exMerge =
  do e1 <- expr1st
     reservedOp ",,"
     e2 <- expr1st
     return $ NC.ExMerge e1 e2

exAnn :: Parser NC.Expression
exAnn =
  do e <- expr1st
     reservedOp ":"
     t <- pType
     return $ NC.ExAnn e t

exRecFld :: Parser NC.Expression
exRecFld =
  do e <- expr1st
     reservedOp "."
     l <- identifier
     return $ NC.ExRecFld e l

-- | Parse an expression from a string.
parseExpr :: String -> NC.Expression
parseExpr str =
  case parse expr1st "" str of
    Left e  -> error $ show e
    Right r -> r

-- | Parse a type from a string.
parseType :: String -> NC.Type
parseType str =
  case parse pType "" str of
    Left e  -> error $ show e
    Right r -> r
