{-# OPTIONS_GHC -Wall #-}

module Parser where

import CommonTypes
import qualified RawSyntax as NC

-- GEORGE: These two seem redundant right now
import Control.Monad ()
import Text.ParserCombinators.Parsec.Expr ()

import Text.Parsec.Prim (Stream, ParsecT)
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

identifier :: Parser String
identifier = Token.identifier lexer

reserved :: String -> Parser ()
reserved   = Token.reserved   lexer

reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer

parens :: Parser a -> Parser a
parens     = Token.parens     lexer

braces :: Parser a -> Parser a
braces     = Token.braces     lexer

integer :: Parser Integer
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
    return (NC.TyRec (MkLabel l) a)

-- ----------------------------------------------------------------------------

-- | Parse a term (highest priority).
pPrimExpr :: Parser NC.Expression
pPrimExpr =   exVar
          <|> exLit
          <|> exTop
          <|> exRec
          <|> parens absHelper

-- | Parse a term variable.
exVar :: Parser NC.Expression
exVar = NC.ExVar . NC.MkRawVar <$> identifier

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
    e <- absHelper
    return (NC.ExRec (MkLabel l) e)

-- ----------------------------------------------------------------------------

pRawVar :: Parser NC.RawVariable
pRawVar = NC.MkRawVar <$> identifier


-- primitive terms  0
-- record selection 1
-- application      2
-- merge            3
-- annotation       4
-- lambda           5

recFldHelper :: Parser NC.Expression
recFldHelper = hetChainl1 pPrimExpr pLabel (NC.ExRecFld <$ reservedOp ".")

appHelper :: Parser NC.Expression
appHelper = chainl1 recFldHelper (pure NC.ExApp)

mergeHelper :: Parser NC.Expression
mergeHelper = chainl1 appHelper (NC.ExMerge <$ reservedOp ",,")

annHelper :: Parser NC.Expression
annHelper = hetChainl1 mergeHelper pType (NC.ExAnn <$ reservedOp ":")

absHelper :: Parser NC.Expression
absHelper =   do reserved "\\"
                 x <- pRawVar
                 reservedOp "."
                 e <- absHelper
                 return (NC.ExAbs x e)
          <|> annHelper


hetChainl1 :: Stream s m t
           => ParsecT s u m a
           -> ParsecT s u m b
           -> ParsecT s u m (a -> b -> a)
           -> ParsecT s u m a
hetChainl1 p1 p2 op = do{ x <- p1; rest x }
                    where
                      rest x = do{ f <- op
                                ; y <- p2
                                ; rest (f x y)
                                }
                              <|> return x

pLabel :: Parser Label
pLabel = MkLabel <$> identifier

-- ----------------------------------------------------------------------------

-- | Parse an expression from a string.
parseExpr :: String -> NC.Expression
parseExpr str =
  case parse (absHelper <* eof) "" str of
  Left e  -> error $ show e
  Right r -> r

-- | Parse a type from a string.
parseType :: String -> NC.Type
parseType str =
  case parse (pType <* eof) "" str of
  Left e  -> error $ show e
  Right r -> r
