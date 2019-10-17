{-# OPTIONS_GHC -Wall #-}

module Language.NeColus.Parser where

import Data.Label
import Text.Parsec.Prim (Stream, ParsecT)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import qualified Language.NeColus.RawSyntax as NC

-- | Return the language definition of the raw syntax.
languageDef :: LanguageDef st
languageDef =
  emptyDef { -- Comments
             Token.commentStart   = "{-" -- Haskell-like
           , Token.commentEnd     = "-}" -- Haskell-like
           , Token.commentLine    = "--" -- Haskell-like
           , Token.nestedComments = True -- Haskell-like

             -- Identifiers
           , Token.identStart      = letter
           , Token.identLetter     = alphaNum <|> char '_'

             -- Operators
           , Token.opStart  = oneOf ":!#$%&*+./<=>?@\\^|-~"
           , Token.opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"

             -- Reserved names and operators
           , Token.reservedNames   = ["T", "Nat"]
           , Token.reservedOpNames = [
               ".", "\\", ",,", ":", "->", "&"
           ]

             -- Case sensitive
           , Token.caseSensitive = True
           }

-- | Create a lexer based on the language definition.
lexer :: Token.TokenParser st
lexer = Token.makeTokenParser languageDef

-- | Create a parser for identifiers in the language.
identifier :: Parser String
identifier = Token.identifier lexer

-- | Create a parser for reserved names in the language.
reserved :: String -> Parser ()
reserved   = Token.reserved   lexer

-- | Create a parser for reserved operators in the language.
reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer

-- | Create a parser for parentheses in the language.
parens :: Parser a -> Parser a
parens     = Token.parens     lexer

-- | Create a parser for braces in the language.
braces :: Parser a -> Parser a
braces     = Token.braces     lexer

-- | Create a parser for integers in the language.
integer :: Parser Integer
integer    = Token.integer    lexer

-- | Parse a type (highest priority).
pPrimTy :: Parser NC.Type
pPrimTy =   tyNat
        <|> tyTop
        -- <|> tyRec
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

-- -- | Parse a record type.
-- tyRec :: Parser NC.Type
-- tyRec = braces $ do
--     l <- pLabel
--     reservedOp ":"
--     a <- pPrimTy
--     return (NC.TyRec l a)

-- ----------------------------------------------------------------------------

-- | Parse a term (highest priority).
pPrimExpr :: Parser NC.Expression
pPrimExpr =   exVar
          <|> exLit
          <|> exTop
          -- <|> exRec
          <|> parens pExpr

-- | Parse a term variable.
exVar :: Parser NC.Expression
exVar = NC.ExVar . NC.MkRawVar <$> identifier

-- | Parse a natural number.
exLit :: Parser NC.Expression
exLit = NC.ExLit . fromIntegral <$> integer

-- | Parse the top expression.
exTop :: Parser NC.Expression
exTop = reserved "T" *> pure NC.ExTop

-- -- | Parse a record.
-- exRec :: Parser NC.Expression
-- exRec = braces $ do
--     l <- identifier
--     reservedOp "="
--     e <- pExpr
--     return (NC.ExRec (MkLabel l) e)

-- ----------------------------------------------------------------------------

-- Operator precedence:
-- primitive terms  0
-- record selection 1
-- application      2
-- merge            3
-- annotation       4
-- lambda           5

-- | Parse a term (lowest priority).
pExpr :: Parser NC.Expression
pExpr = pExAbs <|> pExpr4
  where
    pRawVar :: Parser NC.RawVariable
    pRawVar = NC.MkRawVar <$> identifier

    pExAbs :: Parser NC.Expression
    pExAbs = do
      reservedOp "\\"
      x <- pRawVar
      reservedOp "."
      e <- pExpr
      return (NC.ExAbs x e)

    -- pExpr1 :: Parser NC.Expression
    -- pExpr1 = hetChainl1 pPrimExpr pLabel (NC.ExRecFld <$ reservedOp ".")

    pExpr2 :: Parser NC.Expression
    -- pExpr2 = chainl1 pExpr1 (pure NC.ExApp)
    pExpr2 = chainl1 pPrimExpr (pure NC.ExApp)

    pExpr3 :: Parser NC.Expression
    pExpr3 = chainl1 pExpr2 (NC.ExMerge <$ reservedOp ",,")

    pExpr4 :: Parser NC.Expression
    pExpr4 = hetChainl1 pExpr3 pType (NC.ExAnn <$ reservedOp ":")

-- | Parse a chain of expressions with heterogenous components.
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

-- | Parse a label.
pLabel :: Parser Label
pLabel = MkLabel <$> identifier

-- ----------------------------------------------------------------------------

-- | Parse an expression from a string.
parseExpr :: String -> NC.Expression
parseExpr str =
  case parse (pExpr <* eof) "" str of
  Left e  -> error $ show e
  Right r -> r

-- | Parse a type from a string.
parseType :: String -> NC.Type
parseType str =
  case parse (pType <* eof) "" str of
  Left e  -> error $ show e
  Right r -> r
