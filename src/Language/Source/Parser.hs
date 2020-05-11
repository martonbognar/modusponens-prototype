{-# OPTIONS_GHC -Wall #-}

module Language.Source.Parser where

import Data.Label
import Text.Parsec.Prim (Stream, ParsecT)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import qualified Language.Source.RawSyntax as NC

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
           , Token.reservedNames   = ["T", "Nat", "Bool", "true", "false"]
           , Token.reservedOpNames = [
               ".", "\\", ",,", ":", "->", "&", "\\/", "/\\"
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

-- | Create a parser for booleans in the language.
bool :: Parser NC.Expression
bool =   (reserved "true"  *> pure NC.ExTrue)
     <|> (reserved "false" *> pure NC.ExFalse)

pRawVar :: Parser NC.RawVariable
pRawVar = NC.MkRawVar <$> identifier

-- | Parse a type (highest priority).
pPrimTy :: Parser NC.Type
pPrimTy =   tyNat
        <|> tyBool
        <|> tyTop
        <|> tyRec
        <|> tyAbs
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

-- | Parse a type "Bool".
tyBool :: Parser NC.Type
tyBool = reserved "Bool" *> pure NC.TyBool

-- | Parse the top type "T".
tyTop :: Parser NC.Type
tyTop = reserved "T" *> pure NC.TyTop

-- | Parse a record type.
tyRec :: Parser NC.Type
tyRec = braces $ do
    l <- pLabel
    reservedOp ":"
    a <- pPrimTy
    return (NC.TyRec l a)

tyAbs :: Parser NC.Type
tyAbs = do
    reservedOp "\\/"
    (x, a) <- (parens $ do
      x <- pRawVar
      reservedOp "*"
      a <- pPrimTy
      return (x, a)
      )
    reservedOp "."
    b <- pPrimTy
    return (NC.TyAbs x a b)

-- ----------------------------------------------------------------------------

-- | Parse a term (highest priority).
pPrimExpr :: Parser NC.Expression
pPrimExpr =   exLit
          <|> exBool
          <|> exTop
          <|> exVar
          <|> exRec
          <|> parens pExpr

-- | Parse a term variable.
exVar :: Parser NC.Expression
exVar = NC.ExVar . NC.MkRawVar <$> identifier

-- | Parse a natural number.
exLit :: Parser NC.Expression
exLit = NC.ExLit . fromIntegral <$> integer

-- | Parse a boolean value.
exBool :: Parser NC.Expression
exBool = bool

-- | Parse the top expression.
exTop :: Parser NC.Expression
exTop = reserved "T" *> pure NC.ExTop

-- | Parse a record.
exRec :: Parser NC.Expression
exRec = braces $ do
    l <- identifier
    reservedOp "="
    e <- pExpr
    return (NC.ExRec (MkLabel l) e)

-- ----------------------------------------------------------------------------

-- Operator precedence:
-- primitive terms  0
-- record selection 1
-- application      2
-- type application 3
-- merge            4
-- annotation       5
-- lambda           6
-- type abstraction 7

-- | Parse a term (lowest priority).
pExpr :: Parser NC.Expression
pExpr = pExAbs <|> pExprTyAbs <|> pExprAnn
  where
    pExAbs :: Parser NC.Expression
    pExAbs = do
      reservedOp "\\"
      x <- pRawVar
      reservedOp "."
      e <- pExpr
      return (NC.ExAbs x e)

    pExprTyAbs :: Parser NC.Expression
    pExprTyAbs = do
        reservedOp "/\\"
        (x, a) <- (parens $ do
          x <- pRawVar
          reservedOp "*"
          a <- pPrimTy
          return (x, a)
          )
        reservedOp "."
        b <- pExpr
        return (NC.ExTyAbs x a b)

    pExprRecFld :: Parser NC.Expression
    pExprRecFld = hetChainl1 pPrimExpr pLabel (NC.ExRecFld <$ reservedOp ".")

    pExprApp :: Parser NC.Expression
    pExprApp = chainl1 pExprRecFld (pure NC.ExApp)
    -- pExprApp = chainl1 pPrimExpr (pure NC.ExApp)

    pExprTyApp :: Parser NC.Expression
    pExprTyApp = hetChainl1 pExprApp pType (pure NC.ExTyApp)

    pExprMerge :: Parser NC.Expression
    pExprMerge = chainl1 pExprTyApp (NC.ExMerge <$ reservedOp ",,")

    pExprAnn :: Parser NC.Expression
    pExprAnn = hetChainl1 pExprMerge pType (NC.ExAnn <$ reservedOp ":")

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
