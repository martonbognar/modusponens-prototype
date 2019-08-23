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
             , Token.reservedOpNames = [
                 ".", "\\", "{", "}", ",,", ":",
                 "=", "->", "&", "[", "]", "/", "|", ";", "<-"
               ]
             }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
integer    = Token.integer    lexer

ty1st :: Parser NC.Type
ty1st = tyNat
        <|> tyTop
        <|> tyRec
        <|> parens ty2nd

ty2nd :: Parser NC.Type
ty2nd = try tyArr <|> tyIs

-- | Parse a type "Nat".
tyNat :: Parser NC.Type
tyNat = reserved "Nat" *> pure NC.TyNat

-- | Parse the top type "T".
tyTop :: Parser NC.Type
tyTop = reserved "T" *> pure NC.TyTop

tyArr :: Parser NC.Type
tyArr =
  do a <- ty1st
     reservedOp "->"
     b <- ty1st
     return $ NC.TyArr a b

tyIs :: Parser NC.Type
tyIs =
  do a <- ty1st
     reservedOp "&"
     b <- ty1st
     return $ NC.TyIs a b

tyRec :: Parser NC.Type
tyRec =
  do reserved "{"
     l <- identifier
     reservedOp ":"
     a <- ty1st
     reserved "}"
     return $ NC.TyRec l a

expr1st :: Parser NC.Expression
expr1st = exVar
          <|> exLit
          <|> exTop
          <|> exAbs
          <|> exRec
          <|> parens expr2nd

expr2nd :: Parser NC.Expression
expr2nd = try exMerge
          <|> try exAnn
          <|> try exRecFld
          <|> exApp

-- | Parse a term variable.
exVar :: Parser NC.Expression
exVar = NC.ExVar <$> identifier

-- | Parse a natural number.
exLit :: Parser NC.Expression
exLit = NC.ExLit . fromIntegral <$> integer

-- | Parse the top expression.
exTop :: Parser NC.Expression
exTop = reserved "T" *> pure NC.ExTop

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
     t <- ty1st
     return $ NC.ExAnn e t

exRec :: Parser NC.Expression
exRec =
  do reserved "{"
     l <- identifier
     reservedOp "="
     e <- expr1st
     reserved "}"
     return $ NC.ExRec l e

exRecFld :: Parser NC.Expression
exRecFld =
  do e <- expr1st
     reservedOp "."
     l <- identifier
     return $ NC.ExRecFld e l


parseString :: String -> NC.Expression
parseString str =
  case parse expr1st "" str of
    Left e  -> error $ show e
    Right r -> r
