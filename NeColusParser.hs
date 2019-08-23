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

ty :: Parser NC.Type
ty = parens ty
     <|> tyNat
     <|> tyTop
     <|> tyArr
     <|> tyIs
     <|> tyRec

-- | Parse a type "Nat".
tyNat :: Parser NC.Type
tyNat = reserved "Nat" *> pure NC.TyNat

-- | Parse the top type "T".
tyTop :: Parser NC.Type
tyTop = reserved "T" *> pure NC.TyTop

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
     e <- expr
     return $ NC.ExAbs x e

exApp :: Parser NC.Expression
exApp =
  do reservedOp "|"
     e1 <- expr
     reservedOp "<-"
     e2 <- expr
     reservedOp "|"
     return $ NC.ExApp e1 e2

exMerge :: Parser NC.Expression
exMerge =
  do reservedOp "/"
     e1 <- expr
     reservedOp ",,"
     e2 <- expr
     reservedOp "/"
     return $ NC.ExMerge e1 e2

exAnn :: Parser NC.Expression
exAnn =
  do reservedOp "["
     e <- expr
     reservedOp ":"
     t <- ty
     reservedOp "]"
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
  do reservedOp ";"
     e <- expr
     reservedOp "."
     l <- identifier
     reservedOp ";"
     return $ NC.ExRecFld e l


parseString :: String -> NC.Expression
parseString str =
  case parse expr "" str of
    Left e  -> error $ show e
    Right r -> r
