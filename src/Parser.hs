module Parser where

import Lexer as L
import Types as T

import Prelude hiding (pi)
import Control.Monad
import Data.Text
import Text.Parsec
import Text.Parsec.Text

type TokParser = Parsec [Token] ()

expectedTok :: Token -> TokParser ()
expectedTok t = tokenPrim show (\p _ _ -> p) (\t' -> if (t' == t) then Just () else Nothing)

identifier :: TokParser Name
identifier = tokenPrim show (\p _ _ -> p) (\case
                                              Identifier s -> Just (Specified s)
                                              _ -> Nothing)

capIdentifier :: TokParser Name
capIdentifier = tokenPrim show (\p _ _ -> p) (\case
                                                 CapIdent s -> Just (Specified s)
                                                 _ -> Nothing)

num :: TokParser Integer
num = tokenPrim show (\p _ _ -> p) (\case
                                       Number n -> Just n
                                       _ -> Nothing)

var :: TokParser Term
var = Var <$> identifier

binding :: TokParser Binding
binding = do
  expectedTok OpenParen
  v <- identifier
  expectedTok HasType
  ty <- term
  expectedTok CloseParen
  return (v, ty)

lambda :: TokParser Term
lambda = do
  expectedTok Lambda
  b <- binding
  expectedTok RightSingleArrow
  body <- term
  return (Lam b body)

pi :: TokParser Term
pi = do
  b <- binding
  expectedTok RightSingleArrow
  res <- term
  return (Pi b res)

app :: TokParser Term
app = do
  --TODO: implement precedence rules to make this match
  a <- parenthisedTerm
  b <- term
  return (App a b)

typeUniv :: TokParser Term
typeUniv = do
  expectedTok L.Type
  n <- num
  guard (n >= 0)
  return (Ty (fromInteger n))

case' :: TokParser Term
case' = do
  expectedTok L.Case
  e <- parenthisedTerm
  expectedTok Of
  terms <- many caseTerm
  return (T.Case e terms)
  where
    caseTerm :: TokParser CaseTerm
    caseTerm = do
      expectedTok Pipe
      ctor <- capIdentifier
      vars <- many binding
      expectedTok RightDoubleArrow
      e <- parenthisedTerm
      return (CaseTerm ctor vars e)

parenthisedTerm :: TokParser Term
parenthisedTerm = between (expectedTok OpenParen) (expectedTok CloseParen) term

term :: TokParser Term
term = app <|> lambda <|> typeUniv <|> var <|> pi <|> case' <|> parenthisedTerm

parser :: Text -> Either ParseError Term
parser = parse lexer "" >=> parse (term <* eof) ""
