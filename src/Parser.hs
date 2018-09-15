-- | Convert the sexp tree into a @Term@ datatype.
module Parser where

import Lexer as L
import Sexp
import Types as T

import Prelude hiding (pi)
import Control.Applicative
import Control.Monad
import Data.Bifunctor
import Data.Text hiding (map)
import Text.Parsec hiding ((<|>))
import Text.Parsec.Text

data LexerParserError
  = ErrLex ParseError
  | ErrParse
  deriving Show

identifier :: TokParser Name
identifier = tokenPrim show (\p _ _ -> p) (\case
                                              Identifier s -> Just (Specified s)
                                              _ -> Nothing)

binding :: TokenTree -> Maybe Binding
binding (SexpTree [Node (Identifier v), ty]) = (Specified v,) <$> term ty
binding _ = Nothing

var :: TokenTree -> Maybe Term
var (SexpTree [Node (Identifier v)]) = Just (Var (Specified v))
var _ = Nothing

lambda :: TokenTree -> Maybe Term
lambda (SexpTree [Node Lambda, bind, body]) = Lam <$> binding bind <*> term body
lambda _ = Nothing

pi :: TokenTree -> Maybe Term
pi (SexpTree [Node L.Pi, bind, ret]) = T.Pi <$> binding bind <*> term ret
pi _ = Nothing

app :: TokenTree -> Maybe Term
--TODO: consider multiple (uncurried) arguments
app (SexpTree [f,x]) = App <$> term f <*> term x
app _ = Nothing

typeUniv :: TokenTree -> Maybe Term
typeUniv (SexpTree [Node L.Type, Node (Number n)]) | n >= 0 = Just (Ty (fromInteger n))
typeUniv _ = Nothing

case' :: TokenTree -> Maybe Term
case' (SexpTree (Node L.Case:e:cs)) = T.Case <$> term e <*> sequence (map caseTerm cs)
case' _ = Nothing

caseTerm :: TokenTree -> Maybe CaseTerm
caseTerm (SexpTree [SexpTree (Node (CapIdent ctor):vars), body]) =
  CaseTerm (Specified ctor) <$> sequence (map binding vars) <*> term body
caseTerm _ = Nothing

term :: TokenTree -> Maybe Term
term t = lambda t <|> pi t <|> app t <|> typeUniv t <|> case' t <|> var t

parser :: Text -> Either LexerParserError Term
parser s = toTerm $ parse (sexpTree <* eof) "" =<< parse lexer "" s
  where
    toTerm :: Either ParseError TokenTree -> Either LexerParserError Term
    toTerm (Left e) = Left (ErrLex e)
    toTerm (Right t) = maybe (Left ErrParse) Right (term t)
