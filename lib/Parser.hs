-- | Convert the sexp tree into a @Term@ datatype.
module Parser where

import Lexer as L
import Sexp
import Types hiding (Node)
import qualified Types as T

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
var (Node (Identifier v)) = Just (Var (Specified v))
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
typeUniv (SexpTree [Node Type, Node (Number n)]) | n >= 0 = Just (Ty (fromInteger n))
typeUniv _ = Nothing

case' :: TokenTree -> Maybe Term
case' (SexpTree (Node L.Case:e:cs)) = T.Case <$> term e <*> sequence (map caseTerm cs)
case' _ = Nothing

caseTerm :: TokenTree -> Maybe CaseTerm
caseTerm (SexpTree [SexpTree (Node (Identifier ctor):vars), body]) =
  CaseTerm (Specified ctor) <$> sequence (map binding vars) <*> term body
caseTerm _ = Nothing

definition :: TokenTree -> Maybe Definition
definition (SexpTree [Node Define, Node (Identifier name), ty, body]) =
  Definition (Specified name) <$> term ty <*> term body
definition _ = Nothing

data' :: TokenTree -> Maybe DataDecl
data' (SexpTree (Node Data : Node (Identifier name) : ty : ctors)) =
  DataDecl (Specified name) <$> term ty <*> sequence (map constructor ctors)
data' _ = Nothing

constructor :: TokenTree -> Maybe (Constructor, Type)
constructor (SexpTree [Node (Identifier name), ty])
  = (Specified name,) <$> term ty
constructor _ = Nothing

term :: TokenTree -> Maybe Term
term t = lambda t <|> pi t <|> app t <|> typeUniv t <|> case' t <|> var t

topLevel :: TokenTree -> Maybe TopLevel
topLevel t = (TLData <$> data' t) <|> (TLDef <$> definition t)

type ReplExpr = Either TopLevel Term

replTopLevel :: TokenTree -> Maybe ReplExpr
replTopLevel t = (Left <$> topLevel t) <|> (Right <$> term t)

parser :: Text -> Either LexerParserError TopLevel
parser s = toToplevel $ parse (sexpTree <* eof) "" =<< parse lexer "" s
  where
    toToplevel :: Either ParseError TokenTree -> Either LexerParserError TopLevel
    toToplevel (Left e) = Left (ErrLex e)
    toToplevel (Right t) = maybe (Left ErrParse) Right (topLevel t)

replParser :: Text -> Either LexerParserError ReplExpr
replParser s = toReplExpr $ parse (sexpTree <* eof) "" =<< parse lexer "" s
  where
    toReplExpr :: Either ParseError TokenTree -> Either LexerParserError ReplExpr
    toReplExpr (Left e) = Left (ErrLex e)
    toReplExpr (Right t) = maybe (Left ErrParse) Right (replTopLevel t)
