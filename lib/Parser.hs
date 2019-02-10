-- | Convert the sexp tree into a @Term@ datatype.
module Parser where

import Lexer as L
import Sexp
import Types hiding (Node)
import qualified Types as T

import Prelude hiding (pi)
import Data.Text hiding (map)
import Text.Parsec hiding ((<|>), ParseError)
import qualified Text.Parsec as Parsec

data LexerParserError
  = ErrLex Parsec.ParseError
  | ErrParse ParseError
  deriving Show

data ParseError
  = PEBinding TokenTree
  | PEVar TokenTree
  | PELambda TokenTree
  | PEPi TokenTree
  | PEApp TokenTree
  | PETypeUniv TokenTree
  | PECase TokenTree
  | PE TokenTree
  | PECaseTerm TokenTree
  | PEDefinition TokenTree
  | PEData TokenTree
  | PEConstructor TokenTree
  deriving Show

identifier :: TokParser Name
identifier = tokenPrim show (\p _ _ -> p) (\case
                                              Identifier s -> Just (Specified s)
                                              _ -> Nothing)

binding :: TokenTree -> Either ParseError Binding
binding (SexpTree [Node (Identifier v), ty]) = (Specified v,) <$> term ty
binding t = Left $ PEBinding t

var :: TokenTree -> Either ParseError Term
var (Node (Identifier v)) = Right (Var (Specified v))
var t = Left $ PEVar t

lambda :: TokenTree -> Either ParseError Term
lambda (SexpTree [Node Lambda, bind, body]) = Lam <$> binding bind <*> term body
lambda t = Left $ PELambda t

pi :: TokenTree -> Either ParseError Term
pi (SexpTree [Node L.Pi, bind, ret]) = T.Pi <$> binding bind <*> term ret
pi t = Left $ PEPi t

app :: TokenTree -> Either ParseError Term
--TODO: consider multiple (uncurried) arguments
app (SexpTree [f,x]) = App <$> term f <*> term x
app t = Left $ PEApp t

typeUniv :: TokenTree -> Either ParseError Term
typeUniv (SexpTree [Node Type, Node (Number n)]) | n >= 0 = Right (Ty (fromInteger n))
typeUniv t = Left $ PETypeUniv t

case' :: TokenTree -> Either ParseError Term
case' (SexpTree (Node L.Case:e:cs)) = T.Case <$> term e <*> sequence (map caseTerm cs)
case' t = Left $ PECase t

caseTerm :: TokenTree -> Either ParseError CaseTerm
caseTerm (SexpTree [SexpTree (Node (Identifier ctor):vars), body]) =
  CaseTerm (Specified ctor) <$> sequence (map binding vars) <*> term body
caseTerm t = Left $ PECaseTerm t

definition :: TokenTree -> Either ParseError Definition
definition (SexpTree [Node Define, Node (Identifier name), ty, body]) =
  Definition (Specified name) <$> term ty <*> term body
definition t = Left $ PEDefinition t

data' :: TokenTree -> Either ParseError DataDecl
data' (SexpTree (Node Data : Node (Identifier name) : ty : ctors)) =
  DataDecl (Specified name) <$> term ty <*> sequence (map constructor ctors)
data' t = Left $ PEData t

constructor :: TokenTree -> Either ParseError (Constructor, Type)
constructor (SexpTree [Node (Identifier name), ty])
  = (Specified name,) <$> term ty
constructor t = Left $ PEConstructor t

infixl 5 <||>
(<||>) :: Either e a -> Either e a -> Either e a
(Left a) <||> b = b
(Right a) <||> b = Right a

term :: TokenTree -> Either ParseError Term
term t = lambda t <||> pi t <||> app t <||> typeUniv t <||> var t <||> case' t 

topLevel :: TokenTree -> Either ParseError TopLevel
topLevel t = (TLData <$> data' t) <||> (TLDef <$> definition t)

type ReplExpr = Either TopLevel Term

replTopLevel :: TokenTree -> Either ParseError ReplExpr
replTopLevel t = (Left <$> topLevel t) <||> (Right <$> term t)

parser :: Text -> Either LexerParserError TopLevel
parser s = toToplevel $ parse (sexpTree <* eof) "" =<< parse lexer "" s
  where
    toToplevel :: Either Parsec.ParseError TokenTree -> Either LexerParserError TopLevel
    toToplevel (Left e) = Left (ErrLex e)
    toToplevel (Right t) = either (Left . ErrParse) Right (topLevel t)

parseTerm :: Text -> Either LexerParserError Term
parseTerm s = toTerm $ parse (sexpTree <* eof) "" =<< parse lexer "" s
  where
    toTerm :: Either Parsec.ParseError TokenTree -> Either LexerParserError Term
    toTerm (Left e) = Left (ErrLex e)
    toTerm (Right t) = either (Left . ErrParse) Right (term t)

replParser :: Text -> Either LexerParserError ReplExpr
replParser s = toReplExpr $ parse (sexpTree <* eof) "" =<< parse lexer "" s
  where
    toReplExpr :: Either Parsec.ParseError TokenTree -> Either LexerParserError ReplExpr
    toReplExpr (Left e) = Left (ErrLex e)
    toReplExpr (Right t) = either (Left . ErrParse) Right (replTopLevel t)
