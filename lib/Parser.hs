-- | Convert the sexp tree into a @Term@ datatype.
module Parser where

import Lexer as L
import Sexp
import Types hiding (Node, name)
import qualified Types as T
import Utils

import Prelude hiding (pi)
import Data.Bifunctor
import Data.Text hiding (map, length, reverse, unsnoc, foldl1)
import Text.Parsec hiding ((<|>), ParseError)
import qualified Text.Parsec as Parsec

data LexerParserError
  = ErrLex Parsec.ParseError
  | ErrParse ParseError
  | ErrNothingToParse
  deriving Show

data ParseError
  = PEBinding TokenTree
  | PEVar TokenTree
  | PELambda TokenTree
  | PEPi TokenTree
  | PEApp TokenTree
  | PETypeUniv TokenTree
  | PECase TokenTree
  | PECaseDupCtors [(Name, CaseTerm)]
  | PECaseTerm TokenTree
  | PEName TokenTree
  | PEDefinition TokenTree
  | PEData TokenTree
  | PEDataDupCtors [(Name, Term)]
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
app (SexpTree (x:xs)) = foldl1 App <$> (mapM term (x:xs))
app t = Left $ PEApp t

typeUniv :: TokenTree -> Either ParseError Term
typeUniv (SexpTree [Node Type, Node (Number n)]) | n >= 0 = Right (Ty (fromInteger n))
typeUniv t = Left $ PETypeUniv t

case' :: TokenTree -> Either ParseError Term
case' (SexpTree (Node L.Case:e:m:cs))
  = T.Case <$> term e <*> term m
  <*> (fromListNoDups PECaseDupCtors =<< traverse caseTerm cs)
case' t = Left $ PECase t

caseTerm :: TokenTree -> Either ParseError (Constructor, CaseTerm)
caseTerm (SexpTree [SexpTree (Node (Identifier ctor):vars), body]) =
  (Specified ctor,) <$> (CaseTerm  <$> traverse name vars <*> term body)
caseTerm t = Left $ PECaseTerm t

name :: TokenTree -> Either ParseError Name
name (Node (Identifier n)) = pure (Specified n)
name t = Left $ PEName t

definition :: TokenTree -> Either ParseError Definition
definition (SexpTree [Node Define, Node (Identifier name), ty, body]) =
  Definition (Specified name) <$> term ty <*> term body
definition t = Left $ PEDefinition t

data' :: TokenTree -> Either ParseError DataDecl
data' (SexpTree (Node Data : Node (Identifier name) : ty : ctors)) =
  DataDecl (Specified name) <$> term ty
  <*> (fromListNoDups PEDataDupCtors =<< traverse constructor ctors)
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

unsnoc :: [a] -> Maybe ([a], a)
unsnoc (reverse -> (x:xs)) = Just (reverse xs, x)
unsnoc _ = Nothing

parseFile :: Text -> Either LexerParserError ([TopLevel], Term)
parseFile t = f =<< first ErrLex (parse (many sexpTree) "" =<< parse lexer "" t)
  where
    f xs = case (unsnoc xs) of
      Nothing -> Left ErrNothingToParse
      Just (topLevels, t) -> do
        tls <- first ErrParse (sequence (topLevel <$> topLevels))
        t' <- first ErrParse (term t)
        pure (tls, t')
