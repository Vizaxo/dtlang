module Lexer (Token (..), TokParser, lexer, expect) where

import Control.Monad
import Data.Foldable
import Data.String
import Data.Text
import Text.Parsec
import Text.Parsec.Text
import Text.Read hiding (Number, choice)

data Token
  = Identifier String
  | Number Integer
  | Comment String
  | Lambda
  | RightSingleArrow
  | RightDoubleArrow
  | HasType
  | OpenParen
  | CloseParen
  | Equals
  | Type
  | Case
  | Of
  | Pipe
  | Pi
  | Define
  | Data
  deriving (Eq, Show)

type TokParser = Parsec [Token] ()

reservedWords :: IsString s => [(s, Token)]
reservedWords =
  [ ("lambda", Lambda)
  , ("->", RightSingleArrow)
  , ("=>", RightDoubleArrow)
  , (":", HasType)
  , ("(", OpenParen)
  , (")", CloseParen)
  , ("=", Equals)
  , ("Type", Type)
  , ("case", Case)
  , ("of", Of)
  , ("|", Pipe)
  , ("Pi", Pi)
  , ("define", Define)
  , ("data", Data)
  ]

reserved :: Parser Token
reserved = choice (try . parseReserved <$> reservedWords)
  where
    parseReserved :: (String, t) -> Parser t
    parseReserved (s, t) = t <$ string s

identifier :: Parser Token
identifier = Identifier <$> ((:) <$> letter <*> many alphaNum)

startComment :: Parser ()
startComment = void $ string "{-"

endComment :: Parser ()
endComment = void $ string "-}"

comment :: Parser Token
comment = Comment <$> (startComment *> manyTill anyChar endComment)

num :: Parser Token
num = toNum . fmap pack $ many digit
  where
    toNum :: Parsec Text u Text -> Parsec Text u Token
    toNum m = do
      x <- readMaybe . unpack <$> m
      case x of
        Just n -> return $ Number n
        Nothing -> mzero

tok :: Parser Token
tok = many comment *> (reserved <|> identifier <|> num)

lexer :: Parser [Token]
lexer = spaces *> sepBy tok spaces <* eof

expect :: Token -> TokParser ()
expect t = tokenPrim show (\p _ _ -> p) (\t' -> if (t' == t) then Just () else Nothing)
