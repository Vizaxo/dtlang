module Main where

import Interpret
import Parser
import TC
import TypeCheck
import Types

import Control.Monad
import Data.Bifunctor
import Data.Text (Text, pack)
import qualified Data.Text as T

data ReplError
  = ErrLexParse LexerParserError
  | ErrType TypeError
  | ErrRun TypeError
  | Unsupported
  deriving Show

command :: Text -> Either ReplError (Term, Term)
command s = do
  (first ErrLexParse $ replParser s) >>= \case
    Left _ -> Left Unsupported
    Right t -> do
      ty <- first ErrType $ runTC $ typeCheck t
      term <- first ErrRun $ interpret emptyCtx t
      return (term, ty)

showCommand :: Either ReplError (Term, Term) -> String
showCommand (Left err) = "Error: " <> show err
showCommand (Right (term, ty)) = show term <> " : " <> show ty

repl :: IO ()
repl = interact (unlines . map (showCommand . command . pack) . lines)

main :: IO ()
main = repl
