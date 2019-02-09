module Main where

import Examples
import Interpret
import Parser
import TC
import TypeCheck
import Types

import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Text (Text, pack)

data ReplError
  = ErrLexParse LexerParserError
  | ErrType TypeError
  | ErrCtx TypeError
  | ErrRun TypeError
  | Unsupported
  deriving Show

mapError :: Monad m => (e -> e') -> Either e a -> ExceptT e' m a
mapError mkErr = withExceptT mkErr . ExceptT . return

command :: Text -> ExceptT ReplError (State Context) String
command s = do
  mapError ErrLexParse (replParser s) >>= \case
    Left t -> do
      ctx <- get
      mapError ErrType (runTC ctx (typeCheckTopLevel t)) >>= put
      return (show t)
    Right t -> do
      ctx <- get
      ty <- mapError ErrType (runTC ctx (typeCheck t))
      term <- mapError ErrRun (interpret ctx t)
      return (showTerm term ty)
  where showTerm term ty = show term <> " : " <> show ty

showCommand :: Either ReplError String -> String
showCommand (Left err) = "Error: " <> show err
showCommand (Right s) = s

repl :: String -> String
repl s = showCommand $ do
  ctx <- first ErrCtx defaultCtx
  return (unlines . map showCommand . flip evalState ctx . mapM run . lines $ s)
  where
    run :: String -> State Context (Either ReplError String)
    run = runExceptT . command . pack

main :: IO ()
main = interact repl
