module Main where

import qualified Data.Text as T
import System.Directory
import System.Environment
import System.Exit
import System.IO.Temp
import System.Process

import Compiler
import Examples
import Parser
import TC
import TypeCheck
import Utils

main :: IO ()
main = getArgs >>= \case
  [srcfile, "-o", outfile] -> do
    src <- readFile srcfile
    ctx <- handleErrM defaultCtx $
      \e -> putStrLn "Error type checking default context:" >> print e >> exitFailure
    term <- handleErrM (parseTerm (T.pack src)) $
      \e -> putStrLn "Error parsing file:" >> print e >> exitFailure
    case runTC ctx (typeCheck term) of
      Left e ->
        putStrLn "Error type checking term:" >> print e >> exitFailure
      Right ty -> putStrLn $ "Term had type " <> show ty
    cSrc <- handleErrM (compileToC ctx term) $
        \e -> putStrLn "Error type checking term:" >> print e >> exitFailure
    cSrcFile <- writeSystemTempFile ("dtlang-" <> outfile <> ".c") cSrc
    workingDir <- getCurrentDirectory
    exitWith =<< system ("gcc -I" <> workingDir <> " '" <> cSrcFile <> "' -o '" <> outfile <> "'")
  _ -> getProgName >>= \p -> putStrLn $ "Usage: " <> p <> " srcfile.dtlang -o outfile"
