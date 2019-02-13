module Main where

import Control.Comonad
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
    termAnn <- case runTC ctx (typeCheck' term) of
      Left e ->
        putStrLn "Error type checking term:" >> print e >> exitFailure
      Right termAnn -> do
        putStrLn $ "Term had type " <> show (extract termAnn)
        pure termAnn
    cSrc <- handleErrM (compileToC ctx termAnn) $
        \e -> putStrLn "Error type checking term:" >> print e >> exitFailure
    cSrcFile <- writeSystemTempFile ("dtlang-" <> outfile <> ".c") cSrc
    workingDir <- getCurrentDirectory
    exitWith =<< system ("gcc -ggdb -I" <> workingDir <> " '" <> cSrcFile <> "' -o '" <> outfile <> "'")
  _ -> getProgName >>= \p -> putStrLn $ "Usage: " <> p <> " srcfile.dtlang -o outfile"
