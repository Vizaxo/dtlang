module Main where

import Test.Interpreter
import Test.TypeCheck

import Test.QuickCheck

main :: IO ()
main = do
  quickCheck testGenWellTyped
  quickCheck testIdPreservesType
  quickCheck testIdReturnsArg
  quickCheck testWellTypedInterpretsRight
