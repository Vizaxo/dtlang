module Main where

import Test.TypeCheck

import Test.QuickCheck

main :: IO ()
main = do
  quickCheck testGenWellTyped
  quickCheck testIdPreservesType
