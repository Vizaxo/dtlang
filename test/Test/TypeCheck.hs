module Test.TypeCheck where

import Test.Generators

import Examples
import TypeCheck
import Types

import Data.Either
import Test.QuickCheck

testGenWellTyped
  = forAll (genWellTyped genVInt) $
    \prog -> isRight $ typeCheck [] prog

testIdPreservesType
  = forAll (genWellTyped genVInt) $
    \prog -> let (Right progT) = typeCheck [] prog
             in Right progT === typeCheck [] ((id' `App` progT) `App` prog)
