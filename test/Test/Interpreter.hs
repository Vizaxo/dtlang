module Test.Interpreter where

import Test.Generators

import Examples
import Interpreter
import TypeCheck
import Types

import Test.QuickCheck

testIdReturnsArg
  = forAll (genWellTyped genVInt) $
  \prog -> let (Right progT) = typeCheck [] prog
           in (Right prog) === interpret ((id' `App` progT) `App` prog)
