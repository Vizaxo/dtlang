module Test.Interpreter where

import Test.Generators

import Examples
import Interpreter
import TypeCheck
import Term

import Data.Either
import Test.QuickCheck

testIdReturnsArg
  = forAll genWellTyped $
  \prog -> let (Right progT) = typeCheck [] prog
           in (Right prog) === interpret ((id' `App` progT) `App` prog)

testWellTypedInterpretsRight
  = forAll genWellTyped $
  \prog -> isRight $ interpret prog
