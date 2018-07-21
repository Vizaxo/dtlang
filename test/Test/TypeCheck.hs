module Test.TypeCheck where

import Test.Generators

import Examples
import TypeCheck
import Term

import Data.Either
import Test.QuickCheck

testGenWellTyped
  = forAll genWellTyped $
    \prog -> isRight $ typeCheck [] prog

testIdPreservesType
  = forAll genWellTyped $
    \prog -> let progT = typeCheck [] prog
             --in Right progT === typeCheck [] ((id' `App` progT) `App` prog)
             in progT === typeCheck [] (appId prog)

prop_idPreservesType :: WellTyped Int -> Property
prop_idPreservesType (WellTyped term) =
  wellTyped term ==> let termT = typeCheck [] term
                     in termT === typeCheck [] (appId term)
