module Test.TypeCheck where

import Test.Generators

import Examples
import TypeCheck
import Term

import Data.Either
import Test.QuickCheck

prop_genWellTyped :: (Eq v, Show v, Enum v) => WellTyped v -> Bool
prop_genWellTyped (WellTyped term) = wellTyped [] term

prop_idPreservesType :: (Eq v, Show v, Enum v) => WellTyped v -> Property
prop_idPreservesType (WellTyped term) =
  wellTyped [] term ==> let termT = typeCheck [] term
                        in termT === typeCheck [] (appId term)
