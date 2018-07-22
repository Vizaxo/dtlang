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

prop_pairFstPreservesType :: (Eq v, Show v, Enum v) => WellTyped v -> Property
prop_pairFstPreservesType (WellTyped term) =
  wellTyped [] term ==> let (Right termT) = typeCheck [] term
                        in Right termT === typeCheck [] (pair `App` termT `App` term `App` term `App` (fst' `App` termT))

prop_pairSndPreservesType :: (Eq v, Show v, Enum v) => WellTyped v -> Property
prop_pairSndPreservesType (WellTyped term) =
  wellTyped [] term ==> let (Right termT) = typeCheck [] term
                        in Right termT === typeCheck [] (pair `App` termT `App` term `App` term `App` (snd' `App` termT))

prop_etaExpansionType :: (Eq v, Show v, Enum v) => v -> WellTyped v -> WellTyped v -> Property
prop_etaExpansionType v (WellTyped term) (WellTyped arg)
  = typeCheck [] term === typeCheck [] (App (Lam binding term) arg)
  where binding = (v, argTy)
        (Right argTy) = typeCheck [] arg
