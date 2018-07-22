module Test.TypeCheck where

import Test.Generators

import Examples
import TypeCheck
import Term

import Data.Either
import Test.QuickCheck

-- | Make sure that the arbitrary instance for WellTyped generates well-typed terms.
prop_genWellTyped :: (Eq v, Show v, Enum v) => WellTyped v -> Bool
prop_genWellTyped (WellTyped term) = wellTyped [] term

-- | Applying a term to id (specialised to the term's type) should have no
--   effect on the type.
prop_idPreservesType :: (Eq v, Show v, Enum v) => WellTyped v -> Property
prop_idPreservesType (WellTyped term) =
  wellTyped [] term ==> let termT = typeCheck [] term
                        in termT === typeCheck [] (appId term)

-- | Applying a term twice to a pair then extracting the first element should
--   have no effect on the type.
prop_pairFstPreservesType :: (Eq v, Show v, Enum v) => WellTyped v -> Property
prop_pairFstPreservesType (WellTyped term) =
  wellTyped [] term ==> let (Right termT) = typeCheck [] term
                        in Right termT === typeCheck [] (pair `App` termT `App` term `App` term `App` (fst' `App` termT))

-- | Applying a term twice to a pair then extracting the second element should
--   have no effect on the type.
prop_pairSndPreservesType :: (Eq v, Show v, Enum v) => WellTyped v -> Property
prop_pairSndPreservesType (WellTyped term) =
  wellTyped [] term ==> let (Right termT) = typeCheck [] term
                        in Right termT === typeCheck [] (pair `App` termT `App` term `App` term `App` (snd' `App` termT))

-- | Eta-expanding a term should have no effect on the type.
prop_etaExpansionType :: (Eq v, Show v, Enum v) => v -> WellTyped v -> WellTyped v -> Property
prop_etaExpansionType v (WellTyped term) (WellTyped arg)
  = typeCheck [] term === typeCheck [] (App (Lam binding term) arg)
  where binding = (v, argTy)
        (Right argTy) = typeCheck [] arg
