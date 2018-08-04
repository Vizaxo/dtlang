module Test.TypeCheck where

import Test.Generators

import Equality
import Examples
import TC
import Term
import TypeCheck
import Types

import Data.Either
import Test.QuickCheck

-- | Make sure that the arbitrary instance for WellTyped generates well-typed terms.
prop_genWellTyped :: WellTyped -> Bool
prop_genWellTyped (WellTyped term) = wellTyped [] term

-- | Applying a term to id (specialised to the term's type) should have no
--   effect on the type.
prop_idPreservesType :: WellTyped -> Property
prop_idPreservesType (WellTyped term) =
  wellTyped [] term ==> let termT = typeCheck [] term
                        in termT `tcBetaEq` typeCheck [] (appId term)

-- | Applying a term twice to a pair then extracting the first element should
--   have no effect on the type.
prop_pairFstPreservesType :: WellTyped -> Property
prop_pairFstPreservesType (WellTyped term) =
  wellTyped [] term ==> let (Right termT) = runTC $ typeCheck [] term
                        in return termT `tcBetaEq` typeCheck [] (pair `App` termT `App` term `App` term `App` (fst' `App` termT))

-- | Applying a term twice to a pair then extracting the second element should
--   have no effect on the type.
prop_pairSndPreservesType :: WellTyped -> Property
prop_pairSndPreservesType (WellTyped term) =
  wellTyped [] term ==> let (Right termT) = runTC $ typeCheck [] term
                        in return termT `tcBetaEq` typeCheck [] (pair `App` termT `App` term `App` term `App` (snd' `App` termT))

-- | Eta-expanding a term should have no effect on the type.
prop_etaExpansionType :: WellTyped -> WellTyped -> Name -> Bool
prop_etaExpansionType (WellTyped term) (WellTyped arg) v
  = typeCheck [] term `tcBetaEq` typeCheck [] (App (Lam binding term) arg)
  where binding = (v, argTy)
        (Right argTy) = runTC $ typeCheck [] arg
