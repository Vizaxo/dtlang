module Test.Interpreter where

import Test.Generators

import Equality
import Examples
import TC
import Term
import TypeCheck
import Types

import Data.Either
import Test.QuickCheck

-- | Any well-typed term should not give an error when interpreted to normal
--   form.
prop_wellTypedWhnfSucceeds :: WellTyped -> Bool
prop_wellTypedWhnfSucceeds (WellTyped term) = succeeded $ whnf term

-- | Applying a term to id (specialised to the term's type) should have no
--   effect on the value.
prop_idReturnsArg :: WellTyped -> Bool
prop_idReturnsArg (WellTyped term) = term `isBetaEq` (appId term)

-- | Applying a term twice to a pair then extracting the first element should
--   have no effect on the value.
prop_pairFstReturnsArg :: WellTyped -> Bool
prop_pairFstReturnsArg (WellTyped term) =
  let (Right termT) = runTC $ typeCheck [] term
  in term `isBetaEq` (pair `App` termT `App` term `App` term `App` (fst' `App` termT))

-- | Applying a term twice to a pair then extracting the second element should
--   have no effect on the value.
prop_pairSndReturnsArg :: WellTyped -> Bool
prop_pairSndReturnsArg (WellTyped term) =
  let (Right termT) = runTC $ typeCheck [] term
  in term `isBetaEq` (pair `App` termT `App` term `App` term `App` (snd' `App` termT))

-- | Eta-expanding a term should have no effect on the value.
prop_etaExpansion :: Name -> WellTyped -> WellTyped -> Bool
prop_etaExpansion v (WellTyped term) (WellTyped arg)
  = term `isBetaEq` (App (Lam binding term) arg)
  where binding = (v, argTy)
        (Right argTy) = runTC $ typeCheck [] arg
