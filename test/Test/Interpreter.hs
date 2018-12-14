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
prop_wellTypedWhnfSucceeds (WellTyped term) = succeeded emptyCtx $ whnf term --TODO: Use context

-- | Applying a term to id (specialised to the term's type) should have no
--   effect on the value.
prop_idReturnsArg :: WellTyped -> Bool
prop_idReturnsArg (WellTyped term) = isRight $ defaultCtx >>= flip runTC (do
  ty <- typeCheck term
  term `betaEq` (id' `App` ty `App` term))

-- | Applying a term twice to a pair then extracting the first element should
--   have no effect on the value.
prop_pairFstReturnsArg :: WellTyped -> Bool
prop_pairFstReturnsArg (WellTyped term) = isRight $ defaultCtx >>= flip runTC (do
  ty <- typeCheck term
  term `betaEq` (pair `App` ty `App` term `App` term `App` (fst' `App` ty)))

-- | Applying a term twice to a pair then extracting the second element should
--   have no effect on the value.
prop_pairSndReturnsArg :: WellTyped -> Bool
prop_pairSndReturnsArg (WellTyped term) = isRight $ defaultCtx >>= flip runTC (do
  ty <- typeCheck term
  term `betaEq` (pair `App` ty `App` term `App` term `App` (snd' `App` ty)))

-- | Eta-expanding a term should have no effect on the value.
prop_etaExpansion :: WellTyped -> WellTyped -> Name -> Bool
prop_etaExpansion (WellTyped term) (WellTyped arg) v = isRight $ defaultCtx >>= flip runTC (do
  ty <- typeCheck arg
  betaEq term (App (Lam (v, ty) term) arg))
