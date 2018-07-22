module Test.Interpreter where

import Test.Generators

import Examples
import Interpreter
import TypeCheck
import Term

import Data.Either
import Test.QuickCheck

prop_wellTypedInterpretsRight :: (Eq v, Show v, Enum v) => WellTyped v -> Bool
prop_wellTypedInterpretsRight (WellTyped term) = isRight $ interpret term

prop_idReturnsArg :: (Eq v, Show v, Enum v) => WellTyped v -> Property
prop_idReturnsArg (WellTyped term) = (Right term) === interpret (appId term)

prop_etaExpansion :: (Eq v, Show v, Enum v) => v -> WellTyped v -> WellTyped v -> Property
prop_etaExpansion v (WellTyped term) (WellTyped arg)
  = interpretNF term === interpretNF (App (Lam binding term) arg)
  where binding = (v, argTy)
        (Right argTy) = typeCheck [] arg
