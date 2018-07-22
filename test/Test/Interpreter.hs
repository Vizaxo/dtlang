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

prop_pairFstReturnsArg :: (Eq v, Show v, Enum v) => WellTyped v -> Property
prop_pairFstReturnsArg (WellTyped term) =
  wellTyped [] term ==> let (Right termT) = typeCheck [] term
                        in interpretNF term === interpretNF (pair `App` termT `App` term `App` term `App` (fst' `App` termT))

prop_pairSndReturnsArg :: (Eq v, Show v, Enum v) => WellTyped v -> Property
prop_pairSndReturnsArg (WellTyped term) =
  wellTyped [] term ==> let (Right termT) = typeCheck [] term
                        in interpretNF term === interpretNF (pair `App` termT `App` term `App` term `App` (snd' `App` termT))

prop_etaExpansion :: (Eq v, Show v, Enum v) => v -> WellTyped v -> WellTyped v -> Property
prop_etaExpansion v (WellTyped term) (WellTyped arg)
  = interpretNF term === interpretNF (App (Lam binding term) arg)
  where binding = (v, argTy)
        (Right argTy) = typeCheck [] arg
