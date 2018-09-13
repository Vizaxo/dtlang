module Test.TypeCheck where

import Test.Generators

import Equality
import Examples
import TC
import Term
import TypeCheck
import Types

import Control.Monad.Except
import Control.Monad.Trans.MultiState
import Data.Either
import Test.QuickCheck
import Test.Tasty.HUnit

-- | Make sure that the arbitrary instance for WellTyped generates well-typed terms.
prop_genWellTyped :: Context -> WellTyped -> Bool
prop_genWellTyped ctx (WellTyped term) = succeeded (mSet ctx >> typeCheck term)

prop_typeOfIsWellTyped :: Context -> WellTyped -> Bool
prop_typeOfIsWellTyped ctx (WellTyped term) = succeeded $ do
  mSet ctx
  ty <- typeCheck term
  ty' <- typeCheck ty
  whnf ty' >>= \case
    Ty n -> return ()
    _ -> throwError $ InternalError []

-- | Applying a term to id (specialised to the term's type) should have no
--   effect on the type.
prop_idPreservesType :: Context -> WellTyped -> Bool
prop_idPreservesType ctx (WellTyped term) = succeeded $ do
  termT <- mSet ctx >> typeCheck term
  resT <- mSet ctx >> typeCheck (id' `App` termT `App` term)
  return $ termT `betaEq` resT

-- | Applying a term twice to a pair then extracting the first element should
--   have no effect on the type.
prop_pairFstPreservesType :: Context -> WellTyped -> Bool
prop_pairFstPreservesType ctx (WellTyped term) =
  let (Right termT) = runTC $ mSet ctx >> typeCheck term
  in return termT `tcBetaEq`
     (mSet ctx >> typeCheck (pair `App` termT `App` term `App` term `App` (fst' `App` termT)))

-- | Applying a term twice to a pair then extracting the second element should
--   have no effect on the type.
prop_pairSndPreservesType :: Context -> WellTyped -> Bool
prop_pairSndPreservesType ctx (WellTyped term) =
  let (Right termT) = runTC $ mSet ctx >> typeCheck term
  in return termT `tcBetaEq`
     (mSet ctx >> typeCheck (pair `App` termT `App` term `App` term `App` (snd' `App` termT)))

-- | Eta-expanding a term should have no effect on the type.
prop_etaExpansionType :: Context -> WellTyped -> WellTyped -> Name -> Bool
prop_etaExpansionType ctx (WellTyped term) (WellTyped arg) v
  = (mSet ctx >> typeCheck term)
  `tcBetaEq` (mSet ctx >> typeCheck (App (Lam binding term) arg))
  where binding = (v, argTy)
        (Right argTy) = runTC $ typeCheck arg
