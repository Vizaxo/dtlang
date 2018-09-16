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
prop_genWellTyped ctx (WellTyped term) = succeeded ctx (typeCheck term)

prop_typeOfIsWellTyped :: Context -> WellTyped -> Bool
prop_typeOfIsWellTyped ctx (WellTyped term) = succeeded ctx $ do
  ty <- typeCheck term
  ty' <- typeCheck ty
  whnf ty' >>= \case
    Ty n -> return ()
    _ -> throwError $ InternalError []

-- | Applying a term to id (specialised to the term's type) should have no
--   effect on the type.
prop_idPreservesType :: Context -> WellTyped -> Bool
prop_idPreservesType ctx (WellTyped term) = succeeded ctx $ do
  termT <- typeCheck term
  resT <- typeCheck (id' `App` termT `App` term)
  return $ termT `betaEq` resT

-- | Applying a term twice to a pair then extracting the first element should
--   have no effect on the type.
prop_pairFstPreservesType :: Context -> WellTyped -> Bool
prop_pairFstPreservesType ctx (WellTyped term) = succeeded ctx $ do
  termTy <- typeCheck term
  resTy <- typeCheck (pair `App` termTy `App` term `App` term `App` (fst' `App` termTy))
  termTy `betaEq` resTy

-- | Applying a term twice to a pair then extracting the second element should
--   have no effect on the type.
prop_pairSndPreservesType :: Context -> WellTyped -> Bool
prop_pairSndPreservesType ctx (WellTyped term) = succeeded ctx $ do
  termTy <- typeCheck term
  resTy <- typeCheck (pair `App` termTy `App` term `App` term `App` (snd' `App` termTy))
  termTy `betaEq` resTy

-- | Eta-expanding a term should have no effect on the type.
prop_etaExpansionType :: Context -> WellTyped -> WellTyped -> Name -> Bool
prop_etaExpansionType ctx (WellTyped term) (WellTyped arg) v = succeeded ctx $ do
  termTy <- typeCheck term
  argTy <- typeCheck arg
  resTy <- typeCheck (App (Lam (v, argTy) term) arg)
  termTy `betaEq` resTy
