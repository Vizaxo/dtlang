module Equality where

import Types
import Term
import TC
import Utils

import Control.Monad.Except
import Control.Monad.Reader
import Data.Either
import qualified Data.Map as M
import Test.QuickCheck

-- Two terms are syntactically equal if their structures and variable
-- names are exactly equal.

syntaxEq :: Term -> Term -> TC ()
syntaxEq a b | a == b = return ()
             | otherwise = throwError (TENotSyntaxEq a b)

-- Alpha equality of terms.
alphaEq :: Term -> Term -> TC ()
a `alphaEq` b | a == b = success
(App a b) `alphaEq` (App a' b') = do
  alphaEq a a'
  alphaEq b b'
lamA@(Lam (x,tyX) a) `alphaEq` lamB@(Lam (y,tyY) b) = do
  tyX `alphaEq` tyY
  local (insertCtx x tyX . insertCtx y tyY) $ do
    z <- fresh (allVars lamA ++ allVars lamB)
    let a' = subst x (Var z) a
    let b' = subst y (Var z) b
    a' `alphaEq` b'
piA@(Pi (x,tyX) a) `alphaEq` piB@(Pi (y,tyY) b) = do
  tyX `alphaEq` tyY
  local (insertCtx x tyX . insertCtx y tyY) $ do
    z <- fresh (allVars piA ++ allVars piB)
    let a' = subst x (Var z) a
    let b' = subst y (Var z) b
    a' `alphaEq` b'
(Var x) `alphaEq` (Var y) = unless (x == y) $
  throwError (TEAlphaVarsNotEq x y)
(Ctor c xs) `alphaEq` (Ctor d ys)
  | c == d = zipWithM_ alphaEq xs ys
  | otherwise = throwError (TEAlphaCtorsNotEq c d)
(Ty n) `alphaEq` (Ty m) | n == m = success
                        | otherwise = throwError (TEAlphaTypeUniversesNotEq n m)
a `alphaEq` b = throwError (TEAlphaNotAlphaEq a b)


-- Two terms 'a' and 'b' are beta-equal if there is a finite series of
-- beta-reductions and reverse-beta-reductions which returns 'b' starting
-- with 'a'.
betaEq :: Term -> Term -> TC ()
betaEq a b | eq = success
           | otherwise = do
               a' <- whnf a
               b' <- whnf b
               betaEq' a' b'
  where eq = isAlphaEq emptyCtx a b --TODO: should this have the full context?

-- A helper function for comparing two terms which are in whnf.
betaEq' :: Term -> Term -> TC ()
betaEq' a b | eq = success
  where eq = isAlphaEq emptyCtx a b --TODO: should this have the full context?
lamA@(Lam (x,tyX) a) `betaEq'` lamB@(Lam (y,tyY) b) = do
  tyX `betaEq` tyY
  local (insertCtx x tyX . insertCtx y tyY) $ do
    z <- fresh (allVars lamA ++ allVars lamB)
    ctx <- ask
    let a' = subst x (Var z) a
    let b' = subst y (Var z) b
    a' `betaEq` b'
piA@(Pi (x,tyX) a) `betaEq'` piB@(Pi (y,tyY) b) = do
  tyX `betaEq` tyY
  local (insertCtx x tyX . insertCtx y tyY) $ do
    z <- fresh (allVars piA ++ allVars piB)
    let a' = subst x (Var z) a
    let b' = subst y (Var z) b
    a' `betaEq` b'
a `betaEq'` b = throwError (TENotBetaEq a b)

-- (λx:A.x) = (λy:A.y)
prop_eqIdAlpha ty x y = isAlphaEq emptyCtx (Lam (x,ty) (Var x)) (Lam (y,ty) (Var y))
prop_eqIdBeta ty x y = isBetaEq emptyCtx (Lam (x,ty) (Var x)) (Lam (y,ty) (Var y))

-- The fst function (specialised to a generated type) should not be equal
-- to the snd function.
prop_fstNotSndAlpha t a b =
  a /= b ==> not $ isAlphaEq emptyCtx
                     (Lam (a, t) (Lam (b, t) (Var a)))
                     (Lam (a, t) (Lam (b, t) (Var b)))
prop_fstNotSndBeta t a b =
  a /= b ==> not $ isBetaEq emptyCtx
                     (Lam (a, t) (Lam (b, t) (Var a)))
                     (Lam (a, t) (Lam (b, t) (Var b)))

-- The type of the fst functinon should not be equal to the type of the
-- snd function.
prop_fstNotSndTyAlpha t a b =
  a /= b ==> not $ isAlphaEq emptyCtx
                     (Pi (a, t) (Pi (b, t) (Var a)))
                     (Pi (a, t) (Pi (b, t) (Var b)))
prop_fstNotSndTyBeta t a b =
  a /= b ==> not $ isBetaEq emptyCtx
                     (Pi (a, t) (Pi (b, t) (Var a)))
                     (Pi (a, t) (Pi (b, t) (Var b)))

-- Evaluate a term to weak-head normal-form. This assumes that the given
-- term type-checks. The resulting term will have the same type as the
-- input term.
whnf :: (MonadError TypeError m, MonadReader Context m) => Term -> m Term
whnf (App a b) =
  whnf a >>= \case
    (Lam (x,tyX) body) -> whnf $ subst x b body
    t -> return (App t b)
whnf t@(Case e m terms) = do
  m' <- whnf m
  whnf e >>= \case
    Ctor c args -> do
      case M.lookup c terms of
        Nothing -> throwError (TEWhnfUnmatchedCase c t)
        Just (CaseTerm bs body) -> whnf $ substBindings (zip bs args) body
    t -> return (Case t m' terms)
whnf (Var v) = partiallyApplyCtor v
whnf (TFix t) = whnf (App t (TFix t))
whnf t = return t

-- Substitute a list of bindings into an expression.
substBindings :: [(Name, Term)] -> Term -> Term
substBindings xs body = foldr (\(v,val) term -> subst v val term) body xs

-- Eta-expand a constructor, so that constructors are always fully applied.
-- The type is assumed to be in whnf.
partiallyApplyCtor :: MonadReader Context m => Name -> m Term
partiallyApplyCtor v = do
  lookupEnv v <$> ask >>= \case
    Just t -> pure t
    Nothing ->
      fromRight (Var v) <$> runExceptT (partiallyApplyCtor' [] <$> lookupCtor v)
  where
    partiallyApplyCtor' args (Pi (x,ty) ret)
      = Lam (x,ty) (partiallyApplyCtor' (Var x:args) ret)
    partiallyApplyCtor' args _
      = Ctor v args

-- Helper functions for using these equalities in different contexts
isAlphaEq ctx = succeeded ctx .: alphaEq
isBetaEq ctx = succeeded ctx .: betaEq

tcBetaEq :: Context -> TC Term -> TC Term -> Bool
tcBetaEq ctx a b = succeeded ctx $ do
  a' <- a
  b' <- b
  a' `betaEq` b'

-- Run a TC computation, reporting if it succeded.
succeeded :: Context -> TC a -> Bool
succeeded = isRight .: runTC
