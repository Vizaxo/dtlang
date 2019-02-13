> module Equality where

> import Types
> import Term
> import TC
> import Utils

> import Control.Monad.Except
> import Control.Monad.Reader
> import Data.Either
> import qualified Data.Map as M
> import Test.QuickCheck

Two terms are syntactically equal if their structures and variable
names are exactly equal.

> syntaxEq :: Term -> Term -> TC ()
> syntaxEq a b | a == b = return ()
>              | otherwise = throwError $ TypeError [PS "Terms", PT a, PS "and", PT b, PS "are not syntactically equal."]

Alpha equality of terms.

> alphaEq :: Term -> Term -> TC ()

If two terms are syntactially equal, they are alpha-euqal.

> a `alphaEq` b | a == b = success

If two terms' sub-terms are alpha equal, and the top-level term
doesn't contain any variables, then the terms are alpha-equal.

> (App a b) `alphaEq` (App a' b') = do
>   alphaEq a a'
>   alphaEq b b'

Two lambda or pi expressions are alpha equal if
- their types are alpha equal, and
- upon substituting the free variables bound by the binder with a
  fresh variable, the resulting terms are alpha-equal

> lamA@(Lam (x,tyX) a) `alphaEq` lamB@(Lam (y,tyY) b) = do
>   tyX `alphaEq` tyY
>   local (insertCtx x tyX . insertCtx y tyY) $ do
>     z <- fresh (allVars lamA ++ allVars lamB)
>     let a' = subst x (Var z) a
>     let b' = subst y (Var z) b
>     a' `alphaEq` b'
> piA@(Pi (x,tyX) a) `alphaEq` piB@(Pi (y,tyY) b) = do
>   tyX `alphaEq` tyY
>   local (insertCtx x tyX . insertCtx y tyY) $ do
>     z <- fresh (allVars piA ++ allVars piB)
>     let a' = subst x (Var z) a
>     let b' = subst y (Var z) b
>     a' `alphaEq` b'

Two free variables are only alpha-equal if they are the same
variable. If the variables were bound, the rule for binders will make
them the same variable.

> (Var x) `alphaEq` (Var y) = unless (x == y) $
>   throwError $ TypeError [PS "The variables", PN x, PS "and", PN y, PS "are not equal."]

> (Ctor c xs) `alphaEq` (Ctor d ys)
>   | c == d = zipWithM_ alphaEq xs ys
>   | otherwise = throwError $ TypeError [PS "The constructors", PN c, PS "and", PN d, PS "are not the same."]

Ty is alpha-equal to Ty.

> (Ty n) `alphaEq` (Ty m) | n == m = success
>                         | otherwise = throwError $ TypeError [PS "Type universes", PT (Ty n), PS "and", PT (Ty m), PS "are not alpha-equal."]

The above rules outline all of the cases for alpha equality. Anything
else fails.

> a `alphaEq` b = throwError $ TypeError [PS "The terms", PT a, PS "and", PT b, PS "are not alpha-equal."]


Two terms 'a' and 'b' are beta-equal if there is a finite series of
beta-reductions and reverse-beta-reductions which returns 'b' starting
with 'a'.

> betaEq :: Term -> Term -> TC ()

If two terms are alpha-equal, then they are also beta-equal.

> betaEq a b | eq = success

Evaluate both terms to whnf, then compare their heads with the betaEq'
helper function.

>            | otherwise = do
>                a' <- whnf a
>                b' <- whnf b
>                betaEq' a' b'
>   where eq = isAlphaEq emptyCtx a b --TODO: should this have the full context?

A helper function for comparing two terms which are in whnf.

> betaEq' :: Term -> Term -> TC ()

If the whnf terms are alpha-equal, then the terms are also
beta-equal. This covers the cases for the non-recursive terms (Var and
Pi).

> betaEq' a b | eq = success
>   where eq = isAlphaEq emptyCtx a b --TODO: should this have the full context?

If the terms have the same head, recursively compare their
sub-structures.

> lamA@(Lam (x,tyX) a) `betaEq'` lamB@(Lam (y,tyY) b) = do
>   tyX `betaEq` tyY
>   local (insertCtx x tyX . insertCtx y tyY) $ do
>     z <- fresh (allVars lamA ++ allVars lamB)
>     ctx <- ask
>     let a' = subst x (Var z) a
>     let b' = subst y (Var z) b
>     a' `betaEq` b'
> piA@(Pi (x,tyX) a) `betaEq'` piB@(Pi (y,tyY) b) = do
>   tyX `betaEq` tyY
>   local (insertCtx x tyX . insertCtx y tyY) $ do
>     z <- fresh (allVars piA ++ allVars piB)
>     let a' = subst x (Var z) a
>     let b' = subst y (Var z) b
>     a' `betaEq` b'

The terms have been evaluated to whnf, so there cannot be any App terms.
Any other pairs of terms are not beta-equal.

> a `betaEq'` b = throwError $ TypeError
>   [PS "The terms", PT a, PS "and", PT b, PS "are not beta-equal."]

> --isBetaEq' = succeeded .: betaEq'

(λx:A.x) = (λy:A.y)

> prop_eqIdAlpha ty x y = isAlphaEq emptyCtx (Lam (x,ty) (Var x)) (Lam (y,ty) (Var y))
> prop_eqIdBeta ty x y = isBetaEq emptyCtx (Lam (x,ty) (Var x)) (Lam (y,ty) (Var y))

The fst function (specialised to a generated type) should not be equal
to the snd function.

> prop_fstNotSndAlpha t a b =
>   a /= b ==> not $ isAlphaEq emptyCtx
>                      (Lam (a, t) (Lam (b, t) (Var a)))
>                      (Lam (a, t) (Lam (b, t) (Var b)))
> prop_fstNotSndBeta t a b =
>   a /= b ==> not $ isBetaEq emptyCtx
>                      (Lam (a, t) (Lam (b, t) (Var a)))
>                      (Lam (a, t) (Lam (b, t) (Var b)))

The type of the fst functinon should not be equal to the type of the
snd function.

> prop_fstNotSndTyAlpha t a b =
>   a /= b ==> not $ isAlphaEq emptyCtx
>                      (Pi (a, t) (Pi (b, t) (Var a)))
>                      (Pi (a, t) (Pi (b, t) (Var b)))
> prop_fstNotSndTyBeta t a b =
>   a /= b ==> not $ isBetaEq emptyCtx
>                      (Pi (a, t) (Pi (b, t) (Var a)))
>                      (Pi (a, t) (Pi (b, t) (Var b)))

Evaluate a term to weak-head normal-form. This assumes that the given
term type-checks. The resulting term will have the same type as the
input term.

> whnf :: (MonadError TypeError m, MonadReader Context m) => Term -> m Term

An application term can be reduced by applying the function to the
argument.

> whnf (App a b) =
>   whnf a >>= \case

An application of a lambda is beta reduction.

>     (Lam (x,tyX) body) -> whnf $ subst x b body

Otherwise, it can't be reduced.

>     t -> return (App t b)

A case expression with a known scrutinee can be reduced by picking the
appropriate branch.

> whnf (Case e m terms) = do
>   m' <- whnf m
>   whnf e >>= \case
>     Ctor c args -> do
>       case M.lookup c terms of
>         Nothing -> throwError $ TypeError [PS "Non-exhastive patterns in", PT (Case e m' terms)]
>         Just (CaseTerm bs body) -> whnf $ substBindings (zip bs args) body
>     t -> return (Case t m' terms)

A constructor can be eta-expanded, resulting in a lambda surrounding a
fully applied 'Ctor'.

If the variable is not a constructor, it cannot be reduced.

> whnf (Var v) = partiallyApplyCtor v

Any other term is already in whnf.

> whnf t = return t

Substitute a list of bindings into an expression.

> substBindings :: [(Name, Term)] -> Term -> Term
> substBindings xs body = foldr (\(v,val) term -> subst v val term) body xs

Convert a type to whnf.

> whnfTy :: Type -> TC Term
> whnfTy t = whnf t

Eta-expand a constructor, so that constructors are always fully applied.
The type is assumed to be in whnf.

> partiallyApplyCtor :: MonadReader Context m => Name -> m Term
> partiallyApplyCtor v = do
>   lookupEnv v <$> ask >>= \case
>     Just t -> pure $ Var v
>     Nothing ->
>       fromRight (Var v) <$> runExceptT (partiallyApplyCtor' [] <$> lookupCtor v)
>   where
>     partiallyApplyCtor' args (Pi (x,ty) ret)
>       = Lam (x,ty) (partiallyApplyCtor' (Var x:args) ret)
>     partiallyApplyCtor' args _
>       = Ctor v args

Helper functions for using these equalities in different contexts

> isAlphaEq ctx = succeeded ctx .: alphaEq
> isBetaEq ctx = succeeded ctx .: betaEq
>
> tcBetaEq :: Context -> TC Term -> TC Term -> Bool
> tcBetaEq ctx a b = succeeded ctx $ do
>   a' <- a
>   b' <- b
>   a' `betaEq` b'

Run a TC computation, reporting if it succeded.

> succeeded :: Context -> TC a -> Bool
> succeeded = isRight .: runTC
