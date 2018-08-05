> module Equality where

> import Types
> import Term
> import TC
> import Utils

> import Control.Monad.Except
> import Data.Either

Two terms are syntactically equal if their structures and variable
names are exactly equal.

> syntaxEq :: Term -> Term -> TC ()
> syntaxEq a b | a == b = return ()
>              | otherwise = throwError $ TypeError [PS "Terms", PT a, PS "and", PT b, PS "are not syntactically equal."]

Two terms are alpha-equal if they have the same structure, and if for
each pair of variables that occur

(λx:A.x) =α (λy:A.y)

> prop_alphaEqId (Type ty) x y = Lam (x,ty) (Var x) `isAlphaEq` Lam (y,ty) (Var y)

(λx.λy.x) ≠α (λy.λy.y)

> alphaEq :: Term -> Term -> TC ()

If two terms are syntactially equal, they are alpha-euqal.

> a `alphaEq` b | (a `isSyntaxEq` b) = success

If two terms' sub-terms are alpha equal, and the top-level term
doesn't contain any variables, then the terms are alpha-equal.

> (App a b) `alphaEq` (App a' b') = do
>   alphaEq a a'
>   alphaEq b b'

Two lambda or pi expressions are alpha equal if
- their types are alpha equal, and
- upon substituting the free variables bound by the binder with a
  fresh variable, the resulting terms are alpha-equal

> (Lam (x,tyX) a) `alphaEq` (Lam (y,tyY) b) = do
>   tyX `alphaEq` tyY
>   z <- fresh
>   let a' = subst x (Var z) a
>   let b' = subst y (Var z) b
>   a' `alphaEq` b'
> (Pi (x,tyX) a) `alphaEq` (Pi (y,tyY) b) = do
>   tyX `alphaEq` tyY
>   z <- fresh
>   let a' = subst x (Var z) a
>   let b' = subst y (Var z) b
>   a' `alphaEq` b'

Two free variables are only alpha-equal if they are the same
variable. If the variables were bound, the rule for binders will make
them the same variable.

> (Var x) `alphaEq` (Var y) = unless (x == y) $
>   throwError $ TypeError [PS "The variables", PN x, PS "and", PN y, PS "are not equal."]

Ty is alpha-equal to Ty.

> Ty `alphaEq` Ty = success

The above rules outline all of the cases for alpha equality. Anything
else fails.

> a `alphaEq` b = throwError $ TypeError [PS "The terms", PT a, PS "and", PT b, PS "are not alpha-equal."]


Two terms 'a' and 'b' are beta-equal if there is a finite series of
beta-reductions and reverse-beta-reductions which returns 'b' starting
with 'a'.

> betaEq :: Term -> Term -> TC ()

If two terms are alpha-equal, then they are also beta-equal.

> betaEq a b | a `isAlphaEq` b = success

Evaluate both terms to whnf, then compare their heads with the betaEq'
helper function.

>            | otherwise = do
>   a' <- whnf a
>   b' <- whnf b
>   betaEq' a' b'

A helper function for comparing two terms which are in whnf.

>   where
>     betaEq' :: Term -> Term -> TC ()

If the whnf terms are alpha-equal, then the terms are also
beta-equal. This covers the cases for the non-recursive terms (Var and
Pi).

>     betaEq' a b | a `isAlphaEq` b = success

If the terms have the same head, recursively compare their
sub-structures.

>     (Lam (x,tyX) a) `betaEq'` (Lam (y,tyY) b) = do
>       tyX `betaEq` tyY
>       z <- fresh
>       let a' = subst x (Var z) a
>       let b' = subst y (Var z) b
>       a' `betaEq` b'
>     (Pi (x,tyX) a) `betaEq'` (Pi (y,tyY) b) = do
>       tyX `betaEq` tyY
>       z <- fresh
>       let a' = subst x (Var z) a
>       let b' = subst y (Var z) b
>       a' `betaEq'` b'

The terms have been evaluated to whnf, so there cannot be any App terms.
Any other pairs of terms are not beta-equal.

>     a `betaEq'` b = throwError $ TypeError
>       [PS "The terms", PT a, PS "and", PT b, PS "are not beta-equal."]



Evaluate a term to weak-head normal-form. This assumes that the given
term type-checks. The resulting term will have the same type as the
input term.

> whnf :: Term -> TC Term

An application term can be reduced by applying the function to the
argument.

> whnf (App a b) =
>   whnf a >>= \case
>     (Lam (x,tyX) body) -> whnf $ subst x b body
>     t -> throwError $ InternalError
>       [PS "Trying to apply the non-function type" ,PT t
>       ,PS "to the argument", PT b]

A non-application term is already in whnf.

> whnf t = return t

Helper functions for using these equalities in different contexts

> isSyntaxEq = succeeded .: syntaxEq
> isAlphaEq = succeeded .: alphaEq
> isBetaEq = succeeded .: betaEq
>
> tcBetaEq :: TC Term -> TC Term -> Bool
> tcBetaEq a b = succeeded $ do
>   a' <- a
>   b' <- b
>   a' `betaEq` b'

Run a TC computation, reporting if it succeded.

> succeeded :: TC a -> Bool
> succeeded = isRight . runTC