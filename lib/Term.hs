module Term where

import Types
import Utils

import Data.Bifunctor
import Data.Functor.Foldable
import Data.List

-- | Get the maximum nesting level of a term.
maxNesting :: Term -> Int
maxNesting = cata alg
  where
    alg :: TermF Int -> Int
    alg (VarF v) = 0
    alg (LamF (_,b) t) = max b (t + 1)
    alg (PiF (_,b) t) = max b (t + 1)
    alg (AppF a b) = max a b
    alg (TyF _) = 0
    alg (CaseF t branches) = max t (caseNesting branches)

    caseNesting :: [CaseTermF Int] -> Int
    caseNesting = maximumOr 0 . fmap (\(CaseTerm _ bs e) -> max (bindNesting bs) e)

    bindNesting :: [BindingF Int] -> Int
    bindNesting = maximumOr 0 . fmap snd

-- | Substitute all free occurances of the given variable for the
-- second argument, in the third argument.
subst :: Name -> Term -> Term -> Term
subst v with = oldNewCata alg
  where
    alg :: Term -> OldNew Term
    alg (Var u)
      -- Substitute the matching variable
      | v == u = Replace with
    alg (Lam (u, _) _)
      -- Variable is shadowed: don't substitute under the binder
      | v == u = Old
    alg (Pi (u, _) _)
      -- Variable is shadowed: don't substitute under the binder
      | v == u = Old
    -- Else recursively substitute
    alg _ = New

-- | Used in the @oldNewCata@ recursion scheme.
data OldNew a = Old | New | Replace a

-- | Like a cata, but the OldNew value determines whether to use the
-- sub-term without the recursive call applied (@Old@), with the
-- recursive call applied (@New@), or replaced with a completely
-- separate term (@Replace x@).
oldNewCata :: Functor f => (Fix f -> OldNew (Fix f)) -> Fix f -> Fix f
oldNewCata alg f = let f' = Fix (oldNewCata alg <$> unfix f) in
  case alg f' of
    Old -> f
    New -> f'
    Replace x -> x

-- | Pretty-print a term.
prettyPrint :: Term -> String
prettyPrint (Var v) = show v
prettyPrint (Lam (u,uTy) body) = "\\" <> show u <> ":" <> prettyPrint uTy <> ". (" <> prettyPrint body <> ")"
prettyPrint (Pi (u,uTy) ret) = show u <> ":" <> prettyPrint uTy <> " -> (" <> prettyPrint ret <> ")"
prettyPrint (App a b) = "(" <> prettyPrint a <> ") (" <> prettyPrint b <> ")"
prettyPrint (Ty n) = "(Type " <> show n <> ")"

-- | Get a list of all the bound and free variables in a term.
allVars :: Term -> [Name]
allVars t = freeVars t ++ boundVars t

-- | Get a list of all the free variables in a term.
freeVars :: Term -> [Name]
freeVars (Var v) = [v]
freeVars (Ctor c args) = concat (freeVars <$> args)
freeVars (Lam (v,ty) body) = nub (freeVars body ++ freeVars ty) \\ [v]
freeVars (Pi (v,a) ret) = nub (freeVars ret ++ freeVars a) \\ [v]
freeVars (App a b) = nub $ freeVars a ++ freeVars b
freeVars (Ty _) = []

-- | Get a list of all the bound variables in a term.
boundVars :: Term -> [Name]
boundVars (Var v) = []
boundVars (Ctor c args) = concat (boundVars <$> args)
boundVars (Lam (v,_) body) = v:boundVars body
boundVars (Pi (v,_) ret) = v:boundVars ret
boundVars (App a b) = boundVars a ++ boundVars b
boundVars (Ty _) = []
