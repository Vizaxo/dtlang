module Term where

import Types
import Utils

import Data.Functor.Foldable
import Data.List

-- | Get the maximum nesting level of a term.
maxNesting :: Term -> Int
maxNesting = cata alg
  where
    alg :: TermF Int -> Int
    alg (VarF v) = 0
    alg (CtorF c args) = maximum args + 1
    alg (LamF (_,b) t) = max b (t + 1)
    alg (PiF (_,b) t) = max b (t + 1)
    alg (AppF a b) = max a b + 1
    alg (TyF _) = 0
    alg (CaseF t branches) = max t (caseNesting branches)

    caseNesting :: [CaseTermF Int] -> Int
    caseNesting = maximumOr 0 . fmap (\(CaseTerm _ bs e) -> max (bindNesting bs) e)

    bindNesting :: [BindingF Int] -> Int
    bindNesting = maximumOr 0 . fmap snd

-- | Substitute all free occurances of the given variable for the
-- second argument, in the third argument.
subst :: Name -> Term -> Term -> Term
subst v replacement = oldNewCata alg
  where
    alg :: Term -> OldNew Term
    alg (Var u)
      -- Substitute the matching variable
      | v == u = Replace replacement
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
oldNewCata :: (Recursive t, Corecursive t) => (t -> OldNew t) -> t -> t
oldNewCata alg f = let f' = embed (oldNewCata alg <$> project f) in
  case alg f' of
    Old -> f
    New -> f'
    Replace x -> x

-- | Pretty-print a term.
prettyPrint :: Term -> String
prettyPrint = cata alg where
  alg (VarF v) = show v
  alg (CtorF c args) = "(" <> show c <> intercalate " " args <> ")"
  alg (LamF (u,uTy) body) = "\\" <> show u <> ":" <> uTy <> ". (" <> body <> ")"
  alg (PiF (u,uTy) ret) = show u <> ":" <> uTy <> " -> (" <> ret <> ")"
  alg (AppF a b) = "(" <> a <> ") (" <> b <> ")"
  alg (TyF n) = "(Type " <> show n <> ")"
  alg (CaseF t terms) = "(case " <> show t <> " of " <> show terms <> ")"

-- | Get a list of all the bound and free variables in a term.
allVars :: Term -> [Name]
allVars t = freeVars t <> boundVars t

-- | Get a list of all the free variables in a term.
freeVars :: Term -> [Name]
freeVars = cata alg where
  alg (VarF v) = [v]
  alg (CtorF c args) = nub $ concat args
  alg (LamF (v,ty) body) = nub (body <> ty) \\ [v]
  alg (PiF (v,a) ret) = nub (ret <> a) \\ [v]
  alg (AppF a b) = nub $ a <> b
  alg (TyF _) = []
  alg (CaseF t cs) = nub $ t <> concatMap caseTermFrees cs

  caseTermFrees (CaseTerm _ bs e) = nub (concatMap bindingFrees bs <> e) \\ (fst <$> bs)

  bindingFrees (v, t) = t \\ [v]

-- | Get a list of all the bound variables in a term.
boundVars :: Term -> [Name]
boundVars = cata alg where
  alg (VarF v) = []
  alg (CtorF c args) = concat args
  alg (LamF (v,_) body) = v:body
  alg (PiF (v,_) ret) = v:ret
  alg (AppF a b) = a <> b
  alg (TyF _) = []
  alg (CaseF t cs) = t <> concatMap caseTermBounds cs

  caseTermBounds (CaseTerm _ bs t) = concatMap bindingBounds bs <> t

  bindingBounds (v, t) = v:t
