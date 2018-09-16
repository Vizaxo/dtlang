module Term where

import Types
import Utils

import Data.Bifunctor
import Data.List

-- | Get the maximum nesting level of a term.
maxNesting :: Term -> Int
maxNesting (Var v) = 0
maxNesting (Lam _ t) = maxNesting t + 1
maxNesting (Pi _ t) = maxNesting t + 1
maxNesting (App a b) = max (maxNesting a) (maxNesting b)
maxNesting (Ty _) = 0
maxNesting (Case t branches) = max (maxNesting t) caseNesting
  where caseNesting = maximumOr 0 $ fmap (maxNesting . \(CaseTerm _ _ x)->x) branches

-- | Substitute all free occurances of the given variable for the
--   second argument, in the third argument.
subst :: Name -> Term -> Term -> Term
subst v with (Var u) | v == u    = with
                     | otherwise = Var u
subst v with (Ctor c args) = Ctor c (subst v with <$> args)
subst v with lam@(Lam (u,uTy) body)
  | v == u    = lam --Variable is shadowed
  | otherwise = Lam (u,(subst v with uTy)) (subst v with body)
subst v with pi@(Pi (u,uTy) ret)
  | v == u    = pi --Variable is shadowed
  | otherwise = Pi (u,(subst v with uTy)) (subst v with ret)
subst v with (App a b) = App (subst v with a) (subst v with b)
subst v with (Ty n) = Ty n
subst v with (Case e terms) = Case (subst v with e) (substCaseTerm v with <$> terms)

substCaseTerm :: Name -> Term -> CaseTerm -> CaseTerm
substCaseTerm v with (CaseTerm c bs body)
  = CaseTerm c (substBinding v with <$> bs) (subst v with body)

substBinding :: Name -> Term -> (Name, Term) -> (Name, Term)
substBinding v with (n, ty) | v == n = (n, ty)
                            | otherwise = (n, subst v with ty)

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
