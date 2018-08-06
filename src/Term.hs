module Term where

import Types
import Utils

import Data.List

-- | Get the maximum nesting level of a term.
maxNesting :: Term -> Int
maxNesting (Var v) = 0
maxNesting (Lam _ t) = maxNesting t + 1
maxNesting (Pi _ t) = maxNesting t + 1
maxNesting (App a b) = max (maxNesting a) (maxNesting b)
maxNesting Ty = 0
maxNesting (Let _ bindings body) = max (maxNesting body) bindNesting
  where bindNesting = maximumOr 0 $ fmap (maxNesting . snd) bindings
  --Let calculation is wrong: each binding could be nested deeply. But
  --recursive let bindings can't be inlined, so this is good enough without
  --being over-complicated.
maxNesting (Case t branches) = max (maxNesting t) caseNesting
  where caseNesting = maximumOr 0 $ fmap (maxNesting . \(_,_,(Type x))->x) branches

-- | Substitute all free occurances of the given variable for the
--   second argument, in the third argument.
subst :: Name -> Term -> Term -> Term
subst v with (Var u) | v == u    = with
                     | otherwise = Var u
subst v with lam@(Lam (u,uTy) body)
  | v == u    = lam --Variable is shadowed
  | otherwise = Lam (u,(subst v with uTy)) (subst v with body)
subst v with pi@(Pi (u,uTy) ret)
  | v == u    = pi --Variable is shadowed
  | otherwise = Pi (u,(subst v with uTy)) (subst v with ret)
subst v with (App a b) = App (subst v with a) (subst v with b)
subst v with Ty = Ty
subst v with lett@(Let rec bindings body)
  | elem v (fst <$> fst <$> bindings) = lett --Variable is shadowed
  | otherwise = Let rec (substBindings <$> bindings) (subst v with body)
  where substBindings = \((u,uTy),val) -> ((u,subst v with uTy), subst v with val)

-- | Pretty-print a term.
prettyPrint :: Term -> String
prettyPrint (Var v) = show v
prettyPrint (Lam (u,uTy) body) = "\\" <> show u <> ":" <> prettyPrint uTy <> ". (" <> prettyPrint body <> ")"
prettyPrint (Pi (u,uTy) ret) = show u <> ":" <> prettyPrint uTy <> " -> (" <> prettyPrint ret <> ")"
prettyPrint (App a b) = "(" <> prettyPrint a <> ") (" <> prettyPrint b <> ")"
prettyPrint Ty = "Type"
prettyPrint (Let rec bindings body) = pplet rec <> ppbindings <> "in (" <> prettyPrint body <> ")"
  where pplet Rec = "letrec"
        pplet NoRec = "let"
        ppbindings = " bindings "

-- | Get a list of all the bound and free variables in a term.
allVars :: Term -> [Name]
allVars t = freeVars t ++ boundVars t

-- | Get a list of all the free variables in a term.
freeVars :: Term -> [Name]
freeVars (Var v) = [v]
freeVars (Lam (v,ty) body) = (freeVars body ++ freeVars ty) \\ [v]
freeVars (Pi (v,a) ret) = (freeVars ret ++ freeVars a) \\ [v]
freeVars (App a b) = freeVars a ++ freeVars b
freeVars Ty = []
freeVars (Let _ xs body) = freeVars body \\ fmap (fst . fst) xs
  --TODO: free vars in let bindings

-- | Get a list of all the bound variables in a term.
boundVars :: Term -> [Name]
boundVars (Var v) = []
boundVars (Lam (v,_) body) = v:boundVars body
boundVars (Pi (v,_) ret) = v:boundVars ret
boundVars (App a b) = boundVars a ++ boundVars b
boundVars Ty = []
boundVars (Let _ xs body) = fmap (fst . fst) xs ++ boundVars body
