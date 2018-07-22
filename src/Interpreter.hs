module Interpreter where

import Term

-- | Interpret an expression.
--   If the expression is well-typed this should return a Right.
interpret :: (Eq v, Show v) => Term v -> Either String (Term v)
interpret (Var v) = Left $ "Variable " <> show v <> " not defined."
interpret lam@(Lam _ _) = return lam
interpret pi@(Pi _ _) = return pi
interpret (App a b) = do
  a' <- interpret a
  apply a' b
interpret term = return term

apply :: (Eq v, Show v) => Term v -> Term v -> Either String (Term v)
apply (Lam (x,_) body) arg = return $ subst x arg body
apply t _ = Left $ "Trying to apply the non-function term " <> show t
