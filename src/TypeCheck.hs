module TypeCheck where

import Equality
import TC
import Term
import Types
import Utils

import Control.Monad.Except
import Control.Monad.State
import Data.List

-- | Predicate of whether a given term is well-typed in the given context.
wellTyped :: Context -> Term -> Bool
wellTyped = succeeded .: typeCheck

-- | Check the type of a term in the given context. Returns the type
-- if the term is well-typed, and gives an error otherwise.
typeCheck :: Context -> Term -> TC Term
typeCheck gamma (Var v) =
  case lookup v gamma of
    Nothing -> throwError $ TypeError [PS "Could not find", PN v, PS "in context."]
    Just ty -> return ty
typeCheck gamma (Lam (x,xTy) body) =
  typeCheck gamma xTy >>= \case
    Ty -> Pi (x,xTy) <$> typeCheck ((x,xTy):gamma) body
    t  -> throwError $ TypeError [PS "Expected type", PT Ty, PS ", got type", PT t]
typeCheck gamma (Pi (x,xTy) ret) =
  typeCheck gamma xTy >>= \case
    Ty -> do
       typeCheck ((x,xTy):gamma) ret >>= \case
         Ty -> return Ty
         t      -> throwError $ TypeError
           [PS "Expected type ", PT Ty, PS ", got type", PT t]
    t -> throwError $ TypeError [PS "Expected type ", PT Ty, PS ", got type ", PT t]
typeCheck gamma (App a b) =
  typeCheck gamma a >>= \case
    Pi (x,xTy) ret -> do
      bTy <- typeCheck gamma b
      betaEq bTy xTy
      return (subst x b ret)
    _ -> throwError $ TypeError [PS "Trying to apply a non-function type."]
typeCheck gamma Ty = return Ty
typeCheck gamma (Let NoRec bindings body) = do
  --Type-check the bindings without any of the bindings in scope
  sequence $ typeCheckBinding gamma <$> bindings
  let gamma' = (fst <$> bindings) ++ gamma
  let body' = substLet bindings body
  typeCheck gamma' body'
typeCheck gamma (Let Rec bindings body) = do
  let gamma' = (fst <$> bindings) ++ gamma
  --Type-check the bindings with the bindings recursively in scope
  sequence $ typeCheckBinding gamma' <$> bindings
  notType gamma' body >>= (\t -> isType gamma t >> return t)

-- | Helper function to substitute the bindings of a let expression into the body.
substLet :: [(Binding, Term)] -> Term -> Term
substLet xs body = foldr (\((v,_),val) term -> subst v val term) body xs

-- | Returns () if the given term is not a type; throws an error otherwise.
notType gamma t = do
  typeCheck gamma t >>= \case
    Ty -> throwError $ TypeError
      [PS "Expected something not a type, got", PT t, PS ":", PT Ty]
    term -> return term

-- | Returns () if the given term is a type; throws an error otherwise.
isType gamma t = do
  typeCheck gamma t >>= \case
    Ty -> return ()
    term -> throwError $ TypeError
      [PS "Expected a type, got", PT t, PS ":", PT term]

-- | Predicate of whether the given term is a type or not.
isType' :: Context -> Term -> Bool
isType' = succeeded .: isType

-- | Helper function to type-check a single let binding.
typeCheckBinding gamma ((x,xTy),val) = do
  ty <- typeCheck gamma val
  isType gamma xTy
  betaEq xTy ty

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
