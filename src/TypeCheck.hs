module TypeCheck where

import Equality
import TC
import Term
import Types
import Utils

import Control.Monad.Except
import Control.Monad.Trans.MultiState
import Data.List

-- | Predicate of whether a given term is well-typed in the given context.
wellTyped :: Term -> Bool
wellTyped = succeeded . typeCheck

-- | Check the type of a term in the given context. Returns the type
-- if the term is well-typed, and gives an error otherwise.
typeCheck :: Term -> TC Term
typeCheck (Var v) = do
  gamma <- mGet
  case lookup v gamma of
    Nothing -> throwError $ TypeError [PS "Could not find", PN v, PS "in context."]
    Just ty -> return ty
typeCheck (Lam (x,xTy) body) = do
  typeCheck xTy >>= whnf >>= \case
    Ty -> Pi (x,xTy) <$> extendCtx (x,xTy) (typeCheck body)
    t  -> throwError $ TypeError [PS "Expected type", PT Ty, PS ", got type", PT t]
typeCheck (Pi (x,xTy) ret) = do
  typeCheck xTy >>= whnf >>= \case
    Ty -> do
      extendCtx (x,xTy) (typeCheck ret) >>= whnf >>= \case
        Ty -> return Ty
        t  -> throwError $ TypeError
          [PS "Expected type ", PT Ty, PS ", got type", PT t]
    t -> throwError $ TypeError [PS "Expected type ", PT Ty, PS ", got type ", PT t]
typeCheck (App a b) =
  typeCheck a >>= whnf >>= \case
    Pi (x,xTy) ret -> do
      bTy <- typeCheck b
      extendTypeError (betaEq bTy xTy) [PS "When type-checking", PT (App a b)]
      return (subst x b ret)
    _ -> throwError $ TypeError [PS "Trying to apply a non-function type."]
typeCheck Ty = return Ty
typeCheck (Let NoRec bindings body) = do
  --Type-check the bindings without any of the bindings in scope
  sequence $ typeCheckBinding <$> bindings
  mModify ((fst <$> bindings) ++)
  substLet bindings <$> typeCheck body
typeCheck (Let Rec bindings body) = do
  mModify ((fst <$> bindings) ++)
  --Type-check the bindings with the bindings recursively in scope
  sequence $ typeCheckBinding <$> bindings
  --Don't let body of a letrec be a type
  --TODO: Need to substitute bindings? What if non-terminating?
  --      Use context returned from TC monad too?
  notType body

-- | Type-check a data declaration. If successful, it adds the type
-- and constructors to the context.
typeCheckData :: DataDecl -> TC ()
typeCheckData (name, (Type ty), cs) = do
  nameUnique name
  ty `betaEq` Ty
  mModify ((name,ty):)
  bs <- mapM typeCheckC cs
  mapM (\b@(n,_) -> nameUnique n >> mModify (b:)) bs
  mModify (bs ++)
  where
    typeCheckC (c, (Type cTy)) = do
      cTy `hasType` (Type Ty)
      cTy' <- whnf cTy
      returnsData cTy'
      return (c, cTy)
      where
        --TODO: for now this only deals with datatypes with type Ty
        --Add supports for datatypes with Pi types
        returnsData = whnf >=> returnsData'
        returnsData' (Pi (_,_) ret) = returnsData ret
        returnsData' (Var retName)
          | retName == name = success
        returnsData' _ =
          throwError $ TypeError [PS "Constructor", PN c, PS "doesn't return the type", PN name]

-- | Check that a given name does not already occur in the context.
nameUnique :: Name -> TC ()
nameUnique n = do
  ctx <- mGet @Context
  case lookup n ctx of
    Nothing -> success
    Just _ -> throwError $ TypeError [PS "The name", PN n, PS "is already defined"]

-- | Check that a given term has the given type.
hasType :: Term -> Type -> TC ()
hasType t (Type tTy) = do
  ctx <- mGet
  tTy' <- typeCheck t
  extendTypeError (tTy `betaEq` tTy')
    [PS "while checking if", PT t, PS "has type", PT tTy
    ,PS "in the context", PC ctx]

-- | Helper function to substitute the bindings of a let expression into the body.
substLet :: [(Binding, Term)] -> Term -> Term
substLet xs body = foldr (\((v,_),val) term -> subst v val term) body xs

-- | Returns the term's type if the given term is not a type; throws
-- an error otherwise.
notType t =
  typeCheck t >>= \case
    Ty -> throwError $ TypeError
      [PS "Expected something not a type, got", PT t, PS ":", PT Ty]
    ty -> return ty

-- | Returns () if the given term is a type; throws an error otherwise.
isType t = do
  typeCheck t >>= \case
    Ty -> return ()
    term -> throwError $ TypeError
      [PS "Expected a type, got", PT t, PS ":", PT term]

-- | Helper function to type-check a single let binding.
typeCheckBinding ((x,xTy),val) = do
  ty <- typeCheck val
  isType xTy
  betaEq xTy ty

