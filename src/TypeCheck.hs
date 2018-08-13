module TypeCheck where

import Equality
import TC
import Term
import Types
import Utils

import Control.Monad.Except
import Control.Monad.Trans.MultiState
import Data.List
import Data.Ord
import Control.Lens hiding (Context)

-- | Predicate of whether a given term is well-typed in the given context.
wellTyped :: Term -> Bool
wellTyped = succeeded . typeCheck

-- | Check the type of a term in the given context. Returns the type
-- if the term is well-typed, and gives an error otherwise.
typeCheck :: Term -> TC Term
typeCheck (Var v) = fromCtx v
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
  mapM_ (mModify . uncurry insertCtx) (fst <$> bindings)
  substLet bindings <$> typeCheck body
typeCheck (Let Rec bindings body) = do
  mapM_ (mModify . uncurry insertCtx) (fst <$> bindings)
  --Type-check the bindings with the bindings recursively in scope
  sequence $ typeCheckBinding <$> bindings
  --Don't let body of a letrec be a type
  --TODO: Need to substitute bindings? What if non-terminating?
  --      Use context returned from TC monad too?
  notType body
typeCheck (Case e xs) = do
  t <- typeCheck e
  dataname <- dataTypeReturn t
  datatype <- lookupData dataname
  --TODO: use sets instead of lists
  let datactors = over _2 unType <$> (sortBy (comparing fst) $ constructors datatype)
  let casectors = sortBy (comparing constructor) $ xs
  caseTys <- zipWithM (tcCase datatype) datactors casectors
  --TODO: empty cases
  adjacentsSatisfyM betaEq caseTys
  --TODO: check if contexts are properly propogated
  whnf $ head caseTys

  where
    tcCase datatype (ctora, ty) (CaseTerm ctorb bindings expr)
      | ctora /= ctorb = throwError $ TypeError [PS "Constructors for datatype", PD datatype, PS "not matched by case expression", PT (Case e xs)]
      | otherwise = do
          ty' <- whnf ty
          bindings' <- mapM (\(n,ty) -> (n,) <$> whnf ty) bindings
          expr' <- whnf expr
          tcCase' ty' bindings expr'
    tcCase' (Pi (x, xTy) ret) ((y,yTy):bs) expr = do
      --TODO: better type errors
      xTy `betaEq` yTy
      extendCtx (y,yTy) $ tcCase' ret bs expr
    tcCase' ty [] expr = do
      hasType expr (Type ty)
      return ty
    tcCase' _ _ _ = throwError $ TypeError [PS "Couldn't match case term with constructor type"]


-- | Type-check a data declaration. If successful, it adds the type
-- and constructors to the context.
typeCheckData :: DataDecl -> TC ()
typeCheckData d@(DataDecl name (Type ty) cs) = do
  --TODO: propogating the context like state is just wrong? go back to reader?
  nameUnique name
  isolateCtx $ ty `hasType` Type Ty
  mModify (insertCtx name ty)
  bs <- mapM typeCheckC cs
  mapM_ (\(n,t) -> nameUnique n >> mModify (insertCtx n t)) bs
  mModify $ insertDataDecl d

  where
    typeCheckC (c, (Type cTy)) = do
      cTy `hasType` (Type Ty)
      cTy' <- whnf cTy
      returnsData name cTy'
      return (c, cTy)

dataTypeReturn = whnf >=> returnTy >=> whnf >=> appData

returnsData name = dataTypeReturn >=> \n -> case (n == name) of
  True -> success
  False -> throwError $ TypeError [PS "Expected type constructor", PN name, PS ", got type constructor" , PN n]

returnTy (Pi (_,_) ret) = whnf ret >>= returnTy
returnTy t = return t

appData (App a b) = whnf a >>= appData
appData (Var retName) = return retName
appData _ = throwError $ TypeError [PS "AppData not applied to a type constructed from a type constructor"]

-- | Check that a given name does not already occur in the context.
nameUnique :: Name -> TC ()
nameUnique n = do
  ctx <- mGet @Context
  case lookupCtx n ctx of
    Nothing -> success
    Just _ -> throwError $ TypeError [PS "The name", PN n, PS "is already defined"]

-- | Check that a given term has the given type.
hasType :: Term -> Type -> TC ()
hasType t (Type target) = do
  ctx <- mGet
  tTy <- typeCheck t
  extendTypeError (target `betaEq` tTy)
    [PS "while checking if", PT t, PS "has type", PT tTy
    ,PS "in the context", PC ctx]

fromCtx v = do
  ctx <- mGet
  case lookupCtx v ctx of
    Nothing -> throwError $ TypeError [PS "Could not find", PN v, PS "in context."]
    Just ty -> return ty

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

