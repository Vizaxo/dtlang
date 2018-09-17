module TypeCheck where

import Equality
import TC
import Term
import Types
import Utils

import Control.Lens hiding (Context)
import Control.Monad.Except
import Control.Monad.Reader
import Data.List
import Data.Ord

-- | Predicate of whether a given term is well-typed in the given context.
wellTyped :: Context -> Term -> Bool
wellTyped ctx = succeeded ctx . typeCheck

-- | Check the type of a term in the given context. Returns the type
-- if the term is well-typed, and gives an error otherwise.
typeCheck :: Term -> TC Type
typeCheck (Var v) = fromCtx v
typeCheck (Ctor c args) = do
  ty <- lookupCtor c
  tcArgList ty args
typeCheck (Lam (x,xTy) body) = do
  typeCheck xTy >>= whnf >>= \case
    (Ty n) -> Pi (x,xTy) <$> extendCtx (x,xTy) (typeCheck body)
    t  -> throwError $ TypeError [PS "Expected type (Ty n), got type", PT t]
typeCheck (Pi (x,xTy) ret) = do
  typeCheck xTy >>= whnf >>= \case
    (Ty n) -> do
      extendCtx (x,xTy) (typeCheck ret) >>= whnf >>= \case
        (Ty m) -> return (Ty (max n m))
        t  -> throwError $ TypeError
          [PS "Expected a (Ty n), got type", PT t]
    t -> throwError $ TypeError [PS "Expected a (Ty n), got type ", PT t]
typeCheck (App a b) =
  typeCheck a >>= whnf >>= \case
    Pi (x,xTy) ret -> do
      bTy <- typeCheck b
      extendTypeError (betaEq bTy xTy) [PS "When type-checking", PT (App a b)]
      return (subst x b ret)
    t -> throwError $ TypeError [PS "Trying to apply a non-function type in the term", PT (App t b)]
typeCheck (Ty n) = return (Ty (n+1))
typeCheck (Case e xs) = do
  t <- typeCheck e
  dataname <- appData t
  datatype@(DataDecl name ty ctors) <- lookupData dataname
  --TODO: use sets instead of lists
  let datactors = sortOn fst ctors
  let casectors = sortOn ctConstructor xs
  caseTys <- zipWithM (tcCase datatype) datactors casectors
  adjacentsSatisfyM betaEq caseTys
  case caseTys of
    -- We need type inference to know what type to make an empty case
    [] -> throwError $ TypeError [PS "Empty cases are not yet supported"]
    (x:_) -> whnf x

  where
    tcCase datatype (ctora, ty) (CaseTerm ctorb bindings expr)
      | ctora /= ctorb = throwError $ TypeError [PS "Constructors for datatype", PD datatype, PS "not matched by case expression", PT (Case e xs)]
      | otherwise = do
          ty' <- whnf ty
          bindings' <- mapM (traverseOf _2 whnf) bindings
          tcArgList ty' (snd <$> bindings')
          foldl (flip extendCtx) (typeCheck expr) bindings'

-- | Check that a list of arguments could be applied to a term with a
-- given Pi type, and return the value that would be returned as a
-- result of this application.
tcArgList (Pi (x, xTy) ret) (yTy:bs) = do
  --TODO: better type errors
  xTy `betaEq` yTy
  extendCtx (x,xTy) $ tcArgList ret bs
tcArgList ty [] = do
  return ty
tcArgList _ _ = throwError $ TypeError [PS "Couldn't match case term with constructor type"]

typeCheckTopLevel :: TopLevel -> TC Context
typeCheckTopLevel (TLData d) = typeCheckData d
typeCheckTopLevel (TLDef d) = typeCheckDefinition d

typeCheckDefinition :: Definition -> TC Context
typeCheckDefinition (Definition name ty body) = do
  hasType body ty
  insertEnv name body <$> insertCtx name ty <$> ask

-- | Type-check a data declaration. If successful, it adds the type
-- and constructors to the context.
typeCheckData :: DataDecl -> TC Context
typeCheckData d@(DataDecl name ty cs) = do
  ask >>= \ctx -> nameNotDefined ctx name
  isType ty
  local (insertCtx name ty) $ do
    bs <- mapM typeCheckC cs
    ctx <- ask
    mapM_ (nameNotDefined ctx) (fst <$> bs)
    when (hasDuplicates (fst <$> bs))
      (throwError $ TypeError [PS "Duplicate constructors in", PN name])
    return (insertDataDecl d $ foldr (\(n,t) -> insertCtx n t) ctx bs)

  where
    typeCheckC (c, cTy) = do
      isType cTy
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
nameNotDefined :: MonadError TypeError m => Context -> Name -> m ()
nameNotDefined ctx n = do
  case lookupCtx n ctx of
    Nothing -> success
    Just _ -> throwError $ TypeError [PS "The name", PN n, PS "is already defined"]

-- | Check that a given term has the given type.
hasType :: Term -> Type -> TC ()
hasType t target = do
  ctx <- ask
  tTy <- typeCheck t
  extendTypeError (target `betaEq` tTy)
    [PS "while checking if", PT t, PS "has type", PT tTy
    ,PS "in the context", PC ctx]

fromCtx v = do
  ctx <- ask
  case lookupCtx v ctx of
    Nothing -> throwError $ TypeError [PS "Could not find", PN v, PS "in context."]
    Just ty -> return ty

-- | Returns the term's type if the given term is not a type; throws
-- an error otherwise.
notType t =
  typeCheck t >>= \case
    (Ty n) -> throwError $ TypeError
      [PS "Expected something not a type, got", PT t, PS ":", PT (Ty n)]
    ty -> return ty

-- | Returns () if the given term is a type; throws an error otherwise.
isType t = do
  typeCheck t >>= \case
    (Ty n) -> return ()
    term -> throwError $ TypeError
      [PS "Expected a type, got", PT t, PS ":", PT term]

-- | Helper function to type-check a single let binding.
typeCheckBinding ((x,xTy),val) = do
  ty <- typeCheck val
  isType xTy
  betaEq xTy ty

-- | Type-check a term and insert it into the context.
checkAndInsert :: Name -> Term -> TC Context
checkAndInsert name term = do
  ty <- typeCheck term
  insertCtx name ty . insertEnv name term <$> ask