module TypeCheck where

import Equality
import TC
import Term
import Types
import Utils

import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad.Except
import Control.Monad.Reader
import Data.Functor.Foldable
import Data.Map (traverseWithKey)

-- | Predicate of whether a given term is well-typed in the given context.
wellTyped :: Context -> Term -> Bool
wellTyped ctx = succeeded ctx . typeCheck

type TypeF = TermF

typeCheck :: Term -> TC Type
typeCheck = fmap extract . typeCheck'

--TODO: rework errors completely
typeError :: TC a
typeError = throwError (TypeError [])

typeCheck' :: Term -> TC (Cofree TermF Type)
typeCheck' (Var v) = (:<) <$> fromCtx v <*> pure (VarF v)
typeCheck' (Ctor c args) = do
  ty <- lookupCtor c
  t <- tcArgList ty args
  args' <- mapM typeCheck' args
  pure (t :< CtorF c args')
typeCheck' (Lam (x, xTy) body) = do
  xTyAnn <- typeCheck' xTy
  whnf (extract xTyAnn) >>= \case
    (Ty n) -> do
      bodyAnn <- extendCtx (x, xTy) (typeCheck' body)
      pure $ Pi (x, xTy) (extract bodyAnn) :< LamF (x, xTyAnn) bodyAnn
    _ -> typeError
typeCheck' (Pi (x, xTy) ret) = do
  xTyAnn <- typeCheck' xTy
  whnf (extract xTyAnn) >>= \case
    Ty n -> do
      retAnn <- extendCtx (x, xTy) (typeCheck' ret)
      whnf (extract retAnn) >>= \case
        Ty m -> pure $ Ty (max n m) :< PiF (x, xTyAnn) retAnn
        _ -> typeError
    _ -> typeError
typeCheck' (App a b) = do
  aAnn <- typeCheck' a
  whnf (extract aAnn) >>= \case
    Pi (x, xTy) ret -> do
      bAnn <- typeCheck' b
      betaEq (extract bAnn) xTy
      pure $ subst x b ret :< AppF aAnn bAnn
    _ -> typeError
typeCheck' (Ty n) = pure $ Ty (n+1) :< TyF n
typeCheck' (Case expr motive cases) = do
  exprAnn <- typeCheck' expr
  motiveAnn <- typeCheck' motive
  whnf (extract motiveAnn) >>= \case
    Ty n -> pure ()
    _ -> typeError
  dataname <- appData (extract exprAnn)
  datatype@(DataDecl name ty ctors) <- lookupData dataname
  casesAnn <- perfectMerge ctors cases undefined undefined tcCase
  pure (extract motiveAnn :< CaseF exprAnn motiveAnn casesAnn)
    where
      tcCase :: Type -> CaseTerm -> TC (CaseTermF (Cofree TermF Type))
      tcCase args (CaseTerm bs e) = do
        argTys <- extractArgs args
        --TODO: perfectZipWith
        when (length argTys /= length bs) (error "args not length bs")
        extendCtxs (zip bs argTys) $ do
          eTy <- typeCheck' e
          eTy' <- whnf (extract eTy)
          betaEq eTy' =<< whnf motive
          pure (CaseTerm bs eTy)
      -- TODO: match based on type (e.g. don't match VNil for Vect Zero a)

      extractArgs :: Type -> TC [Type]
      extractArgs = histo alg where
        alg :: TermF (Cofree TermF (TC [Type])) -> TC [Type]
        alg (PiF (x, xTy) ret) = do
          xTy' <- whnf (extractBase xTy)
          ret' <- extendCtx (x, xTy') (extract ret)
          pure (xTy':ret')
        alg _ = pure []

--TODO: rewrite this in terms of extractArgs
tcArgList (Pi (x, xTy) ret) (yTy:bs) = do
  --TODO: better type errors
  yTy `hasType` xTy
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
    bs <- traverseWithKey typeCheckC cs
    ctx <- ask
    mapM_ (nameNotDefined ctx) (fst <$> bs)
    return (insertDataDecl d $ foldr (\(n,t) -> insertCtx n t) ctx bs)

  where
    typeCheckC c cTy = do
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

-- | Type-check a term and insert it into the context.
checkAndInsert :: Name -> Term -> TC Context
checkAndInsert name term = do
  ty <- typeCheck term
  insertCtx name ty . insertEnv name term <$> ask
