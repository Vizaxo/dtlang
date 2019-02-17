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

typeCheck :: Term -> TC Type
typeCheck = fmap extract . typeCheck'

typeCheck' :: Term -> TC (Cofree TermF Type)
typeCheck' t = extendError (TEErrorWhenChecking t) (tc t) where
  tc (Var v) = (:<) <$> fromCtx v <*> pure (VarF v)
  tc (Ctor c args) = do
    ty <- lookupCtor c
    t <- tcArgList ty args
    args' <- mapM tc args
    pure (t :< CtorF c args')
  tc (Lam (x, xTy) body) = do
    xTyAnn <- tc xTy
    whnf (extract xTyAnn) >>= \case
      (Ty n) -> do
        bodyAnn <- extendCtx (x, xTy) (tc body)
        bodyAnn' <- whnf (extract bodyAnn)
        pure $ Pi (x, xTy) bodyAnn' :< LamF (x, xTyAnn) bodyAnn
      t -> throwError (TEExpectedTy t)
  tc (Pi (x, xTy) ret) = do
    xTyAnn <- tc xTy
    whnf (extract xTyAnn) >>= \case
      Ty n -> do
        retAnn <- extendCtx (x, xTy) (tc ret)
        whnf (extract retAnn) >>= \case
          Ty m -> pure $ Ty (max n m) :< PiF (x, xTyAnn) retAnn
          t -> throwError (TEExpectedTy t)
      t -> throwError (TEExpectedTy t)
  tc (App a b) = do
    aAnn <- tc a
    whnf (extract aAnn) >>= \case
      Pi (x, xTy) ret -> do
        bAnn <- tc b
        betaEq (extract bAnn) xTy
        ret' <- whnf (subst x b ret)
        pure $ ret' :< AppF aAnn bAnn
      t -> throwError (TEExpectedPi t)
  tc (Ty n) = pure $ Ty (n+1) :< TyF n
  tc (Case expr motive cases) = do
    exprAnn <- tc expr
    motiveAnn <- tc motive
    whnf (extract motiveAnn) >>= \case
      Pi _ _ -> pure ()
      t -> throwError (TEExpectedPi t)
    dataname <- appData (extract exprAnn)
    datatype@(DataDecl name ty ctors) <- lookupData dataname
    casesAnn <- perfectMerge ctors cases undefined undefined tcCase
    retTy <- whnf (motive `App` expr)
    pure (retTy :< CaseF exprAnn motiveAnn casesAnn)
      where
        tcCase :: Constructor -> Type -> CaseTerm -> TC (CaseTermF (Cofree TermF Type))
        tcCase ctor args t@(CaseTerm bs e) = do
          argTys <- extractArgs args
          --TODO: perfectZipWith
          when (length argTys /= length bs) (throwError (TECaseWrongNumCtorArgs argTys t))
          extendCtxs (zip bs argTys) $ do
            eTy <- tc e
            eTy' <- whnf (extract eTy)
            betaEq eTy' =<< whnf (motive `App` Ctor ctor (Var <$> bs))
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
  yTy `hasType` xTy
  extendCtx (x,xTy) $ tcArgList ret bs
tcArgList ty [] = do
  return ty
tcArgList t args = throwError $ TECtorWrongNumArgs t args

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
  False -> throwError $ TEDataReturnsWrong n name

returnTy (Pi (_,_) ret) = whnf ret >>= returnTy
returnTy t = return t

appData (App a b) = whnf a >>= appData
appData (Var retName) = return retName
appData _ = throwError $ TEAppDataError

-- | Check that a given name does not already occur in the context.
nameNotDefined :: MonadError TypeError m => Context -> Name -> m ()
nameNotDefined ctx n = do
  case lookupCtx n ctx of
    Nothing -> success
    Just _ -> throwError $ TENameAlreadyDefined

-- | Check that a given term has the given type.
hasType :: Term -> Type -> TC ()
hasType t target = do
  ctx <- ask
  tTy <- typeCheck t
  catchError (target `betaEq` tTy)
    (\err -> throwError (TEDoesntHaveType t target err))

fromCtx v = do
  ctx <- ask
  case lookupCtx v ctx of
    Nothing -> throwError $ TENotInContext v ctx
    Just ty -> return ty

-- | Returns the term's type if the given term is not a type; throws
-- an error otherwise.
notType t =
  typeCheck t >>= \case
    (Ty n) -> throwError (TEUnexpectedType t)
    ty -> return ty

-- | Returns () if the given term is a type; throws an error otherwise.
isType t = do
  typeCheck t >>= \case
    (Ty n) -> return ()
    term -> throwError (TEExpectedTy term)

-- | Type-check a term and insert it into the context.
checkAndInsert :: Name -> Term -> TC Context
checkAndInsert name term = do
  ty <- typeCheck term
  insertCtx name ty . insertEnv name term <$> ask
