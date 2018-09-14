> module TC where

> import Types
> import Utils

> import Control.Lens hiding (Context)
> import Control.Monad.Except
> import Control.Monad.Trans.MultiState
> import Data.Either
> import Data.Maybe

The TC monad is where all type-checking is done.

> type TC a =

It keeps track of the next generated (as opposed to user-specified)
variable to use, and the current context.

>   (MultiStateT '[GenVar, Context]

It will short-circuit when a type error is thrown, which can then be
printed to show the user.

>   (Except TypeError)) a

Type errors are represented as a list of printing directives. In
future this will also contain other information, such as the error
location in the source code.

> data TypeError
>   = TypeError [ErrorPrint]
>   | InternalError [ErrorPrint]
>   deriving (Eq, Show)

> data ErrorPrint
>   = PT Term
>   | PN Name
>   | PS String
>   | PC Context
>   | PD DataDecl
>   deriving (Eq, Show)

The context can be extended with a new binding.

> extendCtx :: Binding -> TC a -> TC a
> extendCtx (n,v) ma = do
>   mModify (insertCtx n v)
>   ma

Run a TC computation without extending the context of the parent.

> isolateCtx :: TC a -> TC a
> isolateCtx ma = do
>   ctx <- mGet @Context
>   res <- ma
>   mSet ctx
>   return res

We need a way to generate variables that are guaranteed to be fresh.

We get the name to use, then update the next variable that will be
used.

> fresh :: [Name] -> TC Name
> fresh avoid = do
>   v <- mGet @GenVar
>   ctx <- mGet @Context
>   let existingGens = catMaybes $ (fromEnum <$>) . getGen <$> (fst <$> (getCtx ctx)) ++ avoid
>   let nextVar = toEnum $ max (fromEnum v) (1 + maximumOr (-1) (existingGens))
>   mSet $ succ nextVar
>   return $ Generated nextVar
>   where getGen (Generated v) = Just v
>         getGen _ = Nothing

Fresh should produce a variable that is not already present in the
context.

> prop_freshIsFresh :: Context -> [Name] -> Bool
> prop_freshIsFresh ctx existing = isRight $ runTC $ do
>   mSet ctx
>   z <- fresh existing
>   case elem z existing of
>     True -> throwError $ InternalError []
>     False -> return ()
>   case lookupCtx z ctx of
>     Nothing -> return ()
>     Just _ -> throwError $ InternalError []

If the given computation returns a type-error, add the given extra
information to the error.

This can be useful to add more context to error messages.

> extendTypeError :: MonadError TypeError m => m a -> [ErrorPrint] -> m a
> extendTypeError ma err = do
>   catchError ma $
>     \case
>       TypeError e -> throwError $ TypeError $ e <> err
>       e           -> throwError e

We start with an empty context.

> emptyCtx :: Context
> emptyCtx = Context [] []

> lookupCtx :: Name -> Context -> Maybe Term
> lookupCtx n (Context ctx _) = lookup n ctx

> insertCtx :: Name -> Term -> Context -> Context
> insertCtx n t (Context ctx ds) = Context ((n,t):ctx) ds

> insertDataDecl :: DataDecl -> Context -> Context
> insertDataDecl d (Context ctx ds) = Context ctx (d:ds)

> lookupData' :: Name -> Context -> Maybe DataDecl
> lookupData' n (Context _ ds) = listToMaybe $ filter (\(DataDecl n' _ _) -> n == n') ds

> lookupData :: Name -> TC DataDecl
> lookupData n = do
>   ctx <- mGet
>   case lookupData' n ctx of
>     Nothing -> throwError $ TypeError [PS "Type", PN n, PS "not found in context."]
>     Just d -> return d

> lookupCtor :: (MonadError TypeError m, MonadMultiGet Context m) => Constructor -> m Type
> lookupCtor c = do
>   Context ctx ds <- mGet
>   case listToMaybe $ catMaybes $ map findCtor ds of
>     Nothing -> throwError $ TypeError [PS "No constructor named", PN c, PS "in context"]
>     Just ty -> return ty
>   where findCtor (DataDecl _ _ ctors) = lookup c ctors

Run the TC monad, outputting all information. This is useful for debugging purposes.

> debugTC :: TC a -> Either TypeError (a, GenVar, Context)
> debugTC = ((\((a,b),c) -> (a,b,c)) <$>) . runExcept . runMultiStateTNil . withMultiStateAS emptyCtx . withMultiStateAS (toEnum @GenVar 0)

Get the context that was generated from a TC computation.

> getCtxTC :: TC a -> Either TypeError Context
> getCtxTC = ((^. _3) <$>) . debugTC

We can run the TC monad. If a TypeError has occured elsewhere this
will be returned. Otherwise, we get the pure value back.

> runTC :: TC a -> Either TypeError a
> runTC = ((^. _1) <$>) . debugTC

For functions returning a `TC ()`, writing `success` is clearer than
writing `return ()`.

> success :: TC ()
> success = return ()
