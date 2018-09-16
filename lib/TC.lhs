> module TC where

> import Types
> import Utils

> import Control.Lens hiding (Context)
> import Control.Monad.Except
> import Control.Monad.Reader
> import Control.Monad.State
> import Data.Either
> import Data.Maybe

The TC monad is where all type-checking is done.

> type TC a =

The context maps free variables to their types.

>   (ReaderT Context

It keeps track of the next generated (as opposed to user-specified)
variable to use.

>   (StateT GenVar

It will short-circuit when a type error is thrown, which can then be
printed to show the user.

>   (Except TypeError))) a

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
> extendCtx (n,v) = local (insertCtx n v)

We need a way to generate variables that are guaranteed to be fresh.

We get the name to use, then update the next variable that will be
used.

> fresh :: [Name] -> TC Name
> fresh avoid = do
>   v <- get
>   ctx <- ask
>   let existingGens = catMaybes $ (fromEnum <$>) . getGen <$> (fst <$> (getCtx ctx)) ++ avoid
>   let nextVar = toEnum $ max (fromEnum v) (1 + maximumOr (-1) (existingGens))
>   put $ succ nextVar
>   return $ Generated nextVar
>   where getGen (Generated v) = Just v
>         getGen _ = Nothing

Fresh should produce a variable that is not already present in the
context.

> prop_freshIsFresh :: Context -> [Name] -> Bool
> prop_freshIsFresh ctx existing = isRight $ runTC ctx $ do
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
> emptyCtx = Context [] [] []

> lookupCtx :: Name -> Context -> Maybe Term
> lookupCtx n (Context ctx _ _) = lookup n ctx

> insertCtx :: Name -> Term -> Context -> Context
> insertCtx n t (Context ctx env ds) = Context ((n,t):ctx) env ds

> insertEnv :: Name -> Term -> Context -> Context
> insertEnv n t (Context ctx env ds) = Context ctx ((n,t):env) ds

> lookupEnv :: Name -> Context -> Maybe Term
> lookupEnv n (Context _ env _) = lookup n env

> insertDataDecl :: DataDecl -> Context -> Context
> insertDataDecl d (Context ctx env ds) = Context ctx env (d:ds)

> lookupData' :: Name -> Context -> Maybe DataDecl
> lookupData' n (Context _ _ ds) = listToMaybe $ filter (\(DataDecl n' _ _) -> n == n') ds

> lookupData :: Name -> TC DataDecl
> lookupData n = do
>   ctx <- ask
>   case lookupData' n ctx of
>     Nothing -> throwError $ TypeError [PS "Type", PN n, PS "not found in context."]
>     Just d -> return d

> lookupCtor :: (MonadError TypeError m, MonadReader Context m) => Constructor -> m Type
> lookupCtor c = do
>   Context ctx _ ds <- ask
>   case listToMaybe $ catMaybes $ map findCtor ds of
>     Nothing -> throwError $ TypeError [PS "No constructor named", PN c, PS "in context"]
>     Just ty -> return ty
>   where findCtor (DataDecl _ _ ctors) = lookup c ctors

Run the TC monad, outputting all information. This is useful for debugging purposes.

> debugTC :: Context -> TC a -> Either TypeError (a, GenVar)
> debugTC ctx = runExcept . flip runStateT (toEnum @GenVar 0) . flip runReaderT ctx

Get the context that was generated from a TC computation.

> getCtxTC :: Context -> TC Context -> Either TypeError Context
> getCtxTC = ((^. _1) <$>) .: debugTC

We can run the TC monad. If a TypeError has occured elsewhere this
will be returned. Otherwise, we get the pure value back.

> runTC :: Context -> TC a -> Either TypeError a
> runTC ctx = ((^. _1) <$>) . (debugTC ctx)

> retRead :: MonadReader r m => m a -> m (a, r)
> retRead m = (,) <$> m <*> ask

For functions returning a `TC ()`, writing `success` is clearer than
writing `return ()`.

> success :: Monad m => m ()
> success = return ()
