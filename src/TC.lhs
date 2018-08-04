> module TC where

> import Types
> import Utils

> import Control.Monad.Except
> import Control.Monad.Trans.MultiState
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
>   deriving (Eq, Show)

The context can be extended with a new binding.

> extendCtx :: Binding -> TC a -> TC a
> extendCtx b ma = do
>   mModify (b:)
>   ma

We need a way to generate variables that are guaranteed to be fresh.

We get the name to use, then update the next variable that will be
used.

> fresh :: TC Name
> fresh = do
>   v <- mGet @GenVar
>   ctx <- mGet @Context
>   let existingGens = catMaybes $ ((fromEnum <$>) . getGen . fst) <$> ctx
>   let nextVar = toEnum $ max (fromEnum v) (maximumOr (-1) existingGens)
>   mSet $ succ nextVar
>   return $ Generated nextVar
>   where getGen (Generated v) = Just v
>         getGen _ = Nothing

We start with an empty context.

> emptyCtx :: Context
> emptyCtx = []

We can run the TC monad. If a TypeError has occured elsewhere this
will be returned. Otherwise, we get the pure value back.

> runTC :: TC a -> Either TypeError a
> runTC = runExcept . runMultiStateTNil . withMultiStateA emptyCtx . withMultiStateA (toEnum 0)

> debugTC :: TC a -> Either TypeError (a, GenVar, Context)
> debugTC = ((\((a,b),c) -> (a,b,c)) <$>) . runExcept . runMultiStateTNil . withMultiStateAS emptyCtx . withMultiStateAS (toEnum @GenVar 0)

For functions returning a `TC ()`, writing `success` is clearer than
writing `return ()`.

> success :: TC ()
> success = return ()
