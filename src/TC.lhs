> module TC where

> import Types

> import Control.Monad.Except
> import Control.Monad.Identity
> import Control.Monad.Reader
> import Control.Monad.State

The TC monad is where all type-checking is done.

> type TC a =

It keeps track of the current context of the type-checking.

>   ReaderT Context

It keeps track of the next generated (as opposed to user-specified)
variable to use.

>   (StateT GenVar

It will short-circuit when a type error is thrown, which can then be
printed to show the user.

>   (Except TypeError)) a

Type errors are represented as a list of printing directives. In
future this will also contain other information, such as the error
location in the source code.

> data TypeError
>   = TypeError [ErrorPrint]
>   | InternalError [ErrorPrint]

> data ErrorPrint
>   = PT Term
>   | PN Name
>   | PS String

The context can be extended with a new binding.

> extendCtx :: Binding -> TC a -> TC a
> extendCtx b ma = do
>   ctx <- ask
>   lift $ runReaderT ma (b:ctx)

We need a way to generate variables that are guaranteed to be fresh.

We get the name to use, then update the next variable that will be
used.

> fresh :: TC Name
> fresh = do
>   v <- get
>   modify succ
>   return $ Generated v

We start with an empty context.

> emptyCtx :: Context
> emptyCtx = []

We can run the TC monad. If a TypeError has occured elsewhere this
will be returned. Otherwise, we get the pure value back.

> runTC :: TC a -> Either TypeError a
> runTC tc = runExcept $ tc `runReaderT` emptyCtx `evalStateT` (toEnum 0)

For functions returning a `TC ()`, writing `success` is clearer than
writing `return ()`.

> success :: TC ()
> success = return ()
