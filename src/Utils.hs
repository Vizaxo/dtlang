{-# LANGUAGE UndecidableInstances #-}

module Utils where

import Control.Monad.State
import Control.Monad.Trans.MultiState
import Control.Monad.Except

-- | The `blackbird` combinator for composing a function of arity 2.
infixr 5 .:
(.:) = (.).(.)

-- | Get the maximum value in a list, returning a default value if the
--   list is empty.
maximumOr :: (Ord a) => a -> [a] -> a
maximumOr x [] = x
maximumOr _ xs = maximum xs

-- | Monadic version of 'fix'.
fixM f x | (x >>= f) == x = x
         | otherwise    = fixM f (x >>= f)

-- | Remove the given element of a list.
without :: [a] -> Int -> [a]
without (x:xs) 0 = xs
without (x:xs) n = x : without xs (n-1)

-- | The 'modify' function for 'MultiState'

mModify f = do
  st <- mGet
  mSet (f st)


instance MonadError e m => MonadError e (MultiStateT s m) where
  throwError = lift . throwError
  catchError (MultiStateT ma) h = MultiStateT $ StateT $ \s -> runStateT ma s `catchError` \e -> runMultiStateT s (h e)
