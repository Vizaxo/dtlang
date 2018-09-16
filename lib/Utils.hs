{-# LANGUAGE UndecidableInstances #-}

module Utils where

import Control.Monad.State
import Control.Monad.Except
import Data.List
import Debug.Trace

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

-- | Throw an error if the given assertion fails.
assert True e = return ()
assert False e = error $ "Assertion failed! " <> e

-- | Throw an error if the given expression returns a Left.
assertRight (Right _) e = return ()
assertRight (Left e') e = error $ e <> show e'

foldr1M f xs = foldl1 f' return xs
  where f' k x z = f x z >>= k

adjacentsSatisfyM p (x:y:xs) = p x y >> adjacentsSatisfyM p (y:xs)
adjacentsSatisfyM p _ = return ()

spy :: Show a => a -> a
spy a = trace (show a) a

hasDuplicates xs = length xs /= length (nub xs)
