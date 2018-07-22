module Utils where

-- | The `blackbird` combinator for composing a function of arity 2.
infixr 5 .:
(.:) = (.).(.)

-- | Get the maximum value in a list, returning a default value if the
--   list is empty.
maximumOr :: (Ord a) => a -> [a] -> a
maximumOr x [] = x
maximumOr _ xs = maximum xs

-- | Find the fixpoint of a function starting from a given argument.
fix f x | f x == x = x
        | otherwise = fix f (f x)

-- | Monadic version of 'fix'.
fixM f x | (x >>= f) == x = x
         | otherwise    = fixM f (x >>= f)
