module Utils where

infixr 5 .:
(.:) = (.).(.)

maximumOr :: (Ord a) => a -> [a] -> a
maximumOr x [] = x
maximumOr _ xs = maximum xs

-- | Find the fixpoint of a function starting from a given argument.
fix f x | f x == x = x
        | otherwise = fix f (f x)

-- | Monadic version of 'fix'.
fixM f x | (x >>= f) == x = x
         | otherwise    = fixM f (x >>= f)
