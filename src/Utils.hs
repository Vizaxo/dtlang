module Utils where

infixr 5 .:
(.:) = (.).(.)

maximumOr :: (Ord a) => a -> [a] -> a
maximumOr x [] = x
maximumOr _ xs = maximum xs
