module Utils where

import Control.Monad.Except
import Data.Functor.Foldable
import Data.Map (Map, fromList)
import Data.Map.Merge.Lazy
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
without xs i = error
  $ "without: list index " <> show i
  <> "out of bounds of list length " <> show (length xs)

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

cataM' :: (Functor f, Traversable f, Monad m) => (f a -> m a) -> Fix f -> m a
cataM' alg f = alg =<< sequence (cataM alg <$> unfix f)

-- | A monadic catamorphism, where the algebra can have monadic
-- effects which will be propogated to the top-level.
cataM :: (Recursive t, Traversable (Base t), Monad m) => (Base t a -> m a) -> t -> m a
cataM alg f = alg =<< sequence (cataM alg <$> project f)

maybeMPlus :: MonadPlus m => Maybe a -> m a
maybeMPlus = maybe mzero pure

withError :: (MonadError e' m) => (e -> e') -> ExceptT e m a -> m a
withError f ma = do
  runExceptT ma >>= \case
    Left e -> throwError (f e)
    Right x -> pure x

handleErrM :: Applicative m => Either a b -> (a -> m b) -> m b
handleErrM (Left x) f = f x
handleErrM (Right y) f = pure y


extractBase :: Corecursive t => Cofree (Base t) a -> t
extractBase (a :< f) = embed (extractBase <$> f)

splitCofree :: Corecursive t => Cofree (Base t) a -> (t, a)
splitCofree = extractBase &&& extract
perfectMerge :: forall k a e m b c. (Ord k, MonadError e m)
  => Map k a -> Map k b -> (k -> a -> e) -> (k -> b -> e) -> (a -> b -> m c) -> m (Map k c)
perfectMerge x y xe ye f = mergeA (missing xe) (missing ye) matched x y where
    missing e = traverseMissing (throwError .: e)
    matched = zipWithAMatched (\k x y -> f x y)

fromListNoDups :: Ord k => ([(k, v)] -> e) -> [(k, v)] -> Either e (Map k v)
fromListNoDups f kvs
  | length (nub ks) == length ks = pure (fromList kvs)
  | otherwise = Left (f kvs)
  where
    ks = fst <$> kvs
