-- | An implementation of Palka et al. 2011 [1]. This alows the
-- QuickCheck generator to always generate a well-typed term
-- efficiently, so much larger terms can be generated.
--
-- [1]: Michał H. Pałka, Koen Claessen, Alejandro Russo, and John
-- Hughes. 2011. Testing an optimising compiler by generating random
-- lambda terms. In Proceedings of the 6th International Workshop on
-- Automation of Software Test (AST '11).
module Test.BackTrackGen where

import Utils

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.Maybe
import Test.QuickCheck hiding (variant, sized, resize, choose, frequency)
import QuickCheck.GenT
import System.Random

-- | A generator which can fail. This allows backtracking, using 'freqBacktrack'.
type BackTrackGen a = MaybeT Gen a

-- | Run a 'BackTrackGen'. This is currently just 'runMaybeT', but
-- might change if more transformers are added to the monad.
runBackTrackGen :: BackTrackGen a -> Gen (Maybe a)
runBackTrackGen = runMaybeT

instance MonadGen m => MonadGen (MaybeT m) where
  liftGen :: Gen a -> MaybeT m a
  liftGen = lift . liftGen

  variant :: Integral n => n -> MaybeT m a -> MaybeT m a
  variant n (MaybeT mgx) = MaybeT (variant n mgx)

  sized :: (Int -> MaybeT m a) -> MaybeT m a
  sized (smgx) = MaybeT (sized (runMaybeT . smgx))

  resize :: Int -> MaybeT m a -> MaybeT m a
  resize n (MaybeT ma) = MaybeT (resize n ma)

  choose :: Random a => (a,a) -> MaybeT m a
  choose = lift . choose

-- | A re-implementation of 'scale' for any 'MonadGen'.
scale :: MonadGen m => (Int -> Int) -> m a -> m a
scale f m = sized $ \size -> resize (f size) m

-- | The QuickCheck 'frequency' function, but it will backtrack over
-- failed branches. It will never revisit a failed branch, so nested
-- branches should also use this function at failure points if you
-- want to consider all possible branches.
freqBacktrack :: [(Int, BackTrackGen a)] -> BackTrackGen a
freqBacktrack [] = mzero
freqBacktrack xs = MaybeT $ do
  let tagged = zip (fst <$> xs) (return <$> [0..])
  index <- frequency tagged
  try <- runBackTrackGen $ snd $ xs !! index
  case try of
    Nothing -> runBackTrackGen $ freqBacktrack (xs `without` index)
    _-> return try

-- | 'freqBacktrack' properly backtracks over failed branches.
prop_backtracks = forAll (runMaybeT testBacktrack) isJust

--TODO: use this as a benchmark
expensiveBacktrack :: Int -> BackTrackGen Char
expensiveBacktrack n = iterate tree mzero !! 2
  where tree x = freqBacktrack $ replicate n (1, x)


testBacktrack :: BackTrackGen Char
testBacktrack = freqBacktrack
  [ (100, expensiveBacktrack 5)
  , (1, freqBacktrack [ (1, freqBacktrack [ (100, expensiveBacktrack 5)
                                          , (1, return 'a')
                                          , (100, expensiveBacktrack 5)
                                          , (100, expensiveBacktrack 5)
                                          , (100, expensiveBacktrack 5)
                                          , (100, expensiveBacktrack 5)
                                          , (100, expensiveBacktrack 5)
                                          ])
                      , (100, expensiveBacktrack 5)
                      ])
  , (100, expensiveBacktrack 5)
  , (100, expensiveBacktrack 5)
  , (100, expensiveBacktrack 5)
  , (100, expensiveBacktrack 5)
  , (100, expensiveBacktrack 5)
  , (100, expensiveBacktrack 5)
  ]
