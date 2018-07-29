-- | An implementation of Palka et al. 2011 [1]. This alows the
-- QuickCheck generator to always generate a well-typed term
-- efficiently, so much larger terms can be generated.
--
-- [1]: Michał H. Pałka, Koen Claessen, Alejandro Russo, and John
-- Hughes. 2011. Testing an optimising compiler by generating random
-- lambda terms. In Proceedings of the 6th International Workshop on
-- Automation of Software Test (AST '11).
module Test.BackTrackGen where

import Term
import TypeCheck
import Utils

import Control.Monad
import Data.Maybe
import Test.QuickCheck

--TODO: implement backtracking in the monad?
-- | A generator which can fail. This allows backtracking, using 'freqBacktrack'.
type BackTrackGen a = Gen (Maybe a)

-- | The QuickCheck 'frequency' function, but it will backtrack over
-- failed branches. It will never revisit a failed branch, so nested
-- branches should also use this function at failure points if you
-- want to consider all possible branches.
freqBacktrack :: [(Int, BackTrackGen a)] -> BackTrackGen a
freqBacktrack [] = return mzero
freqBacktrack xs = do
  let tagged = zip (fst <$> xs) (return <$> [0..])
  index <- frequency tagged
  try <- snd $ xs !! index
  case try of
    Nothing -> freqBacktrack (xs `without` index)
    _ -> return try

-- | 'freqBacktrack' properly backtracks over failed branches.
prop_backtracks = forAll testBacktrack isJust

testBacktrack :: BackTrackGen Char
testBacktrack = freqBacktrack
  [ (10, return mzero)
  , (1, freqBacktrack [ (1, freqBacktrack [ (10, return mzero)
                                          , (1, return $ return 'a')

                                          , (1, freqBacktrack [ (10, return mzero)
                                                              , (1, return mzero)
                                                              ])
                                          , (10, return mzero)
                                          ])
                      , (10, return mzero)
                      ])
  , (1, return mzero)
  , (10, freqBacktrack [ (1, freqBacktrack [ (10, return mzero)
                                          , (1, return mzero)
                                          ])
                      , (10, return mzero)
                      ])
  ]

