module TestASM where

import Data.Maybe
import Control.Monad.Trans.Maybe
import Test.QuickCheck

import ASM

prop_instructionsValid :: Instructions -> Property
prop_instructionsValid = ioProperty . (isJust <$>) . runMaybeT . assemble
