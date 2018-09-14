module Interpret where

import Equality
import Examples
import TC
import Types

import Control.Monad.Except
import Control.Monad.Trans.MultiState

interpret :: MonadError TypeError m => Context -> Term -> m Term
interpret ctx = runMultiStateTNil . withMultiStateA ctx . whnf
