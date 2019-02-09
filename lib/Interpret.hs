module Interpret where

import Equality
import TC
import Types

import Control.Monad.Except
import Control.Monad.Reader

interpret :: MonadError TypeError m => Context -> Term -> m Term
interpret ctx = flip runReaderT ctx . whnf
