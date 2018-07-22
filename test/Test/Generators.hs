module Test.Generators where

import TypeCheck
import Term
import Utils

import Control.Applicative
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.LogicState
import Data.Either
import Data.Maybe
import QuickCheck.GenT
import Test.QuickCheck hiding (suchThat, elements, frequency, sized, resize, suchThatMaybe, oneof, variant, choose)
import Debug.Trace


-- | The starting variable, and the next fresh variable to use.
type BoundV v = (v, v, Context v)

-- | The monad transformer stack for generation of values that rely on the
--   state of bound variables.
--   This alows the generators to be much more likely to generate
--   well-typed terms, and to generate more deeply nested terms.
--type CustomGen v a = MaybeT (StateT (BoundV v) Gen) a
type CustomGen v a = (LogicStateT () (BoundV v) Gen) a
type TermGen v = CustomGen v (Term v)

runCustomGen :: forall v a. v -> CustomGen v a -> Gen a
--runCustomGen v0 gen = observeT $ evalState' (v0,v0,[]) gen
runCustomGen v0 = (observeT ((),(v0,v0,([]::Context v))))-- <$> runGenT gen

evalStateT' :: Monad m => s -> StateT s m a -> m a
evalStateT' = flip evalStateT

instance (Monad m, Alternative m) => Alternative (GenT m) where
  empty = lift empty
  (GenT genA) <|> (GenT genB) = GenT (\g i -> genA g i <|> genB g i)

instance MonadPlus m => MonadPlus (GenT m) where
  mzero = empty
  mplus = (<|>)

instance MonadGen m => MonadGen (StateT s m) where
  --liftGen :: Gen a -> StateT s m a
  liftGen = lift . liftGen

  --variant :: Integral n => n -> StateT s m a -> StateT s m a
  variant n (StateT mgx) = StateT (\s -> variant n (mgx s))

  --sized :: (Int -> StateT s m a) -> StateT s m a
  sized sgma
    = StateT (\s -> sized $ \size -> case sgma size of
                                       StateT sgen -> sgen s) --I think this is infinite?

  --resize :: Int -> StateT s m a -> StateT s m a
  resize n (StateT smgx) = StateT (\s -> resize n (smgx s))

  --choose :: Random a => (a,a) -> StateT s m a
  choose = lift . choose

instance MonadGen m => MonadGen (LogicStateT gs bs m) where
  --liftGen :: Gen a -> LogicStateT gs bs m a
  liftGen = lift . liftGen

  --variant :: Integral n => n -> LogicStateT gs bs m a -> LogicStateT gs bs m a
  variant n (LogicStateT m) = LogicStateT (\s f -> variant n (m s f))
  --variant = lift .: variant

  --sized :: (Int -> LogicStateT gs bs m a) -> LogicStateT gs bs m a
  sized sgma
    = LogicStateT (\s f -> sized $ \size -> case sgma size of
                                 LogicStateT m -> m s f)

  --resize :: Int -> LogicStateT gs bs m a -> LogicStateT gs bs m a
  resize n (LogicStateT m) = LogicStateT (\s f -> resize n (m s f))

  --choose :: Random a => (a,a) -> g a
  choose = lift . choose


instance MonadGen m => MonadGen (MaybeT m) where
  --liftGen :: Gen a -> MaybeT m a
  liftGen = lift . liftGen

  --variant :: Integral n => n -> MaybeT m a -> MaybeT m a
  variant n (MaybeT mgx) = MaybeT (variant n mgx)

  --sized :: (Int -> MaybeT m a) -> MaybeT m a
  sized sgma
    = MaybeT (sized $ \size -> case sgma size of
                                 MaybeT gen -> gen)

  --resize :: Int -> MaybeT m a -> MaybeT m a
  resize n (MaybeT mgx) = MaybeT (resize n mgx)

  --choose :: Random a => (a,a) -> g a
  choose = lift . choose


-- | Helper function for getting the current state of bound variables.
getV :: CustomGen v (v, v, Context v)
getV = fmap snd get

putV :: (v,v,Context v) -> CustomGen v ()
putV v = put ((),v)

-- | Eval a given state transformer with the starting state. This is useful for
--   chaining evaluations of StateT, keeping the starting state adjacent to the
--   call of eval for each layer.
evalState' :: Monad m => s -> StateT s m a -> m a
evalState' = flip evalStateT

genExistingVar :: (Eq v, Show v, Enum v) => CustomGen v v
genExistingVar = do
  (v0, vmax, _) <- getV
  elements [v0..pred vmax]

-- | Generate a fresh variable with a generated type, and use it as a binding.
genNewBinding :: (Eq v, Show v, Enum v) => CustomGen v (Binding v)
genNewBinding = do
  (v0, v, gamma) <- getV
  ty <- genTerm
  putV (v0, succ v, (v,ty):gamma)
  return (v, ty)

-- | Generate a variable that is bound by a surrounding lambda or pi term.
genVar :: (Eq v, Show v, Enum v) => TermGen v
genVar = Var <$> genExistingVar

-- | Generate a random lambda abstraction.
genLam :: (Eq v, Show v, Enum v) => TermGen v
genLam = sized $ \size -> do
  (_,_,gamma) <- getV
  Lam <$> genNewBinding <*> genTerm

-- TODO: only generate types as the nested terms
-- | Generate a random pi type.
genPi :: (Eq v, Show v, Enum v) => TermGen v
genPi = do (_,_,gamma) <- getV
           Pi <$> genNewBinding <*> genTerm

-- | Generate a random application of one term to another.
genApp :: (Eq v, Show v, Enum v) => TermGen v
genApp = sized $ \size -> do
  (_,_,gamma) <- getV
  App <$> genLam <*> genTerm

-- | Generate a type (currently only generates 'Ty').
genTy :: TermGen v
genTy = return Ty

-- | Generate a type (currently only generates 'Ty').
genLetrec :: (Eq v, Show v, Enum v) => TermGen v
genLetrec = do
  (_,_,gamma) <- getV
  do numBindings <- frequency $ [(10, return 0), (40, return 1), (20, return 2), (10, return 3)]
     --Must do this first, so that the new variables are in scope for the other bodies
     --Generate bindings first so they can be used in the terms
     bindings <- replicateM numBindings genNewBinding
     terms <- replicateM numBindings genTerm
     body <- genTerm
     (return $ Let Rec (zip bindings terms) body)

genLet :: (Eq v, Show v, Enum v) => TermGen v
genLet = do
  (_,_,gamma) <- getV
  do numBindings <- frequency $ [(10, return 0), (40, return 1), (20, return 2), (10, return 3)]
     --Generate bindings second so they can't be used in the terms
     terms <- replicateM numBindings genTerm
     bindings <- replicateM numBindings genNewBinding
     body <- genTerm
     return $ Let NoRec (zip bindings terms) body

--TODO: handle state passing better
--TODO: make sure samples contain a healthy mix of all constructors.
--    Specifically, App seems very rare.
-- | Generate a random term, attempting to generate sensible values to make
--   generating well-typed terms more efficient and have a better distribution.
--   Uses 'CustomGen' to determine the currently bound variables.
genTerm' :: (Eq v, Show v, Enum v) => Int -> TermGen v
genTerm' size = do
  (v0, v, gamma) <- getV
  (do let vFreq = if fromEnum v0 == fromEnum v then const 0 else id
      frequency [ (vFreq 1000, genVar)
                , (size*10, resize (size `div` 2) genLam)
                , (size*5, resize (size `div` 2) genPi)
                , (size*8, resize (size `div` 2) genApp)
                , (500, resize (size `div` 2) genTy)
                , (size*2, resize (size `div` 2) genLet)
                , (size*1, resize (size `div` 2) genLetrec)
                ])  `backtrackUnless` wellTyped gamma

genTerm :: (Eq v, Show v, Enum v) => TermGen v
genTerm = sized genTerm'

-- | Generate a random term, taking the starting variable as an argument.
--   The variable enum should be able to produce a large number of results;
--   for example 'Int' or 'Char'.
generateTerm :: (Eq v, Show v, Enum v) => v -> Gen (Term v)
generateTerm v0 = sized $ \size -> runCustomGen v0 genTerm `suchThat'` (\t -> wellTyped [] t && maxNesting t >= size `div` 30)

-- | Generate a random well-typed term, starting variables with 'a'.
genWellTyped = generateTerm 'a'

instance (Eq v, Show v, Enum v) => Arbitrary (Term v) where
  arbitrary = generateTerm (toEnum 0)

  shrink (Var v) = []
  shrink (Lam (x,xTy) body) = [body, xTy] ++
                              [Lam (x,xTy') body' | (body', xTy') <- shrink (body, xTy)]
  shrink (Pi (x,xTy) ret) = [ret, xTy] ++
                            [Pi (x,xTy') ret' | (ret', xTy') <- shrink (ret, xTy)]
  shrink (App a b) = [a, b] ++
                     [App a' b' | (a',b') <- shrink (a,b)]
  shrink Ty = []
  shrink (Let rec bindings body) =
    [body] ++
    fmap snd bindings ++
    fmap (snd . fst) bindings ++
    [Let rec bindings' body' | bindings' <- shrinkList shrinkBinding bindings
                             , body' <- shrink body]
  shrink _ = []

shrinkBinding :: (Eq v, Show v, Enum v) => (Binding v, Term v) -> [(Binding v, Term v)]
shrinkBinding ((v,vTy),val) = [((v,vTy'),val') | vTy' <- shrink vTy
                                               , val' <- shrink val]

newtype WellTyped v = WellTyped (Term v)
  deriving (Eq, Show)

instance (Eq v, Show v, Enum v) => Arbitrary (WellTyped v) where
  arbitrary = WellTyped <$> generateTerm (toEnum 0)

  shrink (WellTyped t) = WellTyped <$> (rights $ typeCheck [] <$> shrink t)

gen `backtrackUnless` p = do
  x <- gen
  if p x
    then return x
    else join $ backtrack genTerm

gen `suchThat'` p = do
  x <- gen
  if p x
    then return x
    else gen `suchThat'` p
