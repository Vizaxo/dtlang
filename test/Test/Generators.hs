module Test.Generators where

import Term
import TypeCheck
import Utils

import Control.Monad.LogicState
import Control.Monad.State
import Data.Either
import QuickCheck.GenT
import Test.QuickCheck hiding (suchThat, elements, frequency, sized, resize, suchThatMaybe, oneof, variant, choose)

-- | The starting variable, the next fresh variable to use, and the current
--   context from which bound variables are generated.
type BoundV v = (v, v, Context v)

-- | The monad transformer stack for generation of values that rely on the
--   state of bound variables.
--   This alows the generators to be much more likely to generate
--   well-typed terms, and to generate more deeply nested terms.
type CustomGen v a = (LogicStateT () (BoundV v) Gen) a
type TermGen v = CustomGen v (Term v)

-- | Run the CustomGen term, creating a generator.
runCustomGen :: forall v a. v -> CustomGen v a -> Gen a
runCustomGen v0 = observeT ((), (v0,v0,([]::Context v)))

instance MonadGen m => MonadGen (StateT s m) where
  --liftGen :: Gen a -> StateT s m a
  liftGen = lift . liftGen
  --variant :: Integral n => n -> StateT s m a -> StateT s m a
  variant n (StateT mgx) = StateT (\s -> variant n (mgx s))
  --sized :: (Int -> StateT s m a) -> StateT s m a
  sized sgma
    = StateT (\s -> sized $ \size -> case sgma size of
                                       StateT sgen -> sgen s)
  --resize :: Int -> StateT s m a -> StateT s m a
  resize n (StateT smgx) = StateT (\s -> resize n (smgx s))
  --choose :: Random a => (a,a) -> StateT s m a
  choose = lift . choose

instance MonadGen m => MonadGen (LogicStateT gs bs m) where
  --liftGen :: Gen a -> LogicStateT gs bs m a
  liftGen = lift . liftGen
  --variant :: Integral n => n -> LogicStateT gs bs m a -> LogicStateT gs bs m a
  variant n (LogicStateT m) = LogicStateT (\s f -> variant n (m s f))
  --sized :: (Int -> LogicStateT gs bs m a) -> LogicStateT gs bs m a
  sized sgma
    = LogicStateT (\s f -> sized $ \size -> case sgma size of
                                 LogicStateT m -> m s f)
  --resize :: Int -> LogicStateT gs bs m a -> LogicStateT gs bs m a
  resize n (LogicStateT m) = LogicStateT (\s f -> resize n (m s f))
  --choose :: Random a => (a,a) -> g a
  choose = lift . choose

-- | Helper function for getting the current state of bound variables.
getV :: CustomGen v (v, v, Context v)
getV = fmap snd get

-- | Helper function for setting the current state of bound variables.
putV :: (v,v,Context v) -> CustomGen v ()
putV v = put ((),v)

-- | Generate a variable that's in scope.
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

-- | Generate a variable that is bound by a surrounding lambda, pi, or let term.
genVar :: (Eq v, Show v, Enum v) => TermGen v
genVar = Var <$> genExistingVar

-- | Generate a random lambda abstraction.
genLam :: (Eq v, Show v, Enum v) => TermGen v
genLam = sized $ \size -> do
  (_,_,gamma) <- getV
  Lam <$> genNewBinding <*> genTerm

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

-- | Generate a random letrec expression.
genLetrec :: (Eq v, Show v, Enum v) => TermGen v
genLetrec = do
  (_,_,gamma) <- getV
  do numBindings <- frequency $ [(10, return 0), (40, return 1), (20, return 2), (10, return 3)]
     --Generate bindings first so they can be used in the terms
     bindings <- replicateM numBindings genNewBinding
     terms <- replicateM numBindings genTerm
     body <- genTerm
     (return $ Let Rec (zip bindings terms) body)

-- | Generate a random (non-recursive) let expression.
genLet :: (Eq v, Show v, Enum v) => TermGen v
genLet = do
  (_,_,gamma) <- getV
  do numBindings <- frequency $ [(10, return 0), (40, return 1), (20, return 2), (10, return 3)]
     --Generate bindings second so they can't be used in the terms
     terms <- replicateM numBindings genTerm
     bindings <- replicateM numBindings genNewBinding
     body <- genTerm
     return $ Let NoRec (zip bindings terms) body

-- | Generate a random well-typed term, attempting to generate
--   sensible values to make generating well-typed terms more
--   efficient and have a better distribution.  Uses 'CustomGen' to
--   determine the currently bound variables.
genTerm :: (Eq v, Show v, Enum v) => TermGen v
genTerm = sized $ \size -> do
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

-- | Generate a random well-typed 'Term', taking the starting variable
--   as an argument.  The variable enum should be able to produce a
--   large number of results; for example 'Int' or 'Char'.
generateTerm :: (Eq v, Show v, Enum v) => v -> Gen (Term v)
generateTerm v0 = sized $ \size -> runCustomGen v0 genTerm `suchThat'` (\t -> wellTyped [] t && maxNesting t >= size `div` 30)

-- | Generate a random well-typed 'Term', starting variables with 'a'.
genCharTerm = generateTerm 'a'

-- TODO: make the Arbitrary instances for Term and WellTyped separate,
-- so random not-well-typed terms can be generated.
-- | Generate an arbitrary 'Term', and allow it to be shrunk to pin down
--   bugs detected by QuickCheck.
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

-- | A helper function for 'shrink' on 'Term's.
shrinkBinding :: (Eq v, Show v, Enum v) => (Binding v, Term v) -> [(Binding v, Term v)]
shrinkBinding ((v,vTy),val) = [((v,vTy'),val') | vTy' <- shrink vTy
                                               , val' <- shrink val]

-- TODO: use typeCheck to enforce the well-typed-ness of these.
-- | A 'WellTyped' is a 'Term' that is well-typed.
newtype WellTyped v = WellTyped (Term v)
  deriving (Eq, Show)

instance (Eq v, Show v, Enum v) => Arbitrary (WellTyped v) where
  arbitrary = WellTyped <$> generateTerm (toEnum 0)

  shrink (WellTyped t) = WellTyped <$> (rights $ typeCheck [] <$> shrink t)

-- | Backtrack over a computation if the result doesn't satisfy a predicate.
gen `backtrackUnless` p = do
  x <- gen
  if p x
    then return x
    else join $ backtrack genTerm

-- | Custom version of 'SuchThat' which doesn't affect the size
--   parameter of the generator.
gen `suchThat'` p = do
  x <- gen
  if p x
    then return x
    else gen `suchThat'` p
