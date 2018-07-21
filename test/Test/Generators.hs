module Test.Generators where

import TypeCheck
import Term

import Control.Monad.State
import Test.QuickCheck

-- | The starting variable, and the next fresh variable to use.
type BoundV v = (v, v)

-- | The desired maximum nesting level of the current term.
type Nesting = Int

-- | The monad transformer stack for generation of values that rely on the
--   state of bound variables and current nesting level.
--   This alows the generators to be much more likely to generate
--   well-typed terms, and to generate more deeply nested terms.
type CustomGen v a = StateT (BoundV v) (StateT Nesting Gen) a
type TermGen v = CustomGen v (Term v)

-- | Helper function for getting the current state of bound variables.
getV :: CustomGen v (v,v)
getV = get

-- | Helper function for getting the current desired maximum nesting level.
getNesting :: CustomGen v Int
getNesting = lift get

-- | Eval a given state transformer with the starting state. This is useful for
--   chaining evaluations of StateT, keeping the starting state adjacent to the
--   call of eval for each layer.
evalStateT' :: Monad m => s -> StateT s m a -> m a
evalStateT' = flip evalStateT

genExistingVar :: Enum v => CustomGen v v
genExistingVar = do
  (v0, vmax) <- getV
  lift $ lift $ elements [v0..pred vmax]

-- | Generate a fresh variable with a generated type, and use it as a binding.
genNewBinding :: Enum v => CustomGen v (Binding v)
genNewBinding= do
  (v0, v) <- getV
  ty <- genTerm
  put $ (v0, succ v)
  return (v, ty)

-- | Generate a variable that is bound by a surrounding lambda or pi term.
genVar :: Enum v => TermGen v
genVar = Var <$> genExistingVar

-- | Generate a random lambda abstraction.
genLam :: Enum v => TermGen v
genLam = Lam <$> genNewBinding <*> genTerm

-- TODO: only generate types as the nested terms
-- | Generate a random pi type.
genPi :: Enum v => TermGen v
genPi = Pi <$> genNewBinding <*> genTerm

-- TODO: generate App terms that are more likely to be well-typed
-- | Generate a random application of one term to another.
genApp :: Enum v => TermGen v
genApp = App <$> genTerm <*> genTerm

-- | Generate a type (currently only generates 'Ty').
genTy :: TermGen v
genTy = return Ty

-- | Generate a type (currently only generates 'Ty').
genLetrec :: Enum v => TermGen v
genLetrec = do
  numBindings <- lift . lift . elements $ [0..3]
  --Must do this first, so that the new variables are in scope for the other bodies
  --bindings <- replicateM numBindings genNewBinding
  --letBinds <- mapM (\b -> genTerm >>= fmap return (b,)) bindings
  --Generate bindings first so they can be used in the terms
  bindings <- replicateM numBindings genNewBinding
  terms <- replicateM numBindings genTerm
  body <- genTerm
  return $ Let Rec (zip bindings terms) body

genLet :: Enum v => TermGen v
genLet = do
  numBindings <- lift . lift . elements $ [0..3]
  --Generate bindings second so they can't be used in the terms
  terms <- replicateM numBindings genTerm
  bindings <- replicateM numBindings genNewBinding
  body <- genTerm
  return $ Let NoRec (zip bindings terms) body

--TODO: handle state passing better
-- | Pick a random generator from a list, weighted by the given frequency.
--   This is a lifting of 'frequency' to work with 'CustomGen'.
freq :: [(Int, CustomGen v a)] -> CustomGen v a
freq gens = do
  nesting <- getNesting
  v <- getV
  let evalCustomGen = evalStateT' (nesting - 1) . evalStateT' v
  lift . lift . frequency $ fmap (fmap evalCustomGen) gens

--TODO: generate only in-scope variables
--TODO: make sure samples contain a healthy mix of all constructors.
--    Specifically, App seems very rare.
-- | Generate a random term, attempting to generate sensible values to make
--   generating well-typed terms more efficient and have a better distribution.
--   Uses 'CustomGen' to determine the currently bound variables, and the
--   desired maximum nesting level.
genTerm :: Enum v => TermGen v
genTerm = do
  nesting <- getNesting
  (v0, v) <- getV
  let vFreq = if fromEnum v0 == fromEnum v then const 0 else id
  freq [ (vFreq 5, genVar)
     , (nesting*10, genLam)
     , (nesting*5, genPi)
     , (nesting*10, genApp)
     , (1, genTy)
     , (nesting*2, genLet)
     , (nesting*2, genLetrec)
     ]

-- | Generate a random term, taking the desired maximum nesting level and
--   starting variable as arguments.
--   The variable enum should have enough successors to fulfil the maximum
--   nesting level.
generateTerm :: Enum v => Int -> v -> Gen (Term v)
generateTerm nesting v0 = fmap fst $ flip runStateT nesting $ fst <$> runStateT genTerm (v0, v0)

-- | Generate a random well-typed term. It will have the given nesting level
--   and the variables will be genereated starting from the given enum value.
genWellTyped' :: (Eq v, Show v, Enum v) => v -> Int -> Gen (Term v)
genWellTyped' v0 nesting = generateTerm nesting v0 `suchThat` \t -> wellTyped t && maxNesting t == nesting

-- | Generate a random well-typed term, starting variables with 'a' and with a
--   nesting level between 0 and 3.
genWellTyped = oneof $ genWellTyped' 'a' <$> [0..3]

instance (Eq v, Show v, Enum v) => Arbitrary (Term v) where
  arbitrary = genWellTyped' (toEnum 0) 3
