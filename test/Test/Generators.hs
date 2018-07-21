module Test.Generators where

import TypeCheck
import Term

import Control.Monad.State
import Data.Either
import QuickCheck.GenT
import Test.QuickCheck hiding (suchThat, elements, frequency, sized)


-- | The starting variable, and the next fresh variable to use.
type BoundV v = (v, v)

-- | The monad transformer stack for generation of values that rely on the
--   state of bound variables.
--   This alows the generators to be much more likely to generate
--   well-typed terms, and to generate more deeply nested terms.
type CustomGen v a = GenT (State (BoundV v)) a
type TermGen v = CustomGen v (Term v)

-- | Helper function for getting the current state of bound variables.
getV :: CustomGen v (v,v)
getV = lift get

-- | Eval a given state transformer with the starting state. This is useful for
--   chaining evaluations of StateT, keeping the starting state adjacent to the
--   call of eval for each layer.
evalState' :: s -> State s a -> a
evalState' = flip evalState

genExistingVar :: Enum v => CustomGen v v
genExistingVar = do
  (v0, vmax) <- getV
  elements [v0..pred vmax]

-- | Generate a fresh variable with a generated type, and use it as a binding.
genNewBinding :: Enum v => CustomGen v (Binding v)
genNewBinding= do
  (v0, v) <- getV
  ty <- genTerm
  lift $ put (v0, succ v)
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
  numBindings <- elements $ [0..3]
  --Must do this first, so that the new variables are in scope for the other bodies
  --Generate bindings first so they can be used in the terms
  bindings <- replicateM numBindings genNewBinding
  terms <- replicateM numBindings genTerm
  body <- genTerm
  return $ Let Rec (zip bindings terms) body

genLet :: Enum v => TermGen v
genLet = do
  numBindings <- elements $ [0..3]
  --Generate bindings second so they can't be used in the terms
  terms <- replicateM numBindings genTerm
  bindings <- replicateM numBindings genNewBinding
  body <- genTerm
  return $ Let NoRec (zip bindings terms) body

--TODO: handle state passing better
--TODO: generate only in-scope variables
--TODO: make sure samples contain a healthy mix of all constructors.
--    Specifically, App seems very rare.
-- | Generate a random term, attempting to generate sensible values to make
--   generating well-typed terms more efficient and have a better distribution.
--   Uses 'CustomGen' to determine the currently bound variables.
genTerm :: Enum v => TermGen v
genTerm = sized $ \size -> do
  (v0, v) <- getV
  let vFreq = if fromEnum v0 == fromEnum v then const 0 else id
  frequency [ (vFreq 10000, genVar)
            , (size*20, genLam)
            , (size*2, genPi)
            , (size*10, genApp)
            , (300, genTy)
            , (size*1, genLet)
            , (size*1, genLetrec)
            ]

runCustomGen v0 gen = evalState' (v0,v0) <$> runGenT gen

-- | Generate a random term, taking the starting variable as an argument.
--   The variable enum should be able to produce a large number of results;
--   for example 'Int' or 'Char'.
generateTerm :: Enum v => v -> Gen (Term v)
generateTerm v0 = evalState' (v0, v0) <$> runGenT genTerm

-- | Generate a random well-typed term. The variables will be genereated
--   starting from the given enum value.
genWellTyped' :: (Eq v, Show v, Enum v) => v -> Gen (Term v)
genWellTyped' v0 = sized $ \size -> generateTerm v0 `suchThat` \t -> wellTyped t

-- | Generate a random well-typed term, starting variables with 'a'.
genWellTyped = genWellTyped' 'a'

instance (Eq v, Show v, Enum v) => Arbitrary (Term v) where
  arbitrary = genWellTyped' (toEnum 0)

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
  arbitrary = WellTyped <$> genWellTyped' (toEnum 0)

  shrink (WellTyped t) = WellTyped <$> (rights $ typeCheck [] <$> shrink t)
