module Test.Generators where

import TypeCheck
import Types

import Control.Monad.State
import Test.QuickCheck

type CustomGen v a = StateT (v, v) (StateT Int Gen) a
type TermGen v = CustomGen v (Term v)

genVar :: Enum v => TermGen v
genVar = Var <$> genExistingVar

genExistingVar :: Enum v => CustomGen v v
genExistingVar = do
  (v0, vmax) <- get
  lift $ lift $ elements [v0..pred vmax]


genNewBinding :: Enum v => CustomGen v (Binding v)
genNewBinding= do
  (v0, v) <- get
  ty <- genTerm
  put $ (v0, succ v)
  return (v, ty)

genLam :: Enum v => TermGen v
genLam = Lam <$> genNewBinding <*> genTerm

genPi :: Enum v => TermGen v
genPi = Pi <$> genNewBinding <*> genTerm

genApp :: Enum v => TermGen v
genApp = App <$> genTerm <*> genTerm

halving :: Integral a => a -> [a]
halving 0 = [0]
halving start = start:halving(start `div` 2)

genTy :: TermGen v
genTy = return Ty

--TODO: handle state passing better
freq :: [(Int, CustomGen v a)] -> CustomGen v a
freq gens = do
  nesting <- lift get
  v <- get
  let evalCustomGen = evalStateT' (nesting - 1) . evalStateT' v
  lift . lift . frequency $ fmap (fmap evalCustomGen) gens

evalStateT' :: Monad m => s -> StateT s m a -> m a
evalStateT' = flip evalStateT

--TODO: generate only in-scope variables
--TODO: make sure samples contain a healthy mix of all constructors.
--    Specifically, App seems very rare.
genTerm :: Enum v => TermGen v
genTerm = do
  nesting <- lift get
  (v0, v) <- get
  let vFreq = if fromEnum v0 == fromEnum v then const 0 else id
  freq [ (vFreq 5, genVar)
     , (nesting*10, genLam)
     , (nesting*5, genPi)
     , (nesting*10, genApp)
     , (1, genTy)
     ]

generateTerm :: Enum v => Int -> v -> Gen (Term v)
generateTerm nesting v0 = fmap fst $ flip runStateT nesting $ fst <$> runStateT genTerm (v0, v0)

-- | Generate a random well-typed term. It will have a maximum nesting
--  level of 'nesting', and the variables will be genereated starting
--  from 'v0'.
genWellTyped' :: (Eq v, Show v, Enum v) => v -> Int -> Gen (Term v)
genWellTyped' v0 nesting = generateTerm nesting v0 `suchThat` \t -> wellTyped t && maxNesting t == nesting

genWellTyped = oneof $ genWellTyped' 'a' <$> [0..3]
