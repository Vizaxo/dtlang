module Test.Generators where

import Equality
import Term
import Test.BackTrackGen
import TC hiding (fresh)
import TypeCheck
import Types
import Utils

import Control.Lens hiding (Context, elements)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.Natural hiding (view)
import QuickCheck.GenT
import Test.QuickCheck (Arbitrary, arbitrary, shrink, Gen)

type GenTerm = Term -> Context -> [Name] -> BackTrackGen Term

genTargetTy :: GenTerm
genTargetTy (Ty 0) _ _ = mzero
genTargetTy (Ty n) _ _ = sized $ \size -> if size < (-1) then mzero else return (Ty (n-1))
genTargetTy _  _ _ = mzero

genTargetDataType :: GenTerm
genTargetDataType target ctx _ = elements' $ map (Var . name) $ filter (isBetaEq ctx target . ty) (datatypes ctx)

elements' [] = mzero
elements' xs = elements xs

genTargetVar :: GenTerm
genTargetVar target ctx _ = sized $ \size -> if size < (-1)
  then mzero
  else elements' $ Var . fst <$> filter (isBetaEq ctx target . snd) (getCtx ctx)

fresh :: Context -> [Name] -> Name
fresh ctx avoid = toEnum $ 1 + (maximumOr (-1) $ fromEnum <$> (fst <$> getCtx ctx) ++ avoid)

prop_GenFreshIsFresh :: Context -> [Name] -> Bool
prop_GenFreshIsFresh ctx avoid =
  let v = fresh ctx avoid
  in not (elem v ((fst <$> getCtx ctx) ++ avoid))

genTargetPi :: GenTerm
genTargetPi (Ty n) ctx avoid = sized $ \size -> genTargetPi' size
  where
    genTargetPi' size | size <= 0 = mzero
    genTargetPi' _ = do
      let v = fresh ctx avoid
      (m,p) <- lift (arbitrary @Ordering) >>= \case
        EQ -> return (n,n)
        LT -> (,n) <$> genLeq n
        GT -> (n,) <$> genLeq n
      a <- genTarget (Ty m) ctx (v:avoid)
      b <- genTarget (Ty p) (insertCtx v a ctx) (v:avoid)
      return (Pi (v,a) b)

    genLeq :: (Enum n, Num n) => n -> MaybeT Gen n
    genLeq n = elements' [0..n]
genTargetPi _ ctx _ = mzero

genTargetLam :: GenTerm
genTargetLam (Pi (v,a) b) ctx avoid = sized $ \size -> genTargetLam' size
  where
    genTargetLam' size | size <= 0 = mzero
    genTargetLam' _ = do
      body <- genTarget b (insertCtx v a ctx) (v:avoid)
      return (Lam (v,a) body)
genTargetLam _ ctx _ = mzero

genTargetApp :: GenTerm
genTargetApp target ctx avoid = sized $ \size -> genTargetApp' (min size 3)
  where
    genTargetApp' size
      | size <= 0 = mzero
      | otherwise = do
          argTy <- maxSize 2 $ genTarget (Ty 0) ctx avoid
          let x = fresh ctx (avoid ++ allVars argTy ++ allVars target)
          --TODO: how do we handle substitution?
          a <- genTarget (Pi (x,argTy) target) ctx (x:avoid)
          assert (not $ elem x (freeVars a)) "x used in a"
          b <- genTarget argTy ctx (x:avoid)
          assert (not $ elem x (freeVars b)) "x used in b"
          return (App a b)
    maxSize s g = scale (`min` s) g

pickGen xs target ctx avoid = do
  target' <- case runTC ctx $ whnf target of
    Left e -> error $ "whnf failed during generation: " <> show e <> "in the context " <> show ctx <> "\nWhen trying to whnf " <> show target
    Right t -> return t
  assertRight (runTC ctx (isType target')) "target is not a type"
  res <- freqBacktrack $ ((mkGen target' <$>) <$>) (filter ((/= 0) . view _1) xs)
  assertRight
    (runTC ctx (hasType res target'))
    $  "generated term doesn't have target type:\n"
    <> "the term\n"
    <> show res <> "\n"
    <> "should have type\n"
    <> show target' <> "\n"
  return res

  where mkGen tgt gen = scale (subtract 1) $ gen tgt ctx avoid

genTarget :: GenTerm
genTarget target ctx avoid = do
  res <- pickGen
           [ (20, genTargetTy)
           , (10, genTargetVar)
           , (30, genTargetPi)
           , (50, genTargetLam)
           , (30, genTargetDataType)
           , (0, genTargetApp)
           ] target ctx avoid
  --TODO: add indir rule
  unless (wellTyped ctx res)
    (error ("Generated term is not well-typed:" <> show res))
  return res

genTermAndType :: Gen (Term, Term)
genTermAndType = scale (+1) . backtrackUntilSuccess $ do
  n <- freqBacktrack $ zip
         (takeWhile (/= 0) $ iterate (`div` 4) (4^1)) --Frequencies
         (return <$> [1..])                           --Type universes
  ty <- scale (`div` 10) $ genTarget (Ty n) emptyCtx []
  term <- scale (`div` 5) $ genTarget ty emptyCtx []
  return (term, ty)

--TODO: run exhaustive search, don't just keep generating the same terms forever
backtrackUntilSuccess :: BackTrackGen a -> Gen a
backtrackUntilSuccess gen = do
  runBackTrackGen gen >>= \case
    Nothing -> backtrackUntilSuccess gen
    Just x -> return x

genTerm :: Gen Term
genTerm = fst <$> genTermAndType

-- | Generate a term whose type is of the given universe level
atUniverseLevel :: Natural -> Context -> Gen Term
atUniverseLevel u ctx = scale (+1) . backtrackUntilSuccess $ do
  -- TODO: don't use max here; should be able to properly backtrack over generation of the type
  ty <- scale (max 2 . (`div` 20)) $ genTarget (Ty u) ctx []
  term <- scale (max 2 . (`div` 10)) $ genTarget ty ctx []
  unless (wellTyped ctx ty)
    (error ("atUniverseLevel: Generated type is not well-typed:" <> show ty))
  unless (wellTyped ctx term)
    (error ("atUniverseLevel: Generated term is not well-typed:" <> show term))
  return term

genTermAtCtx :: Term -> Context -> Gen (Maybe Term)
genTermAtCtx ty ctx = scale (max 2 . (`div` 10)) $ runBackTrackGen (genTarget ty ctx [])

genTermAt :: Term -> Gen (Maybe Term)
genTermAt ty = runBackTrackGen (genTarget ty emptyCtx [])

prop_wellTyped :: Context -> Term -> Bool
prop_wellTyped = wellTyped

-- | A helper function for 'shrink' on 'Term's.
shrinkBinding :: (Binding, Term) -> [(Binding, Term)]
shrinkBinding ((v,vTy),val) = [((v,vTy'),val') | vTy' <- shrink vTy
                                               , val' <- shrink val]

noFreeVars :: Term -> Bool
noFreeVars = null . freeVars

instance Arbitrary (Term) where
  arbitrary = genTerm

  shrink = filter (noFreeVars) . shrink'
    where
      shrink' (Var v) = []
      shrink' (Lam (x,xTy) body) = [body, xTy] ++
                                  [Lam (x,xTy') body' | (body', xTy') <- shrink (body, xTy)]
      shrink' (Pi (x,xTy) ret) = [ret, xTy] ++
                                [Pi (x,xTy') ret' | (ret', xTy') <- shrink (ret, xTy)]
      shrink' (App a b) = [a, b] ++
                         [App a' b' | (a',b') <- shrink (a,b)]
      shrink' (Ty n) = []
      shrink' _ = []

-- | A 'WellTyped' is a 'Term' that is well-typed.
newtype WellTyped = WellTyped Term
  deriving (Eq, Show)

instance Arbitrary WellTyped where
  arbitrary = WellTyped <$> genTerm

  shrink (WellTyped t) = WellTyped <$> shrink t

instance Arbitrary GenVar where
  arbitrary = GenVar <$> arbitrary

instance Arbitrary Name where
  arbitrary = oneof [Specified <$> arbitrary, Generated "arbitrary" <$> arbitrary]

instance Arbitrary Context where
  --TODO: arbitrary data declarations
  arbitrary = Context <$> arbitrary <*> arbitrary <*> pure []
