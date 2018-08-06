module Test.Generators where

import Equality
import Term
import Test.BackTrackGen
import TypeCheck
import Types
import Utils

import Control.Monad
import Control.Monad.Trans.Maybe
import Data.Maybe
import QuickCheck.GenT
import Test.QuickCheck (Arbitrary, arbitrary, shrink, Gen, shrinkList)

type GenTerm = Term -> Context -> BackTrackGen (Term)

genTargetTy :: GenTerm
genTargetTy Ty _ = return Ty
genTargetTy _  _ = mzero

elements' [] = mzero
elements' xs = elements xs

genTargetVar :: GenTerm
genTargetVar target ctx = elements' $ Var . fst <$> filter (isBetaEq target . snd) ctx

fresh ctx = toEnum $ 1 + (maximumOr (-1) $ (fromEnum . fst) <$> ctx)

--TODO: implement custom bind operator?
genTargetPi :: GenTerm
genTargetPi Ty ctx = sized $ \size -> genTargetPi' size
  where
    genTargetPi' size | size <= 0 = mzero
    genTargetPi' _ = do
      let v = fresh ctx
      a <- genTarget Ty ctx
      b <- genTarget Ty ((v,a):ctx)
      return (Pi (v,a) b)
genTargetPi _ ctx = mzero

--TODO: implement custom bind operator?
genTargetLam :: GenTerm
genTargetLam (Pi (v,a) b) ctx = sized $ \size -> genTargetLam' size
  where
    genTargetLam' size | size <= 0 = mzero
    genTargetLam' _ = do
      body <- genTarget b ((v,a):ctx)
      return (Lam (v,a) body)
genTargetLam _ ctx = mzero

pickGen xs target ctx = freqBacktrack $ ((mkGen <$>) <$>) xs
  where mkGen gen = scale (subtract 1) $ gen target ctx

--TODO: optimise picking of rules? Probably not needed (e.g. Var -> always targetVariable)
genTarget :: GenTerm
genTarget = pickGen
           [ (2, genTargetTy)
           , (1, genTargetVar)
           , (3, genTargetPi)
           , (5, genTargetLam)
           ]
--TODO: add app rule
--TODO: add indir rule

genTermAndType :: forall v. Gen (Maybe (Term, Term))
genTermAndType = scale (+1) . runBackTrackGen $ do
  ty <- genTarget Ty []
  --Not backtracking over a type that's been genTargetd... The type
  --must be correct; can you always genTarget a term for it?
  term <- genTarget ty []
  return (ty, term)

genTerm :: Gen (Term)
genTerm = fst . fromJust <$> genTermAndType

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
      shrink' Ty = []
      shrink' (Let rec bindings body) =
        [body] ++
        fmap snd bindings ++
        fmap (snd . fst) bindings ++
        [Let rec bindings' body' | bindings' <- shrinkList shrinkBinding bindings
                                 , body' <- shrink body]
      shrink' _ = []

-- TODO: Terms WellTyped
-- | A 'WellTyped' is a 'Term' that is well-typed.
newtype WellTyped = WellTyped Term
  deriving (Eq, Show)

instance Arbitrary WellTyped where
  arbitrary = WellTyped <$> genTerm

  shrink (WellTyped t) = WellTyped <$> shrink t

instance Arbitrary GenVar where
  arbitrary = GenVar <$> arbitrary

instance Arbitrary Name where
  arbitrary = oneof [Specified <$> arbitrary, Generated <$> arbitrary]

instance Arbitrary Type where
  arbitrary = scale (+1) $ Type . fromJust <$> runBackTrackGen (genTarget Ty [])
