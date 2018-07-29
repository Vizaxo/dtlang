module Test.Generators where

import Term
import Test.BackTrackGen
import TypeCheck
import Utils

import Control.Monad
import Data.Maybe
import Test.QuickCheck

type GenTerm v = (Eq v, Show v, Enum v) => Term v -> Context v -> BackTrackGen (Term v)

genTargetTy :: GenTerm v
genTargetTy Ty _ = return (return Ty) --TODO: add pi
genTargetTy _  _ = return mzero

elements' [] = return mzero
elements' xs = elements xs

genTargetVar :: GenTerm v
genTargetVar target ctx = elements' $ return . Var . fst <$> filter (canUnify ctx target . snd) ctx

fresh ctx = toEnum $ 1 + (maximumOr (-1) $ (fromEnum . fst) <$> ctx)

--TODO: implement custom bind operator?
genTargetPi :: GenTerm v
genTargetPi Ty ctx = sized $ \size -> genTargetPi' size
  where
    genTargetPi' size | size <= 0 = return mzero
    genTargetPi' _ = do
      let v = fresh ctx
      genTarget Ty ctx >>= \case
        Nothing -> return mzero
        Just a -> genTarget Ty ((v,a):ctx) >>= \case
          Nothing -> return mzero
          Just b -> return $ return (Pi (v,a) b)
genTargetPi _ ctx = return mzero

--TODO: implement custom bind operator?
genTargetLam :: GenTerm v
genTargetLam (Pi (v,a) b) ctx = sized $ \size -> genTargetLam' size
  where
    genTargetLam' size | size <= 0 = return mzero
    genTargetLam' _ = do
      genTarget b ((v,a):ctx) >>= \case
        Nothing -> return mzero
        Just body -> return $ return (Lam (v,a) body)
genTargetLam _ ctx = return mzero

targetVariable :: GenTerm v
targetVariable (Var v) ctx = return $ lookup v ctx
targetVariable _ ctx = return mzero

pickGen xs target ctx = freqBacktrack $ ((mkGen <$>) <$>) xs
  where mkGen gen = scale (subtract 1) $ gen target ctx

--TODO: optimise picking of rules? Probably not needed (e.g. Var -> always targetVariable)
genTarget :: GenTerm v
genTarget = pickGen
           [ (2, genTargetTy)
           , (1, genTargetVar)
           , (3, genTargetPi)
           , (5, genTargetLam)
           , (1, targetVariable)
           ]
--TODO: add app rule
--TODO: add indir rule

genTermAndType :: forall v. (Eq v, Show v, Enum v) => Gen (Maybe (Term v, Term v))
genTermAndType = scale (+1) $ do
  scale ((+0) . (`div` 1)) $ genTarget @v Ty [] >>= \case
    Nothing -> return mzero
    --Not backtracking over a type that's been genTargetd... The type must be correct; can you always genTarget a term for it?
    Just ty -> ((,ty) <$>) <$> genTarget ty []

genTerm :: (Eq v, Show v, Enum v) => Gen (Term v)
genTerm = fst . fromJust <$> genTermAndType

prop_wellTyped = wellTyped @Int []

-- | A helper function for 'shrink' on 'Term's.
shrinkBinding :: (Eq v, Show v, Enum v) => (Binding v, Term v) -> [(Binding v, Term v)]
shrinkBinding ((v,vTy),val) = [((v,vTy'),val') | vTy' <- shrink vTy
                                               , val' <- shrink val]

noFreeVars :: (Eq v, Show v, Enum v) => Term v -> Bool
noFreeVars = null . freeVars

instance (Eq v, Show v, Enum v) => Arbitrary (Term v) where
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

-- TODO: Term vs WellTyped
-- | A 'WellTyped' is a 'Term' that is well-typed.
newtype WellTyped v = WellTyped (Term v)
  deriving (Eq, Show)

instance (Eq v, Show v, Enum v) => Arbitrary (WellTyped v) where
  arbitrary = WellTyped <$> genTerm

  shrink (WellTyped t) = WellTyped <$> shrink t
