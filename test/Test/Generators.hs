module Test.Generators where

import TypeCheck
import Types

import Test.QuickCheck

genVar :: Gen v -> Gen (Term v)
genVar = fmap Var

genBinding :: Gen v -> Gen (Binding v)
genBinding genV = (,) <$> genV <*> genTerm genV

genLam :: Gen v -> Gen (Term v)
genLam genV = Lam <$> genBinding genV <*> genTerm genV

genPi :: Gen v -> Gen (Term v)
genPi genV = Pi <$> genBinding genV <*> genTerm genV

genApp :: Gen v -> Gen (Term v)
genApp genV = App <$> genTerm genV <*> genTerm genV

halving :: Integral a => a -> [a]
halving 0 = [0]
halving start = start:halving(start `div` 2)

genTy :: Gen (Term v)
genTy = return Ty

--TODO: generate only in-scope variables
--TODO: tweak these values
genTerm :: Gen v -> Gen (Term v)
genTerm genV = frequency $ fmap (fmap ($ genV)) [ (5, genVar)
                                                , (2, genLam)
                                                , (2, genPi)
                                                , (5, genApp)
                                                , (4, const genTy)
                                                ]

genVInt :: Gen Int
genVInt = elements [0..9]

genWellTyped :: (Eq v, Show v) => Gen v -> Gen (Term v)
genWellTyped genV = genTerm genV `suchThat` wellTyped
