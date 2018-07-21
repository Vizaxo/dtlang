module Test.TypeCheck where

import Examples
import TypeCheck
import Types

import Data.Either
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

genUniverse :: Gen Int
genUniverse = frequency $ zip (halving 50) (fmap return [0..])

genTy :: Gen v -> Gen (Term v)
genTy genV = Ty <$> genUniverse

--TODO: generate only in-scope variables
--TODO: tweak these values
genTerm :: Gen v -> Gen (Term v)
genTerm genV = frequency $ fmap (fmap ($ genV)) [ (5, genVar)
                                                , (2, genLam)
                                                , (2, genPi)
                                                , (5, genApp)
                                                , (4, genTy)
                                                ]

genVInt :: Gen Int
genVInt = elements [0..9]

genWellTyped :: (Eq v, Show v) => Gen v -> Gen (Term v)
genWellTyped genV = genTerm genV `suchThat` wellTyped

testGenWellTyped
  = forAll (genWellTyped genVInt) $
    \prog -> isRight $ typeCheck [] prog

testIdPreservesType
  = forAll (genWellTyped genVInt) $
    \prog -> let (Right progT) = typeCheck [] prog
             in Right progT === typeCheck [] ((id' `App` progT) `App` prog)
