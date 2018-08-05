module Main where

import Equality
import Term
import TC
import Types
import TypeCheck

import Test.BackTrackGen
import Test.DataTypes
import Test.Generators
import Test.Interpreter
import Test.TypeCheck

import Data.Either
import Test.Tasty
import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

main :: IO ()
main = defaultMain tests

--TODO: make benchmarking suite
genBenchmark :: IO ()
genBenchmark = sample $ resize 14 $ arbitrary @WellTyped

tests :: TestTree
tests = testGroup "Tests" [evaluator, typeChecker, dataTypes, equality, generator]

testTermProp name prop = testGroup name
  [ QC.testProperty "generated" prop
  , testGroup "regression" $ do testCase <- wellTypedRegression
                                return $ QC.testProperty (show testCase) (prop testCase)
  ]

evaluator :: TestTree
evaluator = testGroup "evaluator"
  [ testTermProp "id returns argument" prop_idReturnsArg
  , testTermProp "evaluating a well-typed to whnf always succeeds" prop_wellTypedWhnfSucceeds
  , testTermProp "fst $ pair a a == a" prop_pairFstReturnsArg
  , testTermProp "snd $ pair a a == a" prop_pairSndReturnsArg
  , testTermProp "eta expanding a term and applying it to an argument preserves value" prop_etaExpansion
  ]

typeChecker :: TestTree
typeChecker = testGroup "type checker"
  [ testTermProp "the type of the term is well-typed" prop_typeOfIsWellTyped
  , testTermProp "id preserves the argument's type" prop_idPreservesType
  , testTermProp "`fst $ pair a a` preserves a's type" prop_pairFstPreservesType
  , testTermProp "`snd $ pair a a` preserves a's type" prop_pairSndPreservesType
  , testTermProp "eta expanding a term and applying it to an argument preserves type" prop_etaExpansionType
  ]

dataTypes :: TestTree
dataTypes = testGroup "data types"
  [ testCase "duplicate constructors are disallowed" test_dupConstructorsDisallowed
  , testCase "a constructor with a return type that is not the datatype is disallowed" test_constructorNotReturnDataDisallowed
  ]

equality :: TestTree
equality = testGroup "equality"
  [ QC.testProperty "(λx:A.x) =α (λy:A.y)" prop_alphaEqId
  ]

generator :: TestTree
generator = testGroup "generator"
  [ testTermProp "a generated WellTyped is always well typed" prop_genWellTyped
  , QC.testProperty "generator backtracks properly" prop_backtracks
  ]

qcRegressionTests :: [Term]
qcRegressionTests
  = [ Lam ((toEnum 0),Ty) (Lam ((toEnum 1),Let Rec [(((toEnum 1),Ty),Var (toEnum 1))] (Var (toEnum 1))) (Lam ((toEnum 2),Var (toEnum 0)) (Var (toEnum 2))))
    , Lam ((toEnum 0),Let NoRec [] Ty) (Lam ((toEnum 1),Ty) (Var (toEnum 0)))
    , Lam ((toEnum 0),Let Rec [(((toEnum 0),Ty),Var (toEnum 0)),(((toEnum 1),Ty),Ty)] (Var (toEnum 1))) (Lam ((toEnum 1),Ty) (Var (toEnum 0)))
    , Lam ((toEnum 0),Ty) (Lam ((toEnum 1),Let Rec [(((toEnum 1),Var (toEnum 0)),Var (toEnum 1)),(((toEnum 2),Var (toEnum 0)),Var (toEnum 2))] (Var (toEnum 0))) (Lam ((toEnum 2),Var (toEnum 0)) Ty))
    , Lam ((toEnum 0),App (Lam ((toEnum 0),Ty) (Var (toEnum 0))) (Let Rec [(((toEnum 0),Ty),Var (toEnum 0)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 1))] (Var (toEnum 1)))) (Lam ((toEnum 1),Ty) (Lam ((toEnum 2),Ty) (Var (toEnum 2))))
    , Lam ((toEnum 0),App (Lam ((toEnum 0),Ty) (Var (toEnum 0))) (Let Rec [(((toEnum 0),Ty),Var (toEnum 1)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 0))] (Var (toEnum 1)))) (Lam ((toEnum 1),Ty) (Lam ((toEnum 2),Var (toEnum 1)) (Var (toEnum 1))))
    , Lam ((toEnum 0),Ty) (Lam ((toEnum 1),Let Rec [(((toEnum 1),Var (toEnum 0)),Var (toEnum 0))] (Var (toEnum 1))) (Pi ((toEnum 2),Ty) (Var (toEnum 2))))
    , Let NoRec [(((toEnum 1),Var (toEnum 0)),Pi ((toEnum 0),Ty) (Var (toEnum 0)))] (Var (toEnum 1))
    , Let Rec [(((toEnum 0),Ty),Var (toEnum 0)),(((toEnum 1),Lam ((toEnum 1),Var (toEnum 0)) (Var (toEnum 1))),Var (toEnum 1))] (Var (toEnum 1))
    , Let Rec [(((toEnum 0),Lam ((toEnum 0),Ty) (Var (toEnum 0))),Var (toEnum 1)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 1))] (Var (toEnum 0))
    , Let Rec [(((toEnum 0),Ty),Var (toEnum 0)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 0)),(((toEnum 2),Var (toEnum 0)),Var (toEnum 0))] (Var (toEnum 1))
    , App (Lam ((toEnum 0),Ty) (Var (toEnum 0))) Ty
    , Let NoRec [(((toEnum 0),Ty),Ty)] (Lam ((toEnum 1),Var (toEnum 0)) (Var (toEnum 0)))
    , Lam ((toEnum 0),App (Lam ((toEnum 0),Ty) (App (Lam ((toEnum 1),Var (toEnum 0)) (Let Rec [(((toEnum 2),Ty),Ty)] (Var (toEnum 1)))) (Var (toEnum 0)))) Ty) Ty
    ]

wellTypedRegression :: [WellTyped]
wellTypedRegression = WellTyped <$> terms ++ types
  where
    terms = filter (isRight . runTC . typeCheck) qcRegressionTests
    types = rights $ runTC . typeCheck <$> qcRegressionTests

qcGenerated :: [Term]
qcGenerated = [Let Rec [(((toEnum 0),Lam ((toEnum 0),Let Rec [] (App (App (App (Let NoRec [(((toEnum 1),Var (toEnum 0)),App (Pi ((toEnum 0),Lam ((toEnum 0),Pi ((toEnum 0),Let NoRec [(((toEnum 1),Var (toEnum 0)),Lam ((toEnum 0),App (Pi ((toEnum 0),App (Lam ((toEnum 0),Let NoRec [(((toEnum 1),Var (toEnum 0)),Lam ((toEnum 0),Ty) (Var (toEnum 0)))] (Var (toEnum 0))) (Var (toEnum 0))) (Pi ((toEnum 1),Var (toEnum 0)) (Var (toEnum 0)))) Ty) (Var (toEnum 0))) (Var (toEnum 0)))] (Lam ((toEnum 2),Ty) (Var (toEnum 1)))) (Var (toEnum 0))) (App (Var (toEnum 0)) (Var (toEnum 0)))) (Var (toEnum 0))) (App (Var (toEnum 0)) (Var (toEnum 0)))),(((toEnum 2),App (Lam ((toEnum 2),App (Let NoRec [] (Var (toEnum 0))) (Var (toEnum 0))) (Var (toEnum 2))) (Var (toEnum 2))),Var (toEnum 0))] (Var (toEnum 0))) (Var (toEnum 2))) (Var (toEnum 0))) (Lam ((toEnum 3),Var (toEnum 2)) (Var (toEnum 2))))) (Var (toEnum 0))),Var (toEnum 0))] (Var (toEnum 0))
              ]
