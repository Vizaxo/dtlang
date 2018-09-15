module Main where

import Equality
import Examples
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
import Data.Maybe
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

main :: IO ()
main = defaultMain tests

defaultCtx' :: Context
defaultCtx' = either
  (\e -> error ("Type checking default context failed: " <> show e))
  id
  defaultCtx

--TODO: make benchmarking suite
genBenchmark :: IO ()
genBenchmark = sample $ resize 14 $ arbitrary @WellTyped

tests :: TestTree
tests = testGroup "Tests" [evaluator, typeChecker, dataTypes, equality, generator]

testTermProp name prop = testGroup name
  --TODO: generate terms at other universe levels?
  [ QC.testProperty "generated" $ forAll (WellTyped <$> atUniverseLevel 0 defaultCtx') prop
  {-
  --TODO: fix regression test universe levels
  , testGroup "regression" $ do
      testCase <- wellTypedRegression
      return $ QC.testProperty (take 30 (show testCase) <> "...") (prop testCase)
  -}
  ]

testTyProp :: Testable p => String -> (Type -> p) -> TestTree
testTyProp name prop = QC.testProperty name (forAll (fromJust <$> genTermAtCtx (Ty 0) defaultCtx') prop)

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
  [ testTermProp "the type of the term is well-typed" (prop_typeOfIsWellTyped defaultCtx')
  , testTermProp "id preserves the argument's type" (prop_idPreservesType defaultCtx')
  , testTermProp "`fst $ pair a a` preserves a's type" (prop_pairFstPreservesType defaultCtx')
  , testTermProp "`snd $ pair a a` preserves a's type" (prop_pairSndPreservesType defaultCtx')
  , testTermProp "eta expanding a term and applying it to an argument preserves type" (prop_etaExpansionType defaultCtx')
  ]

dataTypes :: TestTree
dataTypes = testGroup "data types"
  [ testCase "duplicate constructors are disallowed" test_dupConstructorsDisallowed
  , testCase "a constructor with a return type that is not the datatype is disallowed" test_constructorNotReturnDataDisallowed
  , testCase "a constructor can't access the type variables defined in the data type declaration" test_constructorReferenceVarInData
  , testCase "Nat is well-typed" test_nat
  , testCase "List is well-typed" test_list
  , testCase "Vect is well-typed" test_vect
  , testCase "a constructor can't access variables defined in another constructor" test_constructorReferenceVarInOtherConstructor
  , testCase "partiallyApplyCtor properly converts Zero" test_partiallyApplyCtorZero
  , testCase "partiallyApplyCtor properly converts Succ" test_partiallyApplyCtorSucc
  , testCase "pattern matching on natural numbers type-checks" test_patternMatchNatTypeCheck
  , testCase "pattern matching on zero evaluates correctly" test_patternMatchNatWhnfZero
  , testCase "pattern matching on succ evaluates correctly" test_patternMatchNatWhnfOne
  , testCase "bad versions of sigma don't type check" test_badSigmasFailTC
  , testCase "sigma type checks" test_sigmaTypeChecks
  , testCase "void type checks" test_voidTypeChecks
  ]

equality :: TestTree
equality = testGroup "equality"
  [ testTyProp "(λx:A.x) =α (λy:A.y)" prop_eqIdAlpha
  , testTyProp "(λx:A.x) =β (λy:A.y)" prop_eqIdBeta
  , testTyProp "fst =/α= snd" prop_fstNotSndAlpha
  , testTyProp "fst =/β= snd" prop_fstNotSndBeta
  , testTyProp "typeof fst =/α= typeof snd" prop_fstNotSndTyAlpha
  , testTyProp "typeof fst =/β= typeof snd" prop_fstNotSndTyBeta
  ]

generator :: TestTree
generator = testGroup "generator"
  [ testTermProp "a generated WellTyped is always well typed" (prop_genWellTyped defaultCtx')
  , QC.testProperty "generator backtracks properly" prop_backtracks
  ]

tc :: TestTree
tc = testGroup "tc"
  [ QC.testProperty "fresh generates fresh variables" prop_freshIsFresh
  ]

qcRegressionTests :: [Term]
qcRegressionTests
  = [ Lam ((toEnum 0),(Ty 0)) (Lam ((toEnum 1),Let Rec [(((toEnum 1),(Ty 0)),Var (toEnum 1))] (Var (toEnum 1))) (Lam ((toEnum 2),Var (toEnum 0)) (Var (toEnum 2))))
    , Lam ((toEnum 0),Let NoRec [] (Ty 0)) (Lam ((toEnum 1),(Ty 0)) (Var (toEnum 0)))
    , Lam ((toEnum 0),Let Rec [(((toEnum 0),(Ty 0)),Var (toEnum 0)),(((toEnum 1),(Ty 0)),(Ty 0))] (Var (toEnum 1))) (Lam ((toEnum 1),(Ty 0)) (Var (toEnum 0)))
    , Lam ((toEnum 0),(Ty 0)) (Lam ((toEnum 1),Let Rec [(((toEnum 1),Var (toEnum 0)),Var (toEnum 1)),(((toEnum 2),Var (toEnum 0)),Var (toEnum 2))] (Var (toEnum 0))) (Lam ((toEnum 2),Var (toEnum 0)) (Ty 0)))
    , Lam ((toEnum 0),App (Lam ((toEnum 0),(Ty 0)) (Var (toEnum 0))) (Let Rec [(((toEnum 0),(Ty 0)),Var (toEnum 0)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 1))] (Var (toEnum 1)))) (Lam ((toEnum 1),(Ty 0)) (Lam ((toEnum 2),(Ty 0)) (Var (toEnum 2))))
    , Lam ((toEnum 0),App (Lam ((toEnum 0),(Ty 0)) (Var (toEnum 0))) (Let Rec [(((toEnum 0),(Ty 0)),Var (toEnum 1)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 0))] (Var (toEnum 1)))) (Lam ((toEnum 1),(Ty 0)) (Lam ((toEnum 2),Var (toEnum 1)) (Var (toEnum 1))))
    , Lam ((toEnum 0),(Ty 0)) (Lam ((toEnum 1),Let Rec [(((toEnum 1),Var (toEnum 0)),Var (toEnum 0))] (Var (toEnum 1))) (Pi ((toEnum 2),(Ty 0)) (Var (toEnum 2))))
    , Let NoRec [(((toEnum 1),Var (toEnum 0)),Pi ((toEnum 0),(Ty 0)) (Var (toEnum 0)))] (Var (toEnum 1))
    , Let Rec [(((toEnum 0),(Ty 0)),Var (toEnum 0)),(((toEnum 1),Lam ((toEnum 1),Var (toEnum 0)) (Var (toEnum 1))),Var (toEnum 1))] (Var (toEnum 1))
    , Let Rec [(((toEnum 0),Lam ((toEnum 0),(Ty 0)) (Var (toEnum 0))),Var (toEnum 1)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 1))] (Var (toEnum 0))
    , Let Rec [(((toEnum 0),(Ty 0)),Var (toEnum 0)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 0)),(((toEnum 2),Var (toEnum 0)),Var (toEnum 0))] (Var (toEnum 1))
    , App (Lam ((toEnum 0),(Ty 0)) (Var (toEnum 0))) (Ty 0)
    , Let NoRec [(((toEnum 0),(Ty 0)),(Ty 0))] (Lam ((toEnum 1),Var (toEnum 0)) (Var (toEnum 0)))
    , Lam ((toEnum 0),App (Lam ((toEnum 0),(Ty 0)) (App (Lam ((toEnum 1),Var (toEnum 0)) (Let Rec [(((toEnum 2),(Ty 0)),(Ty 0))] (Var (toEnum 1)))) (Var (toEnum 0)))) (Ty 0)) (Ty 0)
    , App (App (App (App (Lam (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),(Ty 0)) (Var (Generated (GenVar 0)))) (Pi (Generated (GenVar 1),(Ty 0)) (Pi (Generated (GenVar 2),App (Lam (Generated (GenVar 2),(Ty 0)) (Pi (Generated (GenVar 3),Var (Generated (GenVar 1))) (Pi (Generated (GenVar 4),(Ty 0)) (Var (Generated (GenVar 4)))))) (Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),(Ty 0)) (Var (Generated (GenVar 0)))) (Ty 0)) (Pi (Generated (GenVar 1),Pi (Generated (GenVar 1),(Ty 0)) (Var (Generated (GenVar 1)))) (Pi (Generated (GenVar 2),(Ty 0)) (Ty 0)))) (Ty 0)) (Pi (Generated (GenVar 1),Pi (Generated (GenVar 1),Pi (Generated (GenVar 1),(Ty 0)) (Ty 0)) (Pi (Generated (GenVar 2),(Ty 0)) (Ty 0))) (Ty 0)))) (Pi (Generated (GenVar 3),Var (Generated (GenVar 1))) (Ty 0))))) (Lam (Generated (GenVar 0),Pi (Generated (GenVar 0),(Ty 0)) (Ty 0)) (App (Lam (Generated (GenVar 1),Pi (Generated (GenVar 1),(Ty 0)) (Var (Generated (GenVar 1)))) (Lam (Generated (GenVar 0),(Ty 0)) (Lam (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),(Ty 0)) (Pi (Generated (GenVar 1),(Ty 0)) (Ty 0))) (Pi (Generated (GenVar 1),Pi (Generated (GenVar 1),(Ty 0)) (Var (Generated (GenVar 1)))) (Pi (Generated (GenVar 2),(Ty 0)) (Ty 0)))) (Ty 0)) (Var (Generated (GenVar 1)))))) (Lam (Generated (GenVar 1),(Ty 0)) (Ty 0))))) (Lam (Generated (GenVar 0),Pi (Generated (GenVar 0),(Ty 0)) (Var (Generated (GenVar 0)))) (Lam (Generated (GenVar 1),(Ty 0)) (Lam (Generated (GenVar 2),App (Lam (Generated (GenVar 2),(Ty 0)) (Pi (Generated (GenVar 3),Var (Generated (GenVar 1))) (Pi (Generated (GenVar 4),(Ty 0)) (Var (Generated (GenVar 4)))))) (Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),(Ty 0)) (Var (Generated (GenVar 0)))) (Ty 0)) (Pi (Generated (GenVar 1),Pi (Generated (GenVar 1),(Ty 0)) (Var (Generated (GenVar 1)))) (Pi (Generated (GenVar 2),(Ty 0)) (Ty 0)))) (Ty 0)) (Pi (Generated (GenVar 1),Pi (Generated (GenVar 1),Pi (Generated (GenVar 1),(Ty 0)) (Ty 0)) (Pi (Generated (GenVar 2),(Ty 0)) (Ty 0))) (Ty 0)))) (Lam (Generated (GenVar 3),Var (Generated (GenVar 1))) (Pi (Generated (GenVar 4),Pi (Generated (GenVar 4),(Ty 0)) (Ty 0)) (Ty 0))))))) (Lam (Generated (GenVar 0),(Ty 0)) (Pi (Generated (GenVar 1),(Ty 0)) (Pi (Generated (GenVar 2),Pi (Generated (GenVar 2),Pi (Generated (GenVar 2),Pi (Generated (GenVar 2),Pi (Generated (GenVar 2),(Ty 0)) (Pi (Generated (GenVar 3),Pi (Generated (GenVar 3),Pi (Generated (GenVar 3),(Ty 0)) (Ty 0)) (Pi (Generated (GenVar 4),(Ty 0)) (Var (Generated (GenVar 1))))) (Ty 0))) (Pi (Generated (GenVar 3),Pi (Generated (GenVar 3),Pi (Generated (GenVar 3),Pi (Generated (GenVar 3),(Ty 0)) (Ty 0)) (Var (Generated (GenVar 0)))) (Ty 0)) (Pi (Generated (GenVar 4),Pi (Generated (GenVar 4),(Ty 0)) (Pi (Generated (GenVar 5),Var (Generated (GenVar 4))) (Ty 0))) (Pi (Generated (GenVar 5),Pi (Generated (GenVar 5),(Ty 0)) (Var (Generated (GenVar 1)))) (Pi (Generated (GenVar 6),Var (Generated (GenVar 0))) (Ty 0)))))) (Ty 0)) (Pi (Generated (GenVar 3),Pi (Generated (GenVar 3),(Ty 0)) (Ty 0)) (Var (Generated (GenVar 0))))) (Var (Generated (GenVar 0))))))) (Ty 0)) (Lam (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),(Ty 0)) (Pi (Generated (GenVar 1),(Ty 0)) (Ty 0))) (Pi (Generated (GenVar 1),Pi (Generated (GenVar 1),(Ty 0)) (Var (Generated (GenVar 1)))) (Pi (Generated (GenVar 2),(Ty 0)) (Ty 0)))) (Pi (Generated (GenVar 1),(Ty 0)) (Pi (Generated (GenVar 2),Pi (Generated (GenVar 2),(Ty 0)) (Pi (Generated (GenVar 3),Pi (Generated (GenVar 3),(Ty 0)) (Ty 0)) (Pi (Generated (GenVar 4),Pi (Generated (GenVar 4),(Ty 0)) (Var (Generated (GenVar 4)))) (Ty 0)))) (Pi (Generated (GenVar 3),Pi (Generated (GenVar 3),Var (Generated (GenVar 1))) (Var (Generated (GenVar 1)))) (Ty 0)))))
    , App (Lam (Generated (GenVar 0),(Ty 0)) (Lam (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),(Ty 0)) (Ty 0)) (Pi (Generated (GenVar 1),(Ty 0)) (Ty 0))) (Lam (Generated (GenVar 1),(Ty 0)) (Pi (Generated (GenVar 2),Var (Generated (GenVar 1))) (Var (Generated (GenVar 1))))))) (Lam (Generated (GenVar 0),Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),(Ty 0)) (Ty 0)) (Pi (Generated (GenVar 1),(Ty 0)) (Ty 0))) (Lam (Generated (GenVar 1),(Ty 0)) (Pi (Generated (GenVar 2),Var (Generated (GenVar 1))) (Pi (Generated (GenVar 3),Var (Generated (GenVar 1))) (Pi (Generated (GenVar 4),(Ty 0)) (Pi (Generated (GenVar 5),(Ty 0)) (Ty 0)))))))
    , App (Ty 0) (Ty 0)
    , Pi (Generated (GenVar 0),Pi (Generated (GenVar 0),(Ty 0)) (App (Lam (Generated (GenVar 1),(Ty 0)) (Pi (Generated (GenVar 2),(Ty 0)) (Ty 0))) (Pi (Generated (GenVar 0),(Ty 0)) (Var (Generated (GenVar 0)))))) (Pi (Generated (GenVar 1),Pi (Generated (GenVar 1),App (Lam (Generated (GenVar 1),Pi (Generated (GenVar 1),Pi (Generated (GenVar 1),(Ty 0)) (Pi (Generated (GenVar 2),Pi (Generated (GenVar 2),(Ty 0)) (Var (Generated (GenVar 1)))) (Var (Generated (GenVar 1))))) (Ty 0)) (Ty 0)) (Lam (Generated (GenVar 1),Pi (Generated (GenVar 1),(Ty 0)) (Pi (Generated (GenVar 2),Pi (Generated (GenVar 2),(Ty 0)) (Var (Generated (GenVar 1)))) (Var (Generated (GenVar 1))))) (App (Lam (Generated (GenVar 2),Pi (Generated (GenVar 2),Pi (Generated (GenVar 2),(Ty 0)) (Ty 0)) (Pi (Generated (GenVar 3),(Ty 0)) (Ty 0))) (Pi (Generated (GenVar 3),(Ty 0)) (Ty 0))) (Lam (Generated (GenVar 2),Pi (Generated (GenVar 2),(Ty 0)) (Ty 0)) (Lam (Generated (GenVar 3),(Ty 0)) (Ty 0)))))) (Pi (Generated (GenVar 2),(Ty 0)) (Pi (Generated (GenVar 3),Pi (Generated (GenVar 3),Pi (Generated (GenVar 3),(Ty 0)) (Var (Generated (GenVar 2)))) (Pi (Generated (GenVar 4),Var (Generated (GenVar 1))) (Pi (Generated (GenVar 5),Var (Generated (GenVar 1))) (Ty 0)))) (Pi (Generated (GenVar 4),Pi (Generated (GenVar 4),Pi (Generated (GenVar 4),(Ty 0)) (Var (Generated (GenVar 4)))) (Ty 0)) (Pi (Generated (GenVar 5),Var (Generated (GenVar 1))) (Ty 0)))))) (Pi (Generated (GenVar 2),(Ty 0)) (Var (Generated (GenVar 2)))))
    ]

wellTypedRegression :: [WellTyped]
wellTypedRegression = WellTyped <$> terms ++ types
  where
    terms = filter (isRight . runTC . typeCheck) qcRegressionTests
    types = rights $ runTC . typeCheck <$> qcRegressionTests

qcGenerated :: [Term]
qcGenerated = [Let Rec [(((toEnum 0),Lam ((toEnum 0),Let Rec [] (App (App (App (Let NoRec [(((toEnum 1),Var (toEnum 0)),App (Pi ((toEnum 0),Lam ((toEnum 0),Pi ((toEnum 0),Let NoRec [(((toEnum 1),Var (toEnum 0)),Lam ((toEnum 0),App (Pi ((toEnum 0),App (Lam ((toEnum 0),Let NoRec [(((toEnum 1),Var (toEnum 0)),Lam ((toEnum 0),(Ty 0)) (Var (toEnum 0)))] (Var (toEnum 0))) (Var (toEnum 0))) (Pi ((toEnum 1),Var (toEnum 0)) (Var (toEnum 0)))) (Ty 0)) (Var (toEnum 0))) (Var (toEnum 0)))] (Lam ((toEnum 2),(Ty 0)) (Var (toEnum 1)))) (Var (toEnum 0))) (App (Var (toEnum 0)) (Var (toEnum 0)))) (Var (toEnum 0))) (App (Var (toEnum 0)) (Var (toEnum 0)))),(((toEnum 2),App (Lam ((toEnum 2),App (Let NoRec [] (Var (toEnum 0))) (Var (toEnum 0))) (Var (toEnum 2))) (Var (toEnum 2))),Var (toEnum 0))] (Var (toEnum 0))) (Var (toEnum 2))) (Var (toEnum 0))) (Lam ((toEnum 3),Var (toEnum 2)) (Var (toEnum 2))))) (Var (toEnum 0))),Var (toEnum 0))] (Var (toEnum 0))
              ]
