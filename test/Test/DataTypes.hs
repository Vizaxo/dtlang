module Test.DataTypes where

import Equality
import Examples
import TC
import Types
import TypeCheck

import Data.Either
import Data.Map (singleton, fromList)
import Test.Tasty.HUnit

test_constructorNotReturnDataDisallowed = assertLeft $ runTC emptyCtx $ typeCheckData badConstructorType

badConstructorType :: DataDecl
badConstructorType =
  DataDecl
  (Specified "data")
  (Ty 0)
  (singleton (Specified "invalidTypeConstructor") (Ty 0))

badVarReference :: DataDecl
badVarReference =
  DataDecl
  (Specified "Vect")
  (Pi (Specified "a", (Ty 0)) (Pi (Specified "n", Var (Specified "Nat")) (Ty 0)))
   -- VNil : Vect 0 a
  (fromList
   [(Specified "VNil",
      Pi (Specified "a", (Ty 0)) $
       (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` (Var (Specified "Zero")))
   -- VCons : (a:(Ty 0)) -> (x:a) -> (n:Nat) -> (xs:Vect a n) -> Vect a (S n)
   ,(Specified "VCons",
      Pi (Specified "a",(Ty 0)) $
       Pi (Specified "x",Var (Specified "a")) $
        Pi (Specified "xs",App (Var (Specified "List")) (Var (Specified "a"))) $
         (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` ((Var (Specified "Succ")) `App` (Var (Specified "n"))))])

test_constructorReferenceVarInData
  = assertLeft $ runTC emptyCtx $ do
      typeCheckData nat
      typeCheckData list
      typeCheckData badVarReference

badVarReferenceOtherCtor :: DataDecl
badVarReferenceOtherCtor =
  DataDecl
  (Specified "Vect")
  (Pi (Specified "a", (Ty 0)) (Pi (Specified "n", Var (Specified "Nat")) (Ty 0)))
   -- VNil : Vect 0 a
  (fromList
   [(Specified "VNil",
      Pi (Specified "a", (Ty 0)) $
       (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` (Var (Specified "Zero")))
   -- VCons : (a:(Ty 0)) -> (x:a) -> (n:Nat) -> (xs:Vect a n) -> Vect a (S n)
   ,(Specified "VCons",
      Pi (Specified "x",Var (Specified "a")) $
       Pi (Specified "xs",App (Var (Specified "List")) (Var (Specified "a"))) $
        (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` ((Var (Specified "Succ")) `App` (Var (Specified "n"))))])

badVarReferenceOtherCtorRev :: DataDecl
badVarReferenceOtherCtorRev =
  DataDecl
  (Specified "Vect")
  (Pi (Specified "a", (Ty 0)) (Pi (Specified "n", Var (Specified "Nat")) (Ty 0)))
  (fromList
   [(Specified "VCons",
      Pi (Specified "x",Var (Specified "a")) $
       Pi (Specified "xs",App (Var (Specified "List")) (Var (Specified "a"))) $
        (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` ((Var (Specified "Succ")) `App` (Var (Specified "n"))))
   ,(Specified "VNil",
      Pi (Specified "a", (Ty 0)) $
       (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` (Var (Specified "Zero")))])

test_constructorReferenceVarInOtherConstructor
  = do assertLeft $ testingCtx >>= flip runTC
         (typeCheckData badVarReferenceOtherCtor)
       assertLeft $ testingCtx >>= flip runTC
         (typeCheckData badVarReferenceOtherCtorRev)


test_partiallyApplyCtorZero
  = assertRightAlphaEq
      (testingCtx >>= flip runTC (partiallyApplyCtor (var "Zero")))
      (Ctor (Specified "Zero") [])

test_partiallyApplyCtorSucc
  = assertRightAlphaEq
      (testingCtx >>= flip runTC ((partiallyApplyCtor (var "Succ"))))
      (Lam (Specified "n", Var (Specified "Nat")) (Ctor (Specified "Succ") [Var (Specified "n")]))

test_patternMatchNatTypeCheck
  = assertRight $ testingCtx >>= flip runTC (typeCheck patternMatchNat)

test_patternMatchNatWhnfZero
  = assertRightAlphaEq
      (testingCtx >>= flip runTC (whnf (patternMatchNat `App` zero)))
      (succ' zero)

test_patternMatchNatWhnfOne
  = assertRightAlphaEq
      (testingCtx >>= flip runTC (whnf (patternMatchNat `App` (succ' zero))))
      zero


assertLeft = assertBool "Expected a left; got a right" . isLeft

assertRight :: Show a => Either a b -> Assertion
assertRight (Left e) = assertFailure $ "Expected a right; got Left " <> show e
assertRight _ = return ()
assertAlphaEq a b
  = assertBool ("Terms are not alpha equal:\n" <> show a <> "\n" <> show b)  (isAlphaEq emptyCtx a b)

assertRightAlphaEq (Right a) b = assertBool ("Terms are not alpha equal:\n" <> show a <> "\n" <> show b) (isAlphaEq emptyCtx a b)
assertRightAlphaEq _ _ = assertFailure "Terms are not both Right"

badSigmas :: [DataDecl]
badSigmas = [
  DataDecl
  (Specified "Sigma")
  ((var "a", (Ty 0))
    --> (var "b", (var "x", v "a") --> (Ty 0))
    --> (Ty 0)) $
  fromList
  [(var "MkSigma",
     (var "a", (Ty 0))
     --> (var "b", (var "ignored", v "a") --> (Ty 0))
     --> (var "x", v "a")
     --> (var "ignored2", (v "b" `App` v "x"))
     --> (v "Sigma" `App` v "a" `App` (v "b" `App` v "x")))]
  , DataDecl
  (Specified "Sigma")
  ((var "a", (Ty 0))
    --> (var "b", (var "x", v "a") --> (Ty 0))
    --> (Ty 0)) $
  fromList
  [(var "MkSigma",
     (var "a", (Ty 0))
     --> (var "b", (var "ignored", v "a") --> (Ty 0))
     --> (var "x", v "a")
     --> (var "ignored2", (v "b" `App` v "a"))
     --> (v "Sigma" `App` v "a" `App` v "b"))]
  , DataDecl
  (Specified "Sigma")
  (
    (var "a", (Ty 0))
    --> (var "b", (var "x", v "a") --> (Ty 0))
    --> (Ty 0)) $
  fromList
  [(var "MkSigma",
     (var "a", (Ty 0))
     --> (var "b", (var "ignored", v "a") --> (Ty 0))
     --> (var "x", v "a")
     --> (var "ignored2", v "b")
     --> (v "Sigma" `App` v "a" `App` v "b"))]]

test_badSigmasFailTC :: Assertion
test_badSigmasFailTC
  = mapM_ (assertLeft . runTC emptyCtx . typeCheckData) badSigmas

goodBadCtxData :: DataDecl
goodBadCtxData = DataDecl
  (Specified "Good0")
  (
    (var "bad0", (Ty 0))
    --> (var "bad1", (var "bad2", v "bad0") --> (Ty 0))
    --> (Ty 0)) $
  fromList [(var "Good1",
     (var "bad3", (Ty 0))
     --> (var "bad4", (var "bad5", v "bad3") --> (Ty 0))
     --> (var "bad6", v "bad3")
     --> (var "bad7", (v "bad4" `App` v "bad6"))
     --> (v "Good0" `App` v "bad3" `App` v "bad4")
   )]

-- | Test that the context contains things that should be in the
-- context, and doesn't contain anything that shouldn't be.
test_contextProperlyFilledData :: Assertion
test_contextProperlyFilledData
  = assertEqual "Incorrect context returned" expectedCtx =<< getReturnedCtx
  where
    getReturnedCtx = case runTC emptyCtx $ typeCheckData goodBadCtxData of
      Right ctx -> return ctx
      Left err -> assertFailure ("Type error: " <> show err)
    expectedCtx =
      (Context {getCtx = [(Specified "Good1",Pi (Specified "bad3",Ty
      0) (Pi (Specified "bad4",Pi (Specified "bad5",Var (Specified
      "bad3")) (Ty 0)) (Pi (Specified "bad6",Var (Specified "bad3"))
      (Pi (Specified "bad7",App (Var (Specified "bad4")) (Var
      (Specified "bad6"))) (App (App (Var (Specified "Good0")) (Var
      (Specified "bad3"))) (Var (Specified "bad4"))))))),(Specified
      "Good0",Pi (Specified "bad0",Ty 0) (Pi (Specified "bad1",Pi
      (Specified "bad2",Var (Specified "bad0")) (Ty 0)) (Ty 0)))],
      getEnv = [], datatypes = [DataDecl {name = Specified "Good0", ty
      = Pi (Specified "bad0",Ty 0) (Pi (Specified "bad1",Pi (Specified
      "bad2",Var (Specified "bad0")) (Ty 0)) (Ty 0)), constructors =
      fromList [(Specified "Good1",Pi (Specified "bad3",Ty 0) (Pi
      (Specified "bad4",Pi (Specified "bad5",Var (Specified "bad3"))
      (Ty 0)) (Pi (Specified "bad6",Var (Specified "bad3")) (Pi
      (Specified "bad7",App (Var (Specified "bad4")) (Var (Specified
      "bad6"))) (App (App (Var (Specified "Good0")) (Var (Specified
      "bad3"))) (Var (Specified "bad4")))))))]}]})
