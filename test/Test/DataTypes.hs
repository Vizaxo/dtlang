module Test.DataTypes where

import Equality
import Examples
import TC
import Types
import TypeCheck

import Data.Either
import Test.Tasty.HUnit

test_dupConstructorsDisallowed = assertLeft $ runTC $ typeCheckData dupConstructors

dupConstructors :: DataDecl
dupConstructors =
  DataDecl
  (Specified "data")
  (Ty 0)
  ([(Specified "dupConstructor", Var (Specified "data"))
   ,(Specified "dupConstructor", Var (Specified "data"))])

test_constructorNotReturnDataDisallowed = assertLeft $ runTC $ typeCheckData badConstructorType

badConstructorType :: DataDecl
badConstructorType =
  DataDecl
  (Specified "data")
  (Ty 0)
  ([(Specified "invalidTypeConstructor", (Ty 0))])

badVarReference :: DataDecl
badVarReference =
  DataDecl
  (Specified "Vect")
  (Pi (Specified "a", (Ty 0)) (Pi (Specified "n", Var (Specified "Nat")) (Ty 0)))
   -- VNil : Vect 0 a
  ([(Specified "VNil",
      Pi (Specified "a", (Ty 0)) $
       (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` (Var (Specified "Zero")))
   -- VCons : (a:(Ty 0)) -> (x:a) -> (n:Nat) -> (xs:Vect a n) -> Vect a (S n)
   ,(Specified "VCons",
      Pi (Specified "a",(Ty 0)) $
       Pi (Specified "x",Var (Specified "a")) $
        Pi (Specified "xs",App (Var (Specified "List")) (Var (Specified "a"))) $
         (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` ((Var (Specified "Succ")) `App` (Var (Specified "n"))))])

test_constructorReferenceVarInData
  = assertLeft $ runTC $ do
      typeCheckData nat
      typeCheckData list
      typeCheckData badVarReference

badVarReferenceOtherCtor :: DataDecl
badVarReferenceOtherCtor =
  DataDecl
  (Specified "Vect")
  (Pi (Specified "a", (Ty 0)) (Pi (Specified "n", Var (Specified "Nat")) (Ty 0)))
   -- VNil : Vect 0 a
  ([(Specified "VNil",
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
  ([(Specified "VCons",
      Pi (Specified "x",Var (Specified "a")) $
       Pi (Specified "xs",App (Var (Specified "List")) (Var (Specified "a"))) $
        (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` ((Var (Specified "Succ")) `App` (Var (Specified "n"))))
   ,(Specified "VNil",
      Pi (Specified "a", (Ty 0)) $
       (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` (Var (Specified "Zero")))])

test_constructorReferenceVarInOtherConstructor
  = do assertLeft $ runTC $ do
         typeCheckData nat
         typeCheckData list
         typeCheckData badVarReferenceOtherCtor
       assertLeft $ runTC $ do
         typeCheckData nat
         typeCheckData list
         typeCheckData badVarReferenceOtherCtorRev


test_nat = assertRight $ runTC $ typeCheckData nat

test_list = assertRight $ runTC $ typeCheckData list

test_vect = assertRight $ runTC $ typeCheckData nat >> typeCheckData vect

test_partiallyApplyCtorZero
  = assertRightAlphaEq
      (runTC $ typeCheckData nat >> (partiallyApplyCtor (var "Zero")))
      (Ctor (Specified "Zero") [])

test_partiallyApplyCtorSucc
  = assertRightAlphaEq
      (runTC $ typeCheckData nat >> (partiallyApplyCtor (var "Succ")))
      (Lam (Specified "n", Var (Specified "Nat")) (Ctor (Specified "Succ") [Var (Specified "n")]))

test_patternMatchNatTypeCheck
  = assertRight $ runTC $ typeCheckData nat >> typeCheck patternMatchNat

test_patternMatchNatWhnfZero
  = assertRightAlphaEq
      (runTC $ typeCheckData nat >> whnf (patternMatchNat `App` zero))
      (succ' `App` zero)

test_patternMatchNatWhnfOne
  = assertRightAlphaEq
      (runTC $ typeCheckData nat >> whnf (patternMatchNat `App` (succ' `App` zero)))
      zero


assertLeft = assertBool "Expected a left; got a right" . isLeft

assertRight :: Show a => Either a b -> Assertion
assertRight (Left e) = assertFailure $ "Expected a right; got Left " <> show e
assertRight _ = return ()
assertAlphaEq a b = assertBool ("Terms are not alpha equal:\n" <> show a <> "\n" <> show b)  (a `isAlphaEq` b)
assertRightAlphaEq (Right a) b = assertBool ("Terms are not alpha equal:\n" <> show a <> "\n" <> show b) (a `isAlphaEq` b)
assertRightAlphaEq _ _ = assertFailure "Terms are not both Right"

badSigmas :: [DataDecl]
badSigmas = [
  DataDecl
  (Specified "Sigma")
  ((var "a", (Ty 0))
    --> (var "b", (var "x", v "a") --> (Ty 0))
    --> (Ty 0))
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
    --> (Ty 0))
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
    --> (Ty 0))
  [(var "MkSigma",
     (var "a", (Ty 0))
     --> (var "b", (var "ignored", v "a") --> (Ty 0))
     --> (var "x", v "a")
     --> (var "ignored2", v "b")
     --> (v "Sigma" `App` v "a" `App` v "b"))]]

test_badSigmasFailTC :: Assertion
test_badSigmasFailTC
  = mapM_ (assertLeft . runTC . typeCheckData) badSigmas

--TODO: abstract this, check whole library of datatypes type-check
test_sigmaTypeChecks = assertRight $ runTC $ typeCheckData sigma

test_voidTypeChecks = assertRight $ runTC $ typeCheckData void


goodBadCtxData :: DataDecl
goodBadCtxData = DataDecl
  (Specified "Good0")
  (
    (var "bad0", (Ty 0))
    --> (var "bad1", (var "bad2", v "bad0") --> (Ty 0))
    --> (Ty 0))
  [(var "Good1",
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
  = assertEqual "Incorrect context returned" expectedCtx returnedCtx
  where
    returnedCtx = getCtxTC $ typeCheckData goodBadCtxData
    expectedCtx =
      Right (Context {getCtx = [(Specified "Good1",Pi (Specified
      "bad3",Ty 0) (Pi (Specified "bad4",Pi (Specified "bad5",Var
      (Specified "bad3")) (Ty 0)) (Pi (Specified "bad6",Var (Specified
      "bad3")) (Pi (Specified "bad7",App (Var (Specified "bad4")) (Var
      (Specified "bad6"))) (App (App (Var (Specified "Good0")) (Var
      (Specified "bad3"))) (Var (Specified "bad4"))))))),(Specified
      "Good0",Pi (Specified "bad0",Ty 0) (Pi (Specified "bad1",Pi
      (Specified "bad2",Var (Specified "bad0")) (Ty 0)) (Ty 0)))],
      datatypes = [DataDecl {name = Specified "Good0", ty = Pi
      (Specified "bad0",Ty 0) (Pi (Specified "bad1",Pi (Specified
      "bad2",Var (Specified "bad0")) (Ty 0)) (Ty 0)), constructors =
      [(Specified "Good1",Pi (Specified "bad3",Ty 0) (Pi (Specified
      "bad4",Pi (Specified "bad5",Var (Specified "bad3")) (Ty 0)) (Pi
      (Specified "bad6",Var (Specified "bad3")) (Pi (Specified
      "bad7",App (Var (Specified "bad4")) (Var (Specified "bad6")))
      (App (App (Var (Specified "Good0")) (Var (Specified "bad3")))
      (Var (Specified "bad4")))))))]}]})
