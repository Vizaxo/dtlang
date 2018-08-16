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
  (Type Ty)
  ([(Specified "dupConstructor", Type $ Var (Specified "data"))
   ,(Specified "dupConstructor", Type $ Var (Specified "data"))])

test_constructorNotReturnDataDisallowed = assertLeft $ runTC $ typeCheckData badConstructorType

badConstructorType :: DataDecl
badConstructorType =
  DataDecl
  (Specified "data")
  (Type Ty)
  ([(Specified "invalidTypeConstructor", Type $ Ty)])

badVarReference :: DataDecl
badVarReference =
  DataDecl
  (Specified "Vect")
  (Type (Pi (Specified "a", Ty) (Pi (Specified "n", Var (Specified "Nat")) Ty)))
   -- VNil : Vect 0 a
  ([(Specified "VNil", Type $
      Pi (Specified "a", Ty) $
       (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` (Var (Specified "Zero")))
   -- VCons : (a:Ty) -> (x:a) -> (n:Nat) -> (xs:Vect a n) -> Vect a (S n)
   ,(Specified "VCons", Type $
      Pi (Specified "a",Ty) $
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
  (Type (Pi (Specified "a", Ty) (Pi (Specified "n", Var (Specified "Nat")) Ty)))
   -- VNil : Vect 0 a
  ([(Specified "VNil", Type $
      Pi (Specified "a", Ty) $
       (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` (Var (Specified "Zero")))
   -- VCons : (a:Ty) -> (x:a) -> (n:Nat) -> (xs:Vect a n) -> Vect a (S n)
   ,(Specified "VCons", Type $
      Pi (Specified "x",Var (Specified "a")) $
       Pi (Specified "xs",App (Var (Specified "List")) (Var (Specified "a"))) $
        (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` ((Var (Specified "Succ")) `App` (Var (Specified "n"))))])

badVarReferenceOtherCtorRev :: DataDecl
badVarReferenceOtherCtorRev =
  DataDecl
  (Specified "Vect")
  (Type (Pi (Specified "a", Ty) (Pi (Specified "n", Var (Specified "Nat")) Ty)))
  ([(Specified "VCons", Type $
      Pi (Specified "x",Var (Specified "a")) $
       Pi (Specified "xs",App (Var (Specified "List")) (Var (Specified "a"))) $
        (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` ((Var (Specified "Succ")) `App` (Var (Specified "n"))))
   ,(Specified "VNil", Type $
      Pi (Specified "a", Ty) $
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
  (Type $
    (var "a", Ty)
    --> (var "b", (var "x", v "a") --> Ty)
    --> Ty)
  [(var "MkSigma", Type $
     (var "a", Ty)
     --> (var "b", (var "ignored", v "a") --> Ty)
     --> (var "x", v "a")
     --> (var "ignored2", (v "b" `App` v "x"))
     --> (v "Sigma" `App` v "a" `App` (v "b" `App` v "x")))]
  , DataDecl
  (Specified "Sigma")
  (Type $
    (var "a", Ty)
    --> (var "b", (var "x", v "a") --> Ty)
    --> Ty)
  [(var "MkSigma", Type $
     (var "a", Ty)
     --> (var "b", (var "ignored", v "a") --> Ty)
     --> (var "x", v "a")
     --> (var "ignored2", (v "b" `App` v "a"))
     --> (v "Sigma" `App` v "a" `App` v "b"))]
  , DataDecl
  (Specified "Sigma")
  (Type $
    (var "a", Ty)
    --> (var "b", (var "x", v "a") --> Ty)
    --> Ty)
  [(var "MkSigma", Type $
     (var "a", Ty)
     --> (var "b", (var "ignored", v "a") --> Ty)
     --> (var "x", v "a")
     --> (var "ignored2", v "b")
     --> (v "Sigma" `App` v "a" `App` v "b"))]]

test_badSigmasFailTC :: Assertion
test_badSigmasFailTC
  = mapM_ (assertLeft . runTC . typeCheckData) badSigmas

--TODO: abstract this, check whole library of datatypes type-check
test_sigmaTypeChecks = assertRight $ runTC $ typeCheckData sigma

test_voidTypeChecks = assertRight $ runTC $ typeCheckData void
