module Test.DataTypes where

import Examples
import TC
import Types
import TypeCheck

import Data.Either
import Test.Tasty.HUnit

test_dupConstructorsDisallowed = assertLeft $ runTC $ typeCheckData dupConstructors

dupConstructors :: DataDecl
dupConstructors =
  (Specified "data"
    , Type Ty
    , [(Specified "dupConstructor", Type $ Var (Specified "data"))
      ,(Specified "dupConstructor", Type $ Var (Specified "data"))])

test_constructorNotReturnDataDisallowed = assertLeft $ runTC $ typeCheckData badConstructorType

badConstructorType :: DataDecl
badConstructorType =
  (Specified "data"
  , Type Ty
    , [(Specified "invalidTypeConstructor", Type $ Ty)])

badVarReference :: DataDecl
badVarReference =
  (Specified "Vect"
  ,Type (Pi (Specified "a", Ty) (Pi (Specified "n", Var (Specified "Nat")) Ty))
   -- VNil : Vect 0 a
  ,[(Specified "VNil", Type $
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
  (Specified "Vect"
  ,Type (Pi (Specified "a", Ty) (Pi (Specified "n", Var (Specified "Nat")) Ty))
   -- VNil : Vect 0 a
  ,[(Specified "VNil", Type $
      Pi (Specified "a", Ty) $
       (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` (Var (Specified "Zero")))
   -- VCons : (a:Ty) -> (x:a) -> (n:Nat) -> (xs:Vect a n) -> Vect a (S n)
   ,(Specified "VCons", Type $
      Pi (Specified "x",Var (Specified "a")) $
       Pi (Specified "xs",App (Var (Specified "List")) (Var (Specified "a"))) $
        (Var (Specified "Vect")) `App` (Var (Specified "a")) `App` ((Var (Specified "Succ")) `App` (Var (Specified "n"))))])

badVarReferenceOtherCtorRev :: DataDecl
badVarReferenceOtherCtorRev =
  (Specified "Vect"
  ,Type (Pi (Specified "a", Ty) (Pi (Specified "n", Var (Specified "Nat")) Ty))
  ,[(Specified "VCons", Type $
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

assertLeft = assertBool "Expected a left; got a right" . isLeft
assertRight = assertBool "Expected a right; got a left" . isRight
