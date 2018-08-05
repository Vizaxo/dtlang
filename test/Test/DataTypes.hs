module Test.DataTypes where

import TC
import Types
import TypeCheck

import Data.Either
import Test.Tasty.HUnit

test_dupConstructorsDisallowed = assertBool "" $ isLeft $ runTC $ typeCheckData dupConstructors

dupConstructors :: DataDecl
dupConstructors =
  (Specified "data"
    , Type Ty
    , [(Specified "dupConstructor", Type $ Var (Specified "data"))
      ,(Specified "dupConstructor", Type $ Var (Specified "data"))])

test_constructorNotReturnDataDisallowed = assertBool "" $ isLeft $ runTC $ typeCheckData badConstructorType

badConstructorType :: DataDecl
badConstructorType =
  (Specified "data"
  , Type Ty
    , [(Specified "invalidTypeConstructor", Type $ Ty)])
