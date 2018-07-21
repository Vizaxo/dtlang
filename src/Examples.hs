module Examples where

import Interpreter
import TypeCheck
import Types

import Data.Either

id' :: Term Int
id' = Lam (0, Ty) (Lam (1, Var 0) (Var 1))

idTy :: Term Int
idTy = fromRight undefined (typeCheck [] id')

appId :: Term Int
appId = (id' `App` idTy) `App` id'
