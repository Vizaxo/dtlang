module Examples where

import Interpreter
import TypeCheck
import Types

import Data.Either

id' :: Enum v => Term v
id' = Lam (toEnum 0, Ty) (Lam (toEnum 1, Var (toEnum 0)) (Var (toEnum 1)))

idTy :: Term Int
idTy = fromRight undefined (typeCheck [] id')

appId :: Term Int
appId = (id' `App` idTy) `App` id'
