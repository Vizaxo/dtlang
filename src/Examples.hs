module Examples where

import Interpreter
import TypeCheck
import Term

import Data.Either

id' :: Enum v => Term v
id' = Lam (toEnum 0, Ty) (Lam (toEnum 1, Var (toEnum 0)) (Var (toEnum 1)))

idTy :: Term Int
idTy = fromRight undefined (typeCheck [] id')

unsafeGetType :: (Eq v, Show v, Enum v) => Term v -> Term v
unsafeGetType = fromRight undefined . typeCheck []

appId :: (Eq v, Show v, Enum v) => Term v -> Term v
appId t = (id' `App` unsafeGetType t) `App` t

appIdId :: Term Int
appIdId = appId id'

fst' :: (Eq v, Show v, Enum v) => Term v
fst' = (Lam (toEnum 0, Ty)
        (Lam (toEnum 1, Var (toEnum 0))
          (Lam (toEnum 2, Var (toEnum 0))
            (Var (toEnum 1)))))

snd' :: (Eq v, Show v, Enum v) => Term v
snd' = (Lam (toEnum 0, Ty)
        (Lam (toEnum 1, Var (toEnum 0))
          (Lam (toEnum 2, Var (toEnum 0))
            (Var (toEnum 2)))))

pair :: (Eq v, Show v, Enum v) => Term v
pair = (Lam (toEnum 0, Ty)
         (Lam (toEnum 5, Var (toEnum 0))
           (Lam (toEnum 6, Var (toEnum 0))
             (Lam (toEnum 2, Pi (toEnum 3, Var (toEnum 0)) (Pi (toEnum 4, Var (toEnum 0)) (Var (toEnum 0))))
               (App (App (Var (toEnum 2)) (Var (toEnum 5))) (Var (toEnum 6)))))))
