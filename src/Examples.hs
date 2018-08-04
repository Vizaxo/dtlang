module Examples where

import TC
import Types
import TypeCheck

import Data.Either

-- | id : (t:Ty) -> t -> t
--   id = \t. \a. a
id' :: Term
id' = Lam (toEnum 0, Ty) (Lam (toEnum 1, Var (toEnum 0)) (Var (toEnum 1)))

unsafeGetType :: Term -> Term
unsafeGetType = fromRight undefined . runTC . typeCheck

-- | Apply a term to id, automatically substituting in the term's type.
appId :: Term -> Term
appId t = (id' `App` unsafeGetType t) `App` t

-- | fst : (t:Ty) -> t -> t -> t
--   fst = \t. \a. \b. a
fst' :: Term
fst' = (Lam (toEnum 0, Ty)
        (Lam (toEnum 1, Var (toEnum 0))
          (Lam (toEnum 2, Var (toEnum 0))
            (Var (toEnum 1)))))

-- | snd : (t:Ty) -> t -> t -> t
--   snd = \t. \a. \b. b
snd' :: Term
snd' = (Lam (toEnum 0, Ty)
        (Lam (toEnum 1, Var (toEnum 0))
          (Lam (toEnum 2, Var (toEnum 0))
            (Var (toEnum 2)))))

-- | pair : (t:Ty) -> t -> t -> (t -> t -> t) -> t
--   pair = \t. \a. \b. \f. f a b
pair :: Term
pair = (Lam (toEnum 0, Ty)
         (Lam (toEnum 5, Var (toEnum 0))
           (Lam (toEnum 6, Var (toEnum 0))
             (Lam (toEnum 2, Pi (toEnum 3, Var (toEnum 0)) (Pi (toEnum 4, Var (toEnum 0)) (Var (toEnum 0))))
               (App (App (Var (toEnum 2)) (Var (toEnum 5))) (Var (toEnum 6)))))))
