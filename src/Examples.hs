module Examples where

import Term
import TypeCheck

import Data.Either

-- | id : (t:Ty) -> t -> t
--   id = \t. \a. a
id' :: Enum v => Term v
id' = Lam (toEnum 0, Ty) (Lam (toEnum 1, Var (toEnum 0)) (Var (toEnum 1)))

unsafeGetType :: (Eq v, Show v, Enum v) => Term v -> Term v
unsafeGetType = fromRight undefined . typeCheck []

-- | Apply a term to id, automatically substituting in the term's type.
appId :: (Eq v, Show v, Enum v) => Term v -> Term v
appId t = (id' `App` unsafeGetType t) `App` t

-- | fst : (t:Ty) -> t -> t -> t
--   fst = \t. \a. \b. a
fst' :: (Eq v, Show v, Enum v) => Term v
fst' = (Lam (toEnum 0, Ty)
        (Lam (toEnum 1, Var (toEnum 0))
          (Lam (toEnum 2, Var (toEnum 0))
            (Var (toEnum 1)))))

-- | snd : (t:Ty) -> t -> t -> t
--   snd = \t. \a. \b. b
snd' :: (Eq v, Show v, Enum v) => Term v
snd' = (Lam (toEnum 0, Ty)
        (Lam (toEnum 1, Var (toEnum 0))
          (Lam (toEnum 2, Var (toEnum 0))
            (Var (toEnum 2)))))

-- | pair : (t:Ty) -> t -> t -> (t -> t -> t) -> t
--   pair = \t. \a. \b. \f. f a b
pair :: (Eq v, Show v, Enum v) => Term v
pair = (Lam (toEnum 0, Ty)
         (Lam (toEnum 5, Var (toEnum 0))
           (Lam (toEnum 6, Var (toEnum 0))
             (Lam (toEnum 2, Pi (toEnum 3, Var (toEnum 0)) (Pi (toEnum 4, Var (toEnum 0)) (Var (toEnum 0))))
               (App (App (Var (toEnum 2)) (Var (toEnum 5))) (Var (toEnum 6)))))))
