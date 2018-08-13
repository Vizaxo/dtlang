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


nat :: DataDecl
nat = DataDecl
  (Specified "Nat")
  (Type Ty)
  ([(Specified "Zero", Type $ Var (Specified "Nat"))
    ,(Specified "Succ", Type $
       Pi (Specified "x",Var (Specified "Nat"))
         (Var (Specified "Nat")))])

var = Specified
v = Var . var

natT = v "Nat"
zero = v "Zero"
succ' = v "Succ"

list :: DataDecl
list = DataDecl
  (Specified "List")
  (Type (Pi (Specified "a", Ty) Ty))
  -- Nil : List a
  ([(Specified "Nil", Type $
     Pi (Specified "a", Ty) $
      App (Var (Specified "List")) (Var (Specified "a")))
  -- Cons : (a:Ty) -> (x:a) -> (xs:List a) -> List a
  ,(Specified "Cons", Type $
     Pi (Specified "a",Ty) $
      Pi (Specified "x",Var (Specified "a")) $
       Pi (Specified "xs",App (Var (Specified "List")) (Var (Specified "a"))) $
        App (Var (Specified "List")) (Var (Specified "a")))])

listT = v "List"
nil = v "Nil"
cons = v "Cons"

vect :: DataDecl
vect = DataDecl
  (Specified "Vect")
  (Type (Pi (Specified "n", Var (Specified "Nat")) (Pi (Specified "a", Ty) Ty)))
  -- VNil : Vect 0 a
  ([(Specified "VNil", Type $
     Pi (Specified "a", Ty) $
      (Var (Specified "Vect")) `App` (Var (Specified "Zero")) `App` (Var (Specified "a")))
  -- VCons : (a:Ty) -> (x:a) -> (n:Nat) -> (xs:Vect n a) -> Vect (S n) a
   ,(Specified "VCons", Type $
      Pi (Specified "a",Ty) $
       Pi (Specified "n",(Var (Specified "Nat"))) $
        Pi (Specified "x",Var (Specified "a")) $
         Pi (Specified "xs",(Var (Specified "Vect")) `App` (Var (Specified "n")) `App` (Var (Specified "a"))) $
          (Var (Specified "Vect")) `App` ((Var (Specified "Succ")) `App` (Var (Specified "n"))) `App` (Var (Specified "a")))])

vectT = v "Vect"
vnil = v "VNil"
vcons = v "VCons"

zeroT :: Term
zeroT = Var (Specified "Zero")

succT :: Term
succT = Var (Specified "Succ")

three :: Term
three = succT `App` succT `App` succT `App` zeroT

patternMatchNat
  = Lam (var "n", natT) $
     Case (v "n")
      [CaseTerm (var "Zero") [] (succ' `App` zero)
      ,CaseTerm (var "Succ") [(var "n", natT)] zero]
