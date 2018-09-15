module Examples where

import TC
import Types
import TypeCheck

import Data.Either

defaultCtx :: Either TypeError Context
defaultCtx = getCtxTC $
  checkAndInsert (Specified "id") id' >>
  checkAndInsert (Specified "fst") fst' >>
  checkAndInsert (Specified "snd") snd' >>
  checkAndInsert (Specified "pair") pair >>
  typeCheckData nat >>
  typeCheckData list >>
  typeCheckData vect >>
  typeCheckData void >>
  typeCheckData sigma

-- | id : (t:(Ty 0)) -> t -> t
--   id = \t. \a. a
id' :: Term
id' = Lam (toEnum 0, (Ty 0)) (Lam (toEnum 1, Var (toEnum 0)) (Var (toEnum 1)))

unsafeGetType :: Term -> Term
unsafeGetType = fromRight undefined . runTC . typeCheck

-- | Apply a term to id, automatically substituting in the term's type.
appId :: Term -> Term
appId t = (id' `App` unsafeGetType t) `App` t

-- | fst : (t:(Ty 0)) -> t -> t -> t
--   fst = \t. \a. \b. a
fst' :: Term
fst' = (Lam (toEnum 0, (Ty 0))
        (Lam (toEnum 1, Var (toEnum 0))
          (Lam (toEnum 2, Var (toEnum 0))
            (Var (toEnum 1)))))

-- | snd : (t:(Ty 0)) -> t -> t -> t
--   snd = \t. \a. \b. b
snd' :: Term
snd' = (Lam (toEnum 0, (Ty 0))
        (Lam (toEnum 1, Var (toEnum 0))
          (Lam (toEnum 2, Var (toEnum 0))
            (Var (toEnum 2)))))

-- | pair : (t:(Ty 0)) -> t -> t -> (t -> t -> t) -> t
--   pair = \t. \a. \b. \f. f a b
pair :: Term
pair = (Lam (toEnum 0, (Ty 0))
         (Lam (toEnum 5, Var (toEnum 0))
           (Lam (toEnum 6, Var (toEnum 0))
             (Lam (toEnum 2, Pi (toEnum 3, Var (toEnum 0)) (Pi (toEnum 4, Var (toEnum 0)) (Var (toEnum 0))))
               (App (App (Var (toEnum 2)) (Var (toEnum 5))) (Var (toEnum 6)))))))


nat :: DataDecl
nat = DataDecl
  (Specified "Nat")
  (Type (Ty 0))
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
  (Type (Pi (Specified "a", (Ty 0)) (Ty 0)))
  -- Nil : List a
  ([(Specified "Nil", Type $
     Pi (Specified "a", (Ty 0)) $
      App (Var (Specified "List")) (Var (Specified "a")))
  -- Cons : (a:(Ty 0)) -> (x:a) -> (xs:List a) -> List a
  ,(Specified "Cons", Type $
     Pi (Specified "a",(Ty 0)) $
      Pi (Specified "x",Var (Specified "a")) $
       Pi (Specified "xs",App (Var (Specified "List")) (Var (Specified "a"))) $
        App (Var (Specified "List")) (Var (Specified "a")))])

listT = v "List"
nil = v "Nil"
cons = v "Cons"

vect :: DataDecl
vect = DataDecl
  (Specified "Vect")
  (Type (Pi (Specified "n", Var (Specified "Nat")) (Pi (Specified "a", (Ty 0)) (Ty 0))))
  -- VNil : Vect 0 a
  ([(Specified "VNil", Type $
     Pi (Specified "a", (Ty 0)) $
      (Var (Specified "Vect")) `App` (Var (Specified "Zero")) `App` (Var (Specified "a")))
  -- VCons : (a:(Ty 0)) -> (x:a) -> (n:Nat) -> (xs:Vect n a) -> Vect (S n) a
   ,(Specified "VCons", Type $
      Pi (Specified "a",(Ty 0)) $
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

void :: DataDecl
void = DataDecl
  (Specified "Void")
  (Type (Ty 0))
  []

sigma :: DataDecl
sigma = DataDecl
  (Specified "Sigma")
  (Type $
    (var "a", (Ty 0))
    --> (var "b", (var "x", v "a") --> (Ty 0))
    --> (Ty 0))
  [(var "MkSigma", Type $
     (var "a", (Ty 0))
     --> (var "b", (var "ignored", v "a") --> (Ty 0))
     --> (var "x", v "a")
     --> (var "ignored2", (v "b" `App` v "x"))
     --> (v "Sigma" `App` v "a" `App` v "b")
   )]

plus :: Definition
plus = Definition (Specified "plus") (Pi (var "n", natT) $ Pi (var "m", natT) $ natT)
  (Lam (var "n", natT) $ Lam (var "m", natT) $
   Case (v "n") [ CaseTerm (var "Zero") [] (v "m")
                , CaseTerm (var "Succ") [(var "n'", natT)] (v "plus" `App` v "n" `App` v "m")
                ])
