module Examples where

import TC
import Types
import TypeCheck

import Control.Monad.Reader hiding (void)
import Data.Either

defaultCtx :: Either TypeError Context
defaultCtx = getCtxTC emptyCtx $ ask `bindCtx`
  checkAndInsert (Specified "id") id' `bindCtx`
  checkAndInsert (Specified "fst") fst' `bindCtx`
  checkAndInsert (Specified "snd") snd' `bindCtx`
  checkAndInsert (Specified "pair") pair `bindCtx`
  typeCheckData nat `bindCtx`
  typeCheckData list `bindCtx`
  typeCheckData vect `bindCtx`
  typeCheckData void `bindCtx`
  typeCheckData sigma
  where
    infixl 5 `bindCtx`
    bindCtx :: TC Context -> TC a -> TC a
    bindCtx ctxM m = ctxM >>= \ctx -> local (const ctx) m

-- | id : (t:(Ty 0)) -> t -> t
--   id = \t. \a. a
id' :: Term
id' = Lam (toEnum 0, (Ty 0)) (Lam (toEnum 1, Var (toEnum 0)) (Var (toEnum 1)))

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


bool :: DataDecl
bool = DataDecl
  (Specified "Bool")
  (Ty 0)
  ([ (Specified "False", Var (Specified "Bool"))
   , (Specified "True", Var (Specified "Bool"))])

not' :: Term
not' = Lam (var "b", v "Bool") $
     Case (v "b")
      [ CaseTerm (var "True") [] (Ctor (var "False") [])
      , CaseTerm (var "False") [] (Ctor (var "True") [])]

boolId :: Term
boolId = Lam (var "x", Var (Specified "Bool")) (v "x")

nat :: DataDecl
nat = DataDecl
  (Specified "Nat")
  (Ty 0)
  ([(Specified "Zero", Var (Specified "Nat"))
    ,(Specified "Succ",
       Pi (Specified "x",Var (Specified "Nat"))
         (Var (Specified "Nat")))])

natId :: Term
natId = Lam (var "x", natT) (v "x")

var = Specified
v = Var . var

c n = Ctor (var n)

natT = v "Nat"
zero = c "Zero" []
succ' n = c "Succ" [n]

list :: DataDecl
list = DataDecl
  (Specified "List")
  (Pi (Specified "a", (Ty 0)) (Ty 0))
  -- Nil : List a
  ([(Specified "Nil",
     Pi (Specified "a", (Ty 0)) $
      App (Var (Specified "List")) (Var (Specified "a")))
  -- Cons : (a:(Ty 0)) -> (x:a) -> (xs:List a) -> List a
  ,(Specified "Cons",
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
  (Pi (Specified "n", Var (Specified "Nat")) (Pi (Specified "a", (Ty 0)) (Ty 0)))
  -- VNil : Vect 0 a
  ([(Specified "VNil",
     Pi (Specified "a", (Ty 0)) $
      (Var (Specified "Vect")) `App` (Var (Specified "Zero")) `App` (Var (Specified "a")))
  -- VCons : (a:(Ty 0)) -> (x:a) -> (n:Nat) -> (xs:Vect n a) -> Vect (S n) a
   ,(Specified "VCons",
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
      [CaseTerm (var "Zero") [] (Ctor (var "Succ") [Ctor (var "Zero") []])
      ,CaseTerm (var "Succ") [(var "n", natT)] (Ctor (var "Zero") [])]

patternMatchNat'
  = Case (Ctor (var "Succ") [Ctor (var "Succ") [Ctor (var "Zero") []]])
      [CaseTerm (var "Zero") [] (Ctor (var "Succ") [Ctor (var "Zero") []])
      ,CaseTerm (var "Succ") [(var "n", natT)] (v "n")]

testCase = (Ctor (var "Succ") [Ctor (var "Zero") []])

void :: DataDecl
void = DataDecl
  (Specified "Void")
  (Ty 0)
  []

sigma :: DataDecl
sigma = DataDecl
  (Specified "Sigma")
  ((var "a", (Ty 0))
    --> (var "b", (var "x", v "a") --> (Ty 0))
    --> (Ty 0))
  [(var "MkSigma",
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

plusTerm = (Lam (var "n", natT) $ Lam (var "m", natT) $
   Case (v "n") [ CaseTerm (var "Zero") [] (v "m")
                , CaseTerm (var "Succ") [(var "n'", natT)] (v "plus" `App` v "n" `App` v "m")
                ])

k = Lam (var "a", natT) (Lam (var "b", natT) (v "a"))
closureTest = k `App` (succ' zero) `App` zero
