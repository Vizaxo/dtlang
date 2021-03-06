module Examples where

import TC
import Types
import TypeCheck

import Control.Monad.Reader hiding (void)
import Data.Map (singleton, fromList, empty)

testingCtx :: Either TypeError Context
testingCtx = getCtxTC emptyCtx $ ask `bindCtx`
  checkAndInsert (Specified "id") id' `bindCtx`
  checkAndInsert (Specified "fst") fst' `bindCtx`
  checkAndInsert (Specified "snd") snd' `bindCtx`
  checkAndInsert (Specified "pair") pair `bindCtx`
  checkAndInsert (Specified "fix") tfix `bindCtx`
  typeCheckData nat `bindCtx`
  typeCheckData list `bindCtx`
  typeCheckData vect `bindCtx`
  typeCheckData void `bindCtx`
  typeCheckData unit `bindCtx`
  typeCheckData sigma

defaultCtx :: Either TypeError Context
defaultCtx = getCtxTC emptyCtx $ ask `bindCtx`
  checkAndInsert (Specified "fix") tfix

infixl 5 `bindCtx`
bindCtx :: TC Context -> TC a -> TC a
bindCtx ctxM m = ctxM >>= \ctx -> local (const ctx) m

tfix :: Term
tfix = Lam (var "A", Ty 0) $ Lam (var "f", (Pi (var "ignored", v "A") (v "A"))) $ TFix (v "f")

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
  (fromList [ (Specified "False", Var (Specified "Bool"))
            , (Specified "True", Var (Specified "Bool"))])

not' :: Term
not' = Lam (var "b", v "Bool") $
     Case (v "b") (v "Bool") $
      fromList [ (var "True", CaseTerm [] (v "False"))
               , (var "False", CaseTerm [] (Ctor (var "True") []))]

boolId :: Term
boolId = Lam (var "x", Var (Specified "Bool")) (v "x")

nat :: DataDecl
nat = DataDecl
  (Specified "Nat")
  (Ty 0)
  (fromList [(Specified "Zero", Var (Specified "Nat"))
            ,(Specified "Succ",
              Pi (Specified "n",Var (Specified "Nat"))
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
  (fromList
   [(Specified "Nil",
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
  (fromList
   [(Specified "VNil",
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

patternMatchNat :: Term
patternMatchNat
  = Lam (var "n", natT) $
     Case (v "n") (Lam (var "x", natT) natT) $
      fromList
      [(var "Zero", CaseTerm  [] (succ' zero))
      ,(var "Succ", CaseTerm  [var "n"] zero)
      ]

void :: DataDecl
void = DataDecl
  (Specified "Void")
  (Ty 0)
  empty

unit :: DataDecl
unit = DataDecl
  (Specified "Unit")
  (Ty 0) $
  singleton (var "MkUnit") (v "Unit")

sigma :: DataDecl
sigma = DataDecl
  (Specified "Sigma")
  ((var "a", (Ty 0))
    --> (var "b", (var "x", v "a") --> (Ty 0))
    --> (Ty 0))
  $ singleton (var "MkSigma") $
     (var "a", (Ty 0))
     --> (var "b", (var "ignored", v "a") --> (Ty 0))
     --> (var "x", v "a")
     --> (var "ignored2", (v "b" `App` v "x"))
     --> (v "Sigma" `App` v "a" `App` v "b")

plus :: Definition
plus = Definition (Specified "plus") (Pi (var "n", natT) $ Pi (var "m", natT) $ natT)
  (Lam (var "n", natT) $ Lam (var "m", natT) $
   Case (v "n") (Lam (var "ignored", natT) natT) $
   fromList [ (var "Zero", CaseTerm  [] (v "m"))
            , (var "Succ", CaseTerm  [var "n'"] (v "plus" `App` v "n" `App` v "m"))
            ])

plusTerm :: Term
plusTerm = (Lam (var "n", natT) $ Lam (var "m", natT) $
   Case (v "n") (v "Nat") $
   fromList [ (var "Zero", CaseTerm  [] (v "m"))
            , (var "Succ", CaseTerm  [var "n"] (v "plus" `App` v "n" `App` v "m"))
            ])

k :: Term
k = Lam (var "a", natT) (Lam (var "b", natT) (v "a"))

closureTest :: Term
closureTest = k `App` (succ' zero) `App` zero

add :: Term
add = Lam (var "x", natT) $ TFix $ Lam (var "f", (Pi (var "x", natT) natT)) $ Lam (var "y", natT) $
  Case (v "y") (Lam (var "ignored",natT) natT) $
  fromList [ (var "Zero", CaseTerm [] (v "x"))
           , (var "Succ", CaseTerm [var "y'"] (succ' (v "f" `App` v "y'")))]

add' :: Term
add' = Lam (var "f", Pi (var "x", natT) natT) $ Lam (var "y", natT) $
  Case (v "y") (Lam (var "ignored",natT) natT) $
  fromList [ (var "Zero", CaseTerm [] (v "Zero"))
           -- , (var "Succ", CaseTerm [var "y'"] (succ' (v "f" `App` v "y'")))]
           , (var "Succ", CaseTerm [var "y'"] (v "Zero"))]

{-
fac :: Term
fac = TFix $ Lam (var "f", (Pi (var "x", natT) natT)) $ Lam (var "x", natT) $
  Case (v "x") (v "Nat") $
  fromList [ (var "Zero", CaseTerm [] (succ' zero))
           , (var "Succ", CaseTerm [var "n"] (mul `App` (succ' (v "n")) `App` (v "f" `App` v "x")))
           ]
-}
