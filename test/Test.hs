module Main where

import Term

import Test.Interpreter
import Test.TypeCheck

import Test.QuickCheck

main :: IO ()
main = do
  quickCheck testGenWellTyped
  quickCheck testIdPreservesType
  quickCheck testIdReturnsArg
  quickCheck testWellTypedInterpretsRight

qcRegressionTests :: [Term Char]
qcRegressionTests
  = [ Lam ('a',Ty) (Lam ('b',Let Rec [(('b',Ty),Var 'b')] (Var 'b')) (Lam ('c',Var 'a') (Var 'c')))
    , Lam ('a',Let NoRec [] Ty) (Lam ('b',Ty) (Var 'a'))
    , Lam ('a',Let Rec [(('a',Ty),Var 'a'),(('b',Ty),Ty)] (Var 'b')) (Lam ('b',Ty) (Var 'a'))
    , Lam ('a',Ty) (Lam ('b',Let Rec [(('b',Var 'a'),Var 'b'),(('c',Var 'a'),Var 'c')] (Var 'a')) (Lam ('c',Var 'a') Ty))
    , Lam ('a',App (Lam ('a',Ty) (Var 'a')) (Let Rec [(('a',Ty),Var 'a'),(('b',Var 'a'),Var 'b')] (Var 'b'))) (Lam ('b',Ty) (Lam ('c',Ty) (Var 'c')))
    , Lam ('a',App (Lam ('a',Ty) (Var 'a')) (Let Rec [(('a',Ty),Var 'b'),(('b',Var 'a'),Var 'a')] (Var 'b'))) (Lam ('b',Ty) (Lam ('c',Var 'b') (Var 'b')))
    , Lam ('a',Ty) (Lam ('b',Let Rec [(('b',Var 'a'),Var 'a')] (Var 'b')) (Pi ('c',Ty) (Var 'c')))
    ]
