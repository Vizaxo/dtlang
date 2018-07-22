module Main where

import Term

import Test.Interpreter
import Test.TypeCheck

import Test.QuickCheck

main :: IO ()
main = do
  quickCheck (prop_idReturnsArg @Int)
  quickCheck (prop_wellTypedInterpretsRight @Int)

  quickCheck (prop_genWellTyped @Int)
  quickCheck (prop_idPreservesType @Int)


qcRegressionTests :: [Term Char]
qcRegressionTests
  = [ Lam ('a',Ty) (Lam ('b',Let Rec [(('b',Ty),Var 'b')] (Var 'b')) (Lam ('c',Var 'a') (Var 'c')))
    , Lam ('a',Let NoRec [] Ty) (Lam ('b',Ty) (Var 'a'))
    , Lam ('a',Let Rec [(('a',Ty),Var 'a'),(('b',Ty),Ty)] (Var 'b')) (Lam ('b',Ty) (Var 'a'))
    , Lam ('a',Ty) (Lam ('b',Let Rec [(('b',Var 'a'),Var 'b'),(('c',Var 'a'),Var 'c')] (Var 'a')) (Lam ('c',Var 'a') Ty))
    , Lam ('a',App (Lam ('a',Ty) (Var 'a')) (Let Rec [(('a',Ty),Var 'a'),(('b',Var 'a'),Var 'b')] (Var 'b'))) (Lam ('b',Ty) (Lam ('c',Ty) (Var 'c')))
    , Lam ('a',App (Lam ('a',Ty) (Var 'a')) (Let Rec [(('a',Ty),Var 'b'),(('b',Var 'a'),Var 'a')] (Var 'b'))) (Lam ('b',Ty) (Lam ('c',Var 'b') (Var 'b')))
    , Lam ('a',Ty) (Lam ('b',Let Rec [(('b',Var 'a'),Var 'a')] (Var 'b')) (Pi ('c',Ty) (Var 'c')))
    , Let NoRec [(('b',Var 'a'),Pi ('a',Ty) (Var 'a'))] (Var 'b')
    , Let Rec [(('a',Ty),Var 'a'),(('b',Lam ('b',Var 'a') (Var 'b')),Var 'b')] (Var 'b')
    , Let Rec [(('a',Lam ('a',Ty) (Var 'a')),Var 'b'),(('b',Var 'a'),Var 'b')] (Var 'a')
    , Let Rec [(('a',Ty),Var 'a'),(('b',Var 'a'),Var 'a'),(('c',Var 'a'),Var 'a')] (Var 'b')
    , App (Lam ('a',Ty) (Var 'a')) Ty
    , Let NoRec [(('a',Ty),Ty)] (Lam ('b',Var 'a') (Var 'a'))
    , Lam ('a',App (Lam ('a',Ty) (App (Lam ('b',Var 'a') (Let Rec [(('c',Ty),Ty)] (Var 'b'))) (Var 'a'))) Ty) Ty
    ]

qcGenerated :: [Term Char]
qcGenerated = [Let Rec [(('a',Lam ('a',Let Rec [] (App (App (App (Let NoRec [(('b',Var 'a'),App (Pi ('a',Lam ('a',Pi ('a',Let NoRec [(('b',Var 'a'),Lam ('a',App (Pi ('a',App (Lam ('a',Let NoRec [(('b',Var 'a'),Lam ('a',Ty) (Var 'a'))] (Var 'a')) (Var 'a')) (Pi ('b',Var 'a') (Var 'a'))) Ty) (Var 'a')) (Var 'a'))] (Lam ('c',Ty) (Var 'b'))) (Var 'a')) (App (Var 'a') (Var 'a'))) (Var 'a')) (App (Var 'a') (Var 'a'))),(('c',App (Lam ('c',App (Let NoRec [] (Var 'a')) (Var 'a')) (Var 'c')) (Var 'c')),Var 'a')] (Var 'a')) (Var 'c')) (Var 'a')) (Lam ('d',Var 'c') (Var 'c')))) (Var 'a')),Var 'a')] (Var 'a')
              ]
