module Main where

import Equality
import Term
import Types

import Test.BackTrackGen
import Test.Interpreter
import Test.TypeCheck

import Test.QuickCheck

main :: IO ()
main = do
  quickCheck prop_idReturnsArg
  quickCheck prop_wellTypedWhnfSucceeds
  quickCheck prop_pairFstReturnsArg
  quickCheck prop_pairSndReturnsArg
  quickCheck prop_etaExpansion

  quickCheck prop_genWellTyped
  quickCheck prop_idPreservesType
  quickCheck prop_pairFstPreservesType
  quickCheck prop_pairSndPreservesType
  quickCheck prop_etaExpansionType

  quickCheck prop_alphaEqId

  quickCheck prop_backtracks

qcRegressionTests :: [Term]
qcRegressionTests
  = [ Lam ((toEnum 0),Ty) (Lam ((toEnum 1),Let Rec [(((toEnum 1),Ty),Var (toEnum 1))] (Var (toEnum 1))) (Lam ((toEnum 2),Var (toEnum 0)) (Var (toEnum 2))))
    , Lam ((toEnum 0),Let NoRec [] Ty) (Lam ((toEnum 1),Ty) (Var (toEnum 0)))
    , Lam ((toEnum 0),Let Rec [(((toEnum 0),Ty),Var (toEnum 0)),(((toEnum 1),Ty),Ty)] (Var (toEnum 1))) (Lam ((toEnum 1),Ty) (Var (toEnum 0)))
    , Lam ((toEnum 0),Ty) (Lam ((toEnum 1),Let Rec [(((toEnum 1),Var (toEnum 0)),Var (toEnum 1)),(((toEnum 2),Var (toEnum 0)),Var (toEnum 2))] (Var (toEnum 0))) (Lam ((toEnum 2),Var (toEnum 0)) Ty))
    , Lam ((toEnum 0),App (Lam ((toEnum 0),Ty) (Var (toEnum 0))) (Let Rec [(((toEnum 0),Ty),Var (toEnum 0)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 1))] (Var (toEnum 1)))) (Lam ((toEnum 1),Ty) (Lam ((toEnum 2),Ty) (Var (toEnum 2))))
    , Lam ((toEnum 0),App (Lam ((toEnum 0),Ty) (Var (toEnum 0))) (Let Rec [(((toEnum 0),Ty),Var (toEnum 1)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 0))] (Var (toEnum 1)))) (Lam ((toEnum 1),Ty) (Lam ((toEnum 2),Var (toEnum 1)) (Var (toEnum 1))))
    , Lam ((toEnum 0),Ty) (Lam ((toEnum 1),Let Rec [(((toEnum 1),Var (toEnum 0)),Var (toEnum 0))] (Var (toEnum 1))) (Pi ((toEnum 2),Ty) (Var (toEnum 2))))
    , Let NoRec [(((toEnum 1),Var (toEnum 0)),Pi ((toEnum 0),Ty) (Var (toEnum 0)))] (Var (toEnum 1))
    , Let Rec [(((toEnum 0),Ty),Var (toEnum 0)),(((toEnum 1),Lam ((toEnum 1),Var (toEnum 0)) (Var (toEnum 1))),Var (toEnum 1))] (Var (toEnum 1))
    , Let Rec [(((toEnum 0),Lam ((toEnum 0),Ty) (Var (toEnum 0))),Var (toEnum 1)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 1))] (Var (toEnum 0))
    , Let Rec [(((toEnum 0),Ty),Var (toEnum 0)),(((toEnum 1),Var (toEnum 0)),Var (toEnum 0)),(((toEnum 2),Var (toEnum 0)),Var (toEnum 0))] (Var (toEnum 1))
    , App (Lam ((toEnum 0),Ty) (Var (toEnum 0))) Ty
    , Let NoRec [(((toEnum 0),Ty),Ty)] (Lam ((toEnum 1),Var (toEnum 0)) (Var (toEnum 0)))
    , Lam ((toEnum 0),App (Lam ((toEnum 0),Ty) (App (Lam ((toEnum 1),Var (toEnum 0)) (Let Rec [(((toEnum 2),Ty),Ty)] (Var (toEnum 1)))) (Var (toEnum 0)))) Ty) Ty
    ]

qcGenerated :: [Term]
qcGenerated = [Let Rec [(((toEnum 0),Lam ((toEnum 0),Let Rec [] (App (App (App (Let NoRec [(((toEnum 1),Var (toEnum 0)),App (Pi ((toEnum 0),Lam ((toEnum 0),Pi ((toEnum 0),Let NoRec [(((toEnum 1),Var (toEnum 0)),Lam ((toEnum 0),App (Pi ((toEnum 0),App (Lam ((toEnum 0),Let NoRec [(((toEnum 1),Var (toEnum 0)),Lam ((toEnum 0),Ty) (Var (toEnum 0)))] (Var (toEnum 0))) (Var (toEnum 0))) (Pi ((toEnum 1),Var (toEnum 0)) (Var (toEnum 0)))) Ty) (Var (toEnum 0))) (Var (toEnum 0)))] (Lam ((toEnum 2),Ty) (Var (toEnum 1)))) (Var (toEnum 0))) (App (Var (toEnum 0)) (Var (toEnum 0)))) (Var (toEnum 0))) (App (Var (toEnum 0)) (Var (toEnum 0)))),(((toEnum 2),App (Lam ((toEnum 2),App (Let NoRec [] (Var (toEnum 0))) (Var (toEnum 0))) (Var (toEnum 2))) (Var (toEnum 2))),Var (toEnum 0))] (Var (toEnum 0))) (Var (toEnum 2))) (Var (toEnum 0))) (Lam ((toEnum 3),Var (toEnum 2)) (Var (toEnum 2))))) (Var (toEnum 0))),Var (toEnum 0))] (Var (toEnum 0))
              ]
