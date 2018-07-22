module Term where

import Utils

type Program v = ( [DataDecl v] --Data declarations
                 , [TopLevel v] --Top-level definitions
                 )

type DataDecl v = ( v                       --Datatype name
                  , Term v                  --Type of the datatype
                  , [(Constructor v, Term v)] --Constructor declarations
                  )

type Constructor v = v

type TopLevel v = ( v --Name
                  , Term v    --Body
                  )

type Binding v = (v, Term v)


data Term v = Var v                              --Variable
            | Lam (Binding v) (Term v)           --Lambda var body
            | Pi (Binding v) (Term v)            --Pi var return
            | App (Term v) (Term v)              --Application
            | Ty                                 --Type:Type
            | Let IsRec [(Binding v, Term v)] (Term v) --Let bindings in body
            | Case (Term v) [CaseTerm v]         --Case expr of terms
            deriving (Eq, Show)
type CaseTerm v = (Constructor v, [Binding v], (Term v))

infixl 3 `App`

data IsRec = Rec | NoRec
           deriving (Eq, Show)

maxNesting :: Term v -> Int
maxNesting (Var v) = 0
maxNesting (Lam _ t) = maxNesting t + 1
maxNesting (Pi _ t) = maxNesting t + 1
maxNesting (App a b) = max (maxNesting a) (maxNesting b)
maxNesting Ty = 0
maxNesting (Let _ bindings body) = max (maxNesting body) bindNesting
  where bindNesting = maximumOr 0 $ fmap (maxNesting . snd) bindings
  --Let calculation is wrong: each binding could be nested deeply. But
  --recursive let bindings can't be inlined, so this is good enough without
  --being over-complicated.
maxNesting (Case t branches) = max (maxNesting t) caseNesting
  where caseNesting = maximumOr 0 $ fmap (maxNesting . \(_,_,x)->x) branches

--subst for with in
subst :: Eq v => v -> Term v -> Term v -> Term v
subst v with (Var u) | v == u    = with
                     | otherwise = Var u
subst v with lam@(Lam (u,uTy) body)
  | v == u    = lam --Variable is shadowed
  | otherwise = Lam (u,(subst v with uTy)) (subst v with body)
subst v with pi@(Pi (u,uTy) ret)
  | v == u    = pi --Variable is shadowed
  | otherwise = Pi (u,(subst v with uTy)) (subst v with ret)
subst v with (App a b) = App (subst v with a) (subst v with b)
subst v with Ty = Ty
subst v with lett@(Let rec bindings body)
  | elem v (fst <$> fst <$> bindings) = lett --Variable is shadowed
  | otherwise = Let rec (substBindings <$> bindings) (subst v with body)
  where substBindings = \((u,uTy),val) -> ((u,subst v with uTy), subst v with val)

prettyPrint :: Show v => Term v -> String
prettyPrint (Var v) = show v
prettyPrint (Lam (u,uTy) body) = "\\" <> show u <> ":" <> prettyPrint uTy <> ". (" <> prettyPrint body <> ")"
prettyPrint (Pi (u,uTy) ret) = show u <> ":" <> prettyPrint uTy <> " -> (" <> prettyPrint ret <> ")"
prettyPrint (App a b) = "(" <> prettyPrint a <> ") (" <> prettyPrint b <> ")"
prettyPrint Ty = "Type"
prettyPrint (Let rec bindings body) = pplet rec <> ppbindings <> "in (" <> prettyPrint body <> ")"
  where pplet Rec = "letrec"
        pplet NoRec = "let"
        ppbindings = " bindings "
