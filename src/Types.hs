module Types where

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
            | Let [(Binding v, Term v)] (Term v) --Let bindings in body
            | Case (Term v) [CaseTerm v]         --Case expr of terms
            deriving (Eq, Show)
type CaseTerm v = (Constructor v, [Binding v], (Term v))

maxNesting :: Term v -> Int
maxNesting (Var v) = 0
maxNesting (Lam _ t) = maxNesting t + 1
maxNesting (Pi _ t) = maxNesting t + 1
maxNesting (App a b) = max (maxNesting a) (maxNesting b)
maxNesting Ty = 0
