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
            | Ty Int                             --Type universes
            | Let [(Binding v, Term v)] (Term v) --Let bindings in body
            | Case (Term v) [CaseTerm v]         --Case expr of terms
            deriving (Eq, Show)
type CaseTerm v = (Constructor v, [Binding v], (Term v))
