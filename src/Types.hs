{-# LANGUAGE TemplateHaskell #-}

module Types where

import Utils

import Data.Eq.Deriving
import Data.Functor.Foldable
import Data.Natural
import Text.Show.Deriving

-- | A program is a list of top-level definitions and data declarations
type Program = [TopLevel]

data TopLevel
  = TLData DataDecl
  | TLDef Definition

-- | A data declaration has a name, a type, and a list of constructors.
--   Each constructor has an associated type.
data DataDecl = DataDecl
  { name :: Name                          -- ^Datatype name
  , ty :: Type                            -- ^Type of the datatype
  , constructors :: [(Constructor, Type)] -- ^Constructor declarations
  }

-- | A constructor is a name.
type Constructor = Name

-- | A top-level definition is a name and a body.
data Definition = Definition
  { defName :: Name
  , defType :: Term
  , defBody :: Term
  }

-- | A binding of a variable to a type.
type BindingF r = (Name, r)


-- | The term datatype for the language, parameterised by the type of
--   its variables.
data TermF r
  = VarF Name                       -- ^Variable
  | CtorF Constructor [r]           -- ^Fully applied constructor
  | LamF (BindingF r) r                  -- ^Lambda var body
  | PiF (BindingF r) r                   -- ^Pi var return
  | AppF r r                        -- ^Application
  | TyF Natural                     -- ^Type universes
  | CaseF r [CaseTermF r]              -- ^Case expr of terms
  deriving (Eq, Show, Functor)

type Term = Fix TermF

pattern Var n = Fix (VarF n)
pattern Ctor c es = Fix (CtorF c es)
pattern Lam bind e = Fix (LamF bind e)
pattern Pi bind e = Fix (PiF bind e)
pattern App a b = Fix (AppF a b)
pattern Ty n = Fix (TyF n)
pattern Case e ts = Fix (CaseF e ts)

type Binding = BindingF Term

ty --> res = Pi ty res
infixr 5 -->
infixl 5 `App`

data CaseTermF r = CaseTerm
  { ctConstructor :: Constructor
  , ctBindings :: [BindingF r]
  , ctExpression :: r
  }
  deriving (Eq, Show, Functor)

type CaseTerm = CaseTermF Term

-- | @Type@ is just a synonym for @Term@, allowing slightly more
-- informative documentation where needed.
type Type = Term

-- | A map from variables to their types.
data Context = Context
  { getCtx :: [(Name, Type)]
  , getEnv :: [(Name, Term)]
  , datatypes :: [DataDecl]
  }

newtype GenVar = GenVar Int
  deriving (Eq, Ord, Show, Enum)

data Name = Specified String
          | Generated GenVar
          deriving (Eq, Ord, Show)

instance Enum Name where
  toEnum = Generated . toEnum

  fromEnum (Generated a) = fromEnum a
  -- Probably not a great enum instance due to this case, but very useful
  fromEnum (Specified str) = -1


$(deriveEq1 ''TermF)
$(deriveEq1 ''CaseTermF)

$(deriveShow1 ''TermF)
$(deriveShow1 ''CaseTermF)

deriving instance Eq TopLevel
deriving instance Show TopLevel

deriving instance Eq Definition
deriving instance Show Definition

deriving instance Eq Context
deriving instance Show Context

deriving instance Eq DataDecl
deriving instance Show DataDecl
