module Types where

import Utils
import Data.Natural

-- | A program is a list of top-level definitions and data declarations
type Program = [TopLevel]

data TopLevel
  = TLData DataDecl
  | TLDef Definition
  deriving (Eq, Show)

-- | A data declaration has a name, a type, and a list of constructors.
--   Each constructor has an associated type.
data DataDecl = DataDecl
  { name :: Name                          -- ^Datatype name
  , ty :: Type                            -- ^Type of the datatype
  , constructors :: [(Constructor, Type)] -- ^Constructor declarations
  }
  deriving (Eq, Show)

-- | A constructor is a name.
type Constructor = Name

-- | A top-level definition is a name and a body.
data Definition = Definition
  { defName :: Name
  , defType :: Term
  , defBody :: Term
  }
  deriving (Eq, Show)

-- | A binding of a variable to a type.
type Binding = (Name, Term)


-- | The term datatype for the language, parameterised by the type of
--   its variables.
data Term = Var Name                         -- ^Variable
          | Ctor Constructor [Term]          -- ^Fully applied constructor
          | Lam Binding Term                 -- ^Lambda var body
          | Pi Binding Term                  -- ^Pi var return
          | App Term Term                    -- ^Application
          | Ty Natural                       -- ^Type universes
          | Case Term [CaseTerm]             -- ^Case expr of terms
          deriving (Eq, Show)

ty --> res = Pi ty res
infixr 5 -->
infixl 5 `App`

data CaseTerm = CaseTerm
  { ctConstructor :: Constructor
  , ctBindings :: [Binding]
  , ctExpression :: Term
  }
  deriving (Eq, Show)

-- | @Type@ is just a synonym for @Term@, allowing slightly more
-- informative documentation where needed.
type Type = Term

-- | A map from variables to their types.
data Context = Context
  { getCtx :: [(Name, Term)]
  , datatypes :: [DataDecl]
  }
  deriving (Eq, Show)

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
