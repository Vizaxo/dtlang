module Types where

import Utils

-- | A program is a list of data declarations, and top-level definitions.
type Program = ( [DataDecl] -- ^Data declarations
               , [TopLevel] -- ^Top-level definitions
               )

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
type TopLevel = ( Name -- ^Name
                , Term -- ^Body
                )

-- | A binding of a variable to a type.
type Binding = (Name, Term)


-- | The term datatype for the language, parameterised by the type of
--   its variables.
data Term = Var Name                         -- ^Variable
          | Ctor Constructor [Term]          -- ^Fully applied constructor
          | Lam Binding Term                 -- ^Lambda var body
          | Pi Binding Term                  -- ^Pi var return
          | App Term Term                    -- ^Application
          | Ty                               -- ^Type:Type
          | Let IsRec [(Binding, Term)] Term -- ^Let bindings in body
          | Case Term [CaseTerm]             -- ^Case expr of terms
          deriving (Eq, Show)

ty --> res = Pi ty res
infixr 5 -->
infixl 5 `App`

data CaseTerm = CaseTerm
  { constructor :: Constructor
  , bindings :: [Binding]
  , expression :: Term
  }
  deriving (Eq, Show)

-- | 'Type' is a synonym for 'Term', which can have its own
-- 'Arbitrary' implementation.
newtype Type = Type { unType :: Term }
  deriving (Eq, Show)

-- | Determines whether a let(rec) expression is a let or a letrec.
data IsRec = Rec | NoRec
           deriving (Eq, Show)

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
