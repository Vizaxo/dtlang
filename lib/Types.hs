{-# LANGUAGE TemplateHaskell #-}
module Types where

import Data.Functor.Foldable.TH
import Data.Map
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
  , constructors :: Map Constructor Type -- ^Constructor declarations
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

data BTree a = Node (BTree a) (BTree a) | Leaf a
  deriving (Eq, Show, Functor, Foldable)

data CaseTermF r = CaseTerm
  { ctBindings :: [Name]
  , ctExpression :: r
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)

type CaseTerm = CaseTermF Term

data Name = Specified String
          | Generated String GenVar
          deriving (Eq, Ord, Show)

newtype GenVar = GenVar Int
  deriving (Eq, Ord, Show, Enum)

-- | @Type@ is just a synonym for @Term@, allowing slightly more
-- informative documentation where needed.
type Type = Term

ty --> res = Pi ty res
infixr 5 -->
infixl 5 `App`

-- | The term datatype for the language, parameterised by the type of
--   its variables.
data Term
  = Var Name                   -- ^Variable
  | Ctor Constructor [Term]    -- ^Fully applied constructor
  | Lam (BindingF Term) Term   -- ^Lambda var body
  | Pi (BindingF Term) Term    -- ^Pi var return
  | App Term Term              -- ^Application
  | Ty Natural                 -- ^Type universes
  | Case Term Type (Map Constructor CaseTerm)  -- ^Case expr, at type, of terms
  | TFix Term                  -- ^Fixed-point combinator
  deriving (Eq, Show)
makeBaseFunctor ''Term

type Binding = BindingF Term

-- | A map from variables to their types.
data Context = Context
  { getCtx :: [(Name, Type)]
  , getEnv :: [(Name, Term)]
  , datatypes :: [DataDecl]
  }

instance Enum Name where
  toEnum = Generated "" . toEnum

  fromEnum (Generated c a) = fromEnum a
  -- Probably not a great enum instance due to this case, but very useful
  fromEnum (Specified str) = -1


deriving instance Eq TopLevel
deriving instance Show TopLevel

deriving instance Eq Definition
deriving instance Show Definition

deriving instance Eq Context
deriving instance Show Context

deriving instance Eq DataDecl
deriving instance Show DataDecl

deriving instance Show a => Show (TermF a)

deriveShow1 ''CaseTermF
deriveShow1 ''TermF
