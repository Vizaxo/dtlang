module Compiler where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Lens hiding (Context)
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.List
import Data.Tuple
import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as M

import Equality
import Types
import Utils


partiallyApplyCtors :: forall m. MonadReader Context m => Term -> m Term
partiallyApplyCtors = cataM alg where
  alg :: TermF Term -> m Term
  alg (VarF v) = partiallyApplyCtor v
  alg t = pure (embed t)


data ErasedCaseTermF r = ECaseTermF
  { _ectConstructor :: Constructor
  , _ectBindings :: [Name]
  , _ectExpression :: r
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)
makeLenses ''ErasedCaseTermF

-- | Terms but with types erased
data ErasedTerm
  = EVar Name
  | ECtor Constructor [ErasedTerm]
  | ELam Name ErasedTerm
  | EApp ErasedTerm ErasedTerm
  | ECase ErasedTerm [ErasedCaseTermF ErasedTerm]
  | EErasedType
  deriving Show
makeBaseFunctor ''ErasedTerm

-- | Erase types ready for compilation
-- TODO: also erase lambdas where the argument is a type
eraseTypes :: Term -> ErasedTerm
eraseTypes = cata alg where
  alg :: TermF ErasedTerm -> ErasedTerm
  alg (VarF n) = EVar n
  alg (CtorF ctor rs) = ECtor ctor rs
  alg (LamF var body) = ELam (eraseTypesBinding var) body
  alg (PiF _ _) = EErasedType
  alg (AppF a b) = EApp a b
  alg (TyF n) = EErasedType
  alg (CaseF e terms) = ECase e (eraseTypesCase <$> terms)

  eraseTypesCase (CaseTerm ctor bindings e)
    = ECaseTermF ctor (eraseTypesBinding <$> bindings) e

  eraseTypesBinding (name, ty) = name


data FunctionName = FunctionName Name
  deriving (Eq, Show)

data LamLiftedTerm
  = LLVar Name
  | LLEnvRef Int
  | LLCtor Constructor [LamLiftedTerm]
  | LLMkClosure FunctionName [Name]
  | LLApp LamLiftedTerm LamLiftedTerm
  | LLCase LamLiftedTerm [ErasedCaseTermF LamLiftedTerm]
  | LLErasedType
  deriving Show
makeBaseFunctor ''LamLiftedTerm

freeVarsLL :: LamLiftedTerm -> [Name]
freeVarsLL = cata alg where
  alg :: LamLiftedTermF [Name] -> [Name]
  alg (LLVarF v) = [v]
  alg (LLEnvRefF i) = []
  alg (LLCtorF c args) = concat args
  alg (LLMkClosureF f frees) = frees
  alg (LLAppF f xs) = f ++ xs
  alg (LLCaseF e terms) = e ++ (concatMap freeVarsCaseTermE terms)
  alg LLErasedTypeF = []

  freeVarsCaseTermE :: ErasedCaseTermF [Name] -> [Name]
  freeVarsCaseTermE (ECaseTermF _ bindings expr) = expr \\ bindings

data Function t = Function
  { name :: FunctionName
  , arg :: Name
  , env :: [Name]
  , body :: t
  }
  deriving (Show, Functor, Foldable, Traversable)

data TermAndFunctions r = TermAndFunctions
  { _term :: r
  , _funs :: [Function r]
  }
  deriving (Show, Functor, Foldable, Traversable)
makeLenses ''TermAndFunctions

type LamLifted = TermAndFunctions LamLiftedTerm

freshName :: MonadState GenVar m => String -> m Name
freshName custom = do
  name <- get
  modify (\(GenVar i) -> GenVar (i+1))
  pure $ Generated custom name

freshFnName :: MonadState GenVar m => String -> m FunctionName
freshFnName f = FunctionName <$> freshName f

lambdaLift :: MonadState GenVar m => ErasedTerm -> m LamLifted
lambdaLift = fmap (uncurry TermAndFunctions) . runWriterT . cataM alg where
  alg :: (MonadWriter [Function LamLiftedTerm] m, MonadState GenVar m)
    => Base ErasedTerm LamLiftedTerm -> m LamLiftedTerm
  alg (EVarF n) = pure (LLVar n)
  alg (ECtorF ctor args) = pure (LLCtor ctor args)
  alg (ELamF arg body) = do
    name <- freshFnName "lambda"
    let frees = freeVarsLL body \\ [arg]
    tell [Function name arg frees (mkEnvRefs frees body)]
    return (LLMkClosure name frees)
  alg (EAppF f x) = pure (LLApp f x)
  alg (ECaseF e terms) = pure (LLCase e terms)
  alg EErasedTypeF = pure LLErasedType

  mkEnvRefs :: [Name] -> LamLiftedTerm -> LamLiftedTerm
  mkEnvRefs env = cata alg' where
    alg' (LLVarF n) = case elemIndex n env of
      Nothing -> LLVar n
      Just i -> LLEnvRef i
    alg' t = embed t


data Tag = Tag Int
  deriving (Eq, Ord, Show)

data TaggedDataTerm
  = TDVar Name
  | TDEnvRef Int
  | TDUnit
  | TDTaggedUnionExpr Tag [TaggedDataTerm]
  | TDMkClosure FunctionName [Name]
  | TDApp TaggedDataTerm TaggedDataTerm
  | TDCase TaggedDataTerm (Map Tag ([Name], TaggedDataTerm))
  | TDLet [(Name, TaggedDataTerm)] TaggedDataTerm
  deriving Show
makeBaseFunctor ''TaggedDataTerm

type TaggedData = TermAndFunctions TaggedDataTerm

data TaggedDataError
  = TDCtorNotFound Constructor
  deriving Show

toTaggedData :: forall m.
  (MonadReader Context m, MonadError TaggedDataError m, MonadState GenVar m)
  => LamLifted -> m TaggedData
toTaggedData = mapM (cataM alg) where
  alg :: Base LamLiftedTerm TaggedDataTerm -> m TaggedDataTerm
  alg (LLVarF n) = pure $ TDVar n
  alg (LLEnvRefF i) = pure $ TDEnvRef i
  alg (LLCtorF c args) = TDTaggedUnionExpr <$> getCtorTag c <*> pure args
  alg (LLMkClosureF f env) = pure (TDMkClosure f env)
  alg (LLAppF f arg) = pure (TDApp f arg)
  alg (LLCaseF e cases) = do
    cases' <- mapM convertCase cases
    pure (TDCase e (M.fromList cases'))
  alg LLErasedTypeF = pure TDUnit

  convertCase :: ErasedCaseTermF TaggedDataTerm
    -> m (Tag, ([Name], TaggedDataTerm))
  convertCase (ECaseTermF ctor bs e) = (, (bs, e)) <$> getCtorTag ctor

getCtorTag :: (MonadReader Context m, MonadError TaggedDataError m)
  => Constructor -> m Tag
getCtorTag c = do
  datas <- datatypes <$> ask
  Tag <$> maybe
    (throwError (TDCtorNotFound c))
    pure
    (listToMaybe $ catMaybes (ctorIndex <$> datas))
  where
    ctorIndex :: DataDecl -> Maybe Int
    ctorIndex (DataDecl _ _ ((fst <$>) -> ctors))
      = elemIndex c ctors


data ASMType
  = Void
  | Closure
  | TaggedUnion
  | Ptr ASMType
  deriving Show
makeBaseFunctor ''ASMType

data HighLevelAsmExpr
  = HLAEVar Name
  | HLAEEnvRef Int
  | HLAEUnit
  | HLAETaggedUnionExpr Tag Name
  | HLAEMkClosure FunctionName Name
  | HLAEApp HighLevelAsmExpr HighLevelAsmExpr
  | HLAEIndexInto HighLevelAsmExpr Int
  | HLAEStructMember HighLevelAsmExpr String
  | HLAEMalloc ASMType Int
  deriving Show
makeBaseFunctor ''HighLevelAsmExpr

data HighLevelAsmStmt
  = HLASAssign Name HighLevelAsmExpr
  | HLASAssignArr Name Int HighLevelAsmExpr
  | HLASDeclare ASMType Name
  | HLASDeclareArr ASMType Name Int
  | HLASDeclareAssign ASMType Name HighLevelAsmExpr
  | HLASNop
  | HLASExpr HighLevelAsmExpr
  | HLASSwitch HighLevelAsmExpr (Map Tag HighLevelAsmStmt)
  | HLASBlock [HighLevelAsmStmt]
  deriving Show
makeBaseFunctor ''HighLevelAsmStmt

instance Semigroup HighLevelAsmStmt where
   a <> HLASNop = a
   HLASNop <> b = b
   (HLASBlock as) <> (HLASBlock bs) = HLASBlock (as <> bs)
   (HLASBlock as) <> b = HLASBlock (as <> [b])
   a <> (HLASBlock bs) = HLASBlock (a:bs)
   a <> b = HLASBlock [a,b]
instance Monoid HighLevelAsmStmt where
  mempty = HLASNop
  mappend = (<>)

type HighLevelAsm = TermAndFunctions (HighLevelAsmStmt, HighLevelAsmExpr)

toHLA :: MonadState GenVar m => TaggedData -> m HighLevelAsm
toHLA = mapM (fmap swap . cataM alg) where
  alg :: MonadState GenVar m
    => Base TaggedDataTerm (HighLevelAsmExpr, HighLevelAsmStmt)
    -> m (HighLevelAsmExpr, HighLevelAsmStmt)
  alg (TDVarF n) = pure $ (HLAEVar n, HLASNop)
  alg (TDEnvRefF i) = pure $ (HLAEEnvRef i, HLASNop)
  alg (TDTaggedUnionExprF t (unzip->(args, argStmts))) = do
    arr <- freshName "tagged_union_arr"
    tu <- freshName "tagged_union"
    let stmts = mconcat argStmts
          <> HLASDeclareArr (Ptr Void) arr (length args)
          <> mconcat (uncurry (HLASAssignArr arr) <$> zip [0..] args)
          <> HLASDeclareAssign (Ptr TaggedUnion) tu (HLAEMalloc TaggedUnion 1)
          <> HLASAssignArr tu 0 (HLAETaggedUnionExpr t arr)
    pure $ (HLAEVar tu, stmts)
  alg (TDMkClosureF f env) = do
    closure <- freshName "closure"
    envVar <- freshName "closure_env"
    let s = [HLASDeclareAssign (Ptr $ Ptr Void) envVar
            (HLAEMalloc (Ptr Void) (length env))]
          <> ((\(v, i) -> HLASAssignArr envVar i (HLAEVar v)) <$> zip env [0..])
          <> [ HLASDeclareAssign (Ptr Closure) closure (HLAEMalloc Closure 1)
             , HLASAssignArr closure 0 (HLAEMkClosure f envVar)]
    pure (HLAEVar closure, HLASBlock s)
  alg (TDAppF (f,s) (arg,s')) = pure (HLAEApp f arg, s <> s')
  alg (TDCaseF (scrutinee, s) cases) = do
    v <- freshName "case_ret"
    let mkCase (bindings, (expr,s')) = mconcat $
          mkBindings bindings scrutinee <> [s', HLASAssign v expr]
    let stmt = s
          <> HLASDeclare (Ptr Void) v
          <> HLASSwitch (HLAEStructMember scrutinee "tag") (mkCase <$> cases)
    pure $ (HLAEVar v, stmt)
  alg (TDLetF bs (t, s)) = do
    let assigns
          = (\(name,(e,s)) -> s <> HLASDeclareAssign (Ptr Void) name e) <$> bs
    pure (t, mconcat assigns <> s)
  alg (TDUnitF) = pure (HLAEUnit, HLASNop)

  mkBindings :: [Name] -> HighLevelAsmExpr -> [HighLevelAsmStmt]
  mkBindings bindings expr
    = (\(name, i) -> HLASDeclareAssign (Ptr Void) name
        (HLAEIndexInto (HLAEStructMember expr "data") i))
      <$> zip bindings [0..]


toC :: HighLevelAsm -> String
toC (TermAndFunctions t fs)
  = headers
  <> "\n" <> mkTaggedUnionStruct <> "\n" <> mkClosureStruct
  <> "\n" <> mkClosureCallFn
  <> "\n" <> decls
  <> "\n" <> intercalate "\n" (mkMain : (mkCFunction <$> fs))
  where
    decls = concatMap declareCFunction fs

    mkMain = cFunction "main" [] $
      toCStmt (fst t)
      <> "printf(\"%d\\n\", ((taggedunion*)" <> toCExpr (snd t) <> ")->tag);\n"

    headers = intercalate "\n" $ ("#include " <>) <$> ["<stdio.h>", "<stdlib.h>"]

mkCFunction :: Function (HighLevelAsmStmt, HighLevelAsmExpr) -> String
mkCFunction (Function name arg _ (HLASNop, ret))
  = cFunction (toCFnName name)
    [(Ptr Void, toCName arg), (Ptr (Ptr Void), "env")]
    ("return " <> toCExpr ret <> ";\n")
mkCFunction (Function name arg _ (body, ret))
  = cFunction (toCFnName name)
    [(Ptr Void, toCName arg), (Ptr (Ptr Void), "env")]
    (toCStmt body <> "return " <> toCExpr ret <> ";\n")

toCStmt :: HighLevelAsmStmt -> String
toCStmt = cata alg where
  alg (HLASAssignF n e)
    = toCName n <> " = " <> toCExpr e <> ";\n"
  alg (HLASAssignArrF n i e)
    = toCName n <> "[" <> show i <> "] = " <> toCExpr e <> ";\n"
  alg (HLASDeclareF t n)
    = toCType t <> " " <> toCName n <> ";\n"
  alg (HLASDeclareArrF t n i)
    = toCType t <> " " <> toCName n <> "[" <> show i <> "];\n"
  alg (HLASDeclareAssignF t n e)
    = toCType t <> " " <> toCName n <> " = " <> toCExpr e <> ";\n"
  alg HLASNopF
    = ";\n"
  alg (HLASBlockF ss)
    = concat ss
  alg (HLASExprF e)
    = toCExpr e <> ";\n"
  alg (HLASSwitchF n cases)
    = "switch (" <> toCExpr n <> ") {\n"
    <> concat (toCCase <$> M.toList cases) <> "}\n"

  toCCase :: (Tag, String) -> String
  toCCase (Tag t, s)
    = "case " <> show t <> ":\n{\n" <> s <> "break;\n}\n"

toCExpr :: HighLevelAsmExpr -> String
toCExpr = cata alg where
  alg (HLAEVarF n)
    = toCName n
  alg (HLAEEnvRefF i)
    = "env[" <> show i <> "]"
  alg HLAEUnitF
    = "NULL"
  alg (HLAETaggedUnionExprF (Tag tag) arr)
    = "(taggedunion){.tag = " <> show tag <> ", .data = " <> toCName arr <> "}"
  alg (HLAEMkClosureF f env)
    = "(closure){.f = " <> toCFnName f <> ", .env = " <> toCName env <> "}"
  alg (HLAEAppF f x)
    = "closure_call(" <> f <> ", " <> x <> ")"
  alg (HLAEIndexIntoF e i)
    = "((taggedunion**)" <> e <> ")[" <> show i <> "]"
  alg (HLAEStructMemberF e member)
    = "((taggedunion*)" <> e <> ")->" <> member
  alg (HLAEMallocF t size)
    = "malloc(sizeof(" <> toCType t <> ") * " <> show size <> ")"

declareCFunction :: Function (HighLevelAsmStmt, HighLevelAsmExpr) -> String
declareCFunction (Function name arg _ (body, ret))
  = cFunDecl (toCFnName name) [(Ptr Void, toCName arg), (Ptr (Ptr Void), "env")]

cFunction :: String -> [(ASMType, String)] -> String -> String
cFunction name params body
  = "void* " <> name <> "(" <> mkParams params <> ") {\n" <> body <> "}\n"

cFunDecl :: String -> [(ASMType, String)] -> String
cFunDecl name params = "void* " <> name <> "(" <> mkParams params <> ");\n"

mkParams :: [(ASMType, String)] -> String
mkParams = intercalate ", " . fmap (\(t, v) -> toCType t <> " " <> v)

toCName :: Name -> String
toCName (Specified n) = "user_" <> n
toCName (Generated c (GenVar n)) = c <> "_" <> show n

toCFnName :: FunctionName -> String
toCFnName (FunctionName n) = "fn_" <> toCName n

toCType :: ASMType -> String
toCType = cata alg where
  alg :: Base ASMType String -> String
  alg VoidF = "void"
  alg ClosureF = "closure"
  alg TaggedUnionF = "taggedunion"
  alg (PtrF t) = t <> "*"

mkTaggedUnionStruct :: String
mkTaggedUnionStruct
  = "typedef struct {\n\tint tag;\n\tvoid* data;\n} taggedunion;\n"

mkClosureStruct :: String
mkClosureStruct
  = "typedef struct {\n\tvoid* (*f)(void*, void**);\n\tvoid** env;\n} closure;\n"

mkClosureCallFn :: String
mkClosureCallFn
  = "void* closure_call(closure* f, void* arg)"
  <> "{\n\treturn (f->f)(arg, f->env);\n}\n"


data CompilerError
  = CTDError TaggedDataError
  deriving Show

compileToC :: MonadError CompilerError m => Context -> Term -> m String
compileToC ctx = flip evalStateT (GenVar 0) . flip runReaderT ctx
  . fmap toC
  . (toHLA <=< (withError CTDError . toTaggedData)
     <=< lambdaLift <=< fmap eraseTypes)
  . partiallyApplyCtors
