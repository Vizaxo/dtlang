module Compiler where

import Control.Comonad.Cofree (Cofree)
import Control.Comonad.Trans.Cofree (CofreeF ((:<)))
import Control.Lens hiding (Context, (:<))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Either
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.List
import Data.Map (keys, assocs, Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Tuple

import Types
import TC
import Utils


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
eraseTypes :: Cofree TermF Type -> ErasedTerm
eraseTypes = cata alg where
  alg (Ty _ :< _) =  EErasedType
  alg (_ :< VarF n) =  EVar n
  alg (_ :< CtorF ctor rs) =  ECtor ctor rs
  alg (_ :< LamF var body) =  ELam (eraseTypesBinding var) body
  alg (_ :< PiF _ _) = EErasedType
  alg (_ :< AppF a b) = EApp a b
  alg (_ :< TyF n) = EErasedType
  alg (_ :< CaseF e _ terms) =  ECase e (eraseTypesCase <$> assocs terms)

  eraseTypesCase (ctor, (CaseTerm bindings e))
    = ECaseTermF ctor bindings e

  eraseTypesBinding (name, ty) = name


partiallyApplyCtors :: forall m. MonadReader Context m => ErasedTerm -> m ErasedTerm
partiallyApplyCtors = cataM alg where
  alg (EVarF v) = partiallyApplyCtorE v
  alg t = pure (embed t)

partiallyApplyCtorE :: MonadReader Context m => Name -> m ErasedTerm
partiallyApplyCtorE v = do
  lookupEnv v <$> ask >>= \case
    Just t -> pure $ EVar v
    Nothing ->
      fromRight (EVar v) <$> runExceptT (partiallyApplyCtor' [] <$> lookupCtor v)
  where
    partiallyApplyCtor' args (Pi (x,ty) ret)
      = ELam x (partiallyApplyCtor' (EVar x:args) ret)
    partiallyApplyCtor' args _
      = ECtor v args



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
    ctorIndex (DataDecl _ _ ctors)
      = elemIndex c (keys ctors)


data HighLevelAsmExpr
  = HLAEVar Name
  | HLAEFuncVar FunctionName
  | HLAETag Tag
  | HLAEEnvRef Int
  | HLAEUnit
  | HLAEApp HighLevelAsmExpr HighLevelAsmExpr
  | HLAEStructMember HighLevelAsmExpr String
  | HLAEMemIndex HighLevelAsmExpr Int
  deriving Show
makeBaseFunctor ''HighLevelAsmExpr

data HLAAssignExpr
  = HLAAName Name
  | HLAADeref HLAAssignExpr
  | HLAAMemIndex Name Int
  | HLAAStructMember Name String
  deriving Show
makeBaseFunctor ''HLAAssignExpr

data HighLevelAsmStmt
  = HLASAssign HLAAssignExpr HighLevelAsmExpr
  | HLASDeclare Name
  | HLASDeclareHeapAlloc Name Int
  | HLASExpr HighLevelAsmExpr
  | HLASSwitch HighLevelAsmExpr (Map Tag HighLevelAsmStmt)
  | HLASBlock [HighLevelAsmStmt]
  | HLASNop
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
    v <- freshName "tagged_union"
    let stmts = mconcat argStmts
          <> HLASDeclareHeapAlloc v (length args)
          <> HLASAssign (HLAAStructMember v ("data.tag")) (HLAETag t)
          <> mconcat ((\(i, e) -> HLASAssign (HLAAMemIndex v i) e) <$> zip [0..] args)
    pure $ (HLAEVar v, stmts)
  alg (TDMkClosureF f env) = do
    cl <- freshName "closure"
    let s = [ HLASDeclareHeapAlloc cl (length env)
            , HLASAssign (HLAAStructMember cl "data.f") (HLAEFuncVar f)
            ]
          <> ((\(v, i) -> HLASAssign (HLAAMemIndex cl i) (HLAEVar v))
              <$> zip env [0..])
    pure (HLAEVar cl, HLASBlock s)
  alg (TDAppF (f,s) (arg,s')) = pure (HLAEApp f arg, s <> s')
  alg (TDCaseF (scrutinee, s) cases) = do
    v <- freshName "case_ret"
    scrutineeV <- freshName "case_expr"
    let mkCase (bindings, (expr,s')) = mconcat $
          mkBindings bindings scrutineeV <> [s', HLASAssign (HLAAName v) expr]
    let stmt = s
               <> HLASDeclare v
               <> HLASDeclare scrutineeV
               <> HLASAssign (HLAAName scrutineeV) scrutinee
               <> HLASSwitch (HLAEStructMember
                              (HLAEVar scrutineeV) "data.tag")
               (mkCase <$> cases)
    pure $ (HLAEVar v, stmt)
  alg (TDLetF bs (t, s)) = do
    let assigns
          = (\(name,(e,s)) -> s
              <> mconcat [ HLASDeclare name
                         , HLASAssign (HLAAName name) e])
            <$> bs
    pure (t, mconcat assigns <> s)
  alg (TDUnitF) = pure (HLAEUnit, HLASNop)

  mkBindings :: [Name] -> Name -> [HighLevelAsmStmt]
  mkBindings bindings scrutineeV
    = (\(name, i) -> mconcat
        [ HLASDeclare name
        , HLASAssign (HLAAName name) (HLAEMemIndex (HLAEVar scrutineeV) i)
        ])
      <$> zip bindings [0..]


toC :: MonadState GenVar m => HighLevelAsm -> m String
toC (TermAndFunctions t fs)
  = do
  programStmt <- mkProgram <$> toCStmt (fst t)
  let mainStmt = mkMain
  funs <- mapM mkCFunction fs
  pure $ "#include \"rts/headers.h\"\n"
    <> "\n" <> decls
    <> "\n" <> intercalate "\n" (programStmt : mainStmt : funs)
  where
    decls = concatMap declareCFunction fs

    mkMain = cFunction "main" "int" [] $
      "initialise_rts();\n"
      <> "funcall(program);\n"
      <> "run_gc();\nreturn 0;\n"

    mkProgram s
      = cFunction "program" "void" [] $
      s <> "printf(\"%d\\n\", (" <> toCExpr (snd t) <> ")->data.tag);\n"

    headers = intercalate "\n" $ ("#include " <>) <$> ["<stdio.h>", "<stdlib.h>"]

mkCFunction :: MonadState GenVar m => Function (HighLevelAsmStmt, HighLevelAsmExpr) -> m String
mkCFunction (Function name arg _ (body, ret))
  = do body' <- toCStmt body
       pure $ cFunction (toCFnName name) "heap_data*"
         [("heap_data*", toCName arg), ("heap_data**", "env")]
         (body' <> "return " <> toCExpr ret <> ";\n")

toCStmt :: MonadState GenVar m => HighLevelAsmStmt -> m String
toCStmt = cataM alg where
  alg (HLASAssignF a e)
    = pure $ toCAssign a <> " = " <> (toCExpr e) <> ";\n"
  alg (HLASDeclareF d)
    = toCDeclare d
  alg (HLASDeclareHeapAllocF v size)
    = toCDeclareHeapAlloc v size
  alg HLASNopF
    = pure $ ";\n"
  alg (HLASBlockF ss)
    = pure $ concat ss
  alg (HLASExprF e)
    = pure $ toCExpr e <> ";\n"
  alg (HLASSwitchF n cases)
    = pure $ "switch (" <> toCExpr n <> ") {\n"
    <> concat (toCCase <$> M.toList cases) <> "}\n"

  toCCase :: (Tag, String) -> String
  toCCase (Tag t, s)
    = "case " <> show t <> ":\n{\n" <> s <> "break;\n}\n"

toCDeclareHeapAlloc :: MonadState GenVar m => Name -> Int -> m String
toCDeclareHeapAlloc (toCName -> v) size = do
  heapPtr <- toCName <$> freshName "heap_ptr"
  let expr = "heap_data* " <> v <> " = heap_alloc(" <> show size <> ");\n"
      hp = "heap_ptr " <> heapPtr <> " = (heap_ptr){.ptr = &"
        <> v <> ", .next=NULL};\n"
      moveHead = "head_heap_ptr->next = &" <> heapPtr <> ";\n"
        <> "head_heap_ptr = &" <> heapPtr <> ";\n"
  pure (expr <> hp <> moveHead)

toCDeclare :: MonadState GenVar m => Name -> m String
toCDeclare (toCName -> v) = do
  heapPtr <- toCName <$> freshName "heap_ptr"
  let expr = "heap_data* " <> v <> ";\n"
      hp = "heap_ptr " <> heapPtr <> " = (heap_ptr){.ptr = &"
        <> v <> ", .next=NULL};\n"
      moveHead = "head_heap_ptr->next = &" <> heapPtr <> ";\n"
        <> "head_heap_ptr = &" <> heapPtr <> ";\n"
  pure (expr <> hp <> moveHead)

toCAssign :: HLAAssignExpr -> String
toCAssign = cata alg where
  alg (HLAANameF (toCName -> v)) = v
  alg (HLAADerefF a) = "*" <> a
  -- alg (HLAAIndexF a i) = a <> "[" <> show i <> "]"
  alg (HLAAMemIndexF (toCName -> v) i)
    = v <> "->mem[" <> show i <> "]"
  alg (HLAAStructMemberF (toCName -> v) member)
    = v <> "->" <> member

toCExpr :: HighLevelAsmExpr -> String
toCExpr = cata alg where
  alg (HLAEVarF n)
    = toCName n
  alg (HLAEFuncVarF f)
    = toCFnName f
  alg (HLAETagF (Tag t))
    =  show t
  alg (HLAEEnvRefF i)
    = "env[" <> show i <> "]"
  alg HLAEUnitF
    = "NULL"
  alg (HLAEAppF f x)
    = "closure_call(" <> f <> ", " <> x <> ")"
  alg (HLAEStructMemberF e member)
    = "(" <> e <> ")->" <> member
  alg (HLAEMemIndexF e i)
    = "(" <> e <> ")->mem[" <> show i <> "]"

declareCFunction :: Function (HighLevelAsmStmt, HighLevelAsmExpr) -> String
declareCFunction (Function name arg _ (body, ret))
  = cFunDecl (toCFnName name) "heap_data*" [("heap_data*", toCName arg), ("heap_data**", "env")]

cFunction :: String -> String -> [(String, String)] -> String -> String
cFunction name ret params body
  = ret <> " " <> name <> "(" <> mkParams params <> ") {\n" <> body <> "}\n"

cFunDecl :: String -> String -> [(String, String)] -> String
cFunDecl name ret params = ret <> " " <> name <> "(" <> mkParams params <> ");\n"

mkParams :: [(String, String)] -> String
mkParams = intercalate ", " . fmap (\(t, v) -> t <> " " <> v)

toCName :: Name -> String
toCName (Specified n) = "user_" <> n
toCName (Generated c (GenVar n)) = c <> "_" <> show n

toCFnName :: FunctionName -> String
toCFnName (FunctionName n) = "fn_" <> toCName n

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

compileToC :: MonadError CompilerError m => Context -> Cofree TermF Type -> m String
compileToC ctx = flip evalStateT (GenVar 0) . flip runReaderT ctx
  . (toC <=< toHLA <=< (withError CTDError . toTaggedData)
     <=< lambdaLift <=< partiallyApplyCtors)
  . eraseTypes
