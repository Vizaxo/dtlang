{-# LANGUAGE TemplateHaskell #-}
module Compiler where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Lens
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.List
import Data.Tuple
import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as M

import Types
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
eraseTypes :: Term -> ErasedTerm
eraseTypes = cata alg
  where
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
lambdaLift = fmap (uncurry TermAndFunctions) . runWriterT . cataM alg
  where
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

data ExplicitDataData
  = EDClosure' FunctionName [ExplicitDataData]
  | EDTaggedUnion Tag [Name] --TODO: distinguish between data and expr returning data
  deriving Show

data EDClosure = EDClosure FunctionName [Name]
  deriving Show

data ExplicitDataTerm
  = EDVar Name
  | EDEnvRef Int
  | EDUnit
  | EDTaggedUnionExpr Tag [Name]
  | EDMkClosure FunctionName [Name]
  | EDApp ExplicitDataTerm ExplicitDataTerm
  | EDCase ExplicitDataTerm (Map Tag ([Name], ExplicitDataTerm))
  | EDLet [(Name, ExplicitDataTerm)] ExplicitDataTerm
  deriving Show
makeBaseFunctor ''ExplicitDataTerm

type ExplicitData = TermAndFunctions ExplicitDataTerm

data ExplicitDataError
  = EDCtorNotFound Constructor
  deriving Show

toExplicitData :: forall m. (MonadReader [DataDecl] m, MonadError ExplicitDataError m, MonadState GenVar m) => LamLifted -> m ExplicitData
toExplicitData = mapM (cataM alg)
  where
    alg :: Base LamLiftedTerm ExplicitDataTerm -> m ExplicitDataTerm
    alg (LLVarF n) = pure $ EDVar n
    alg (LLEnvRefF i) = pure $ EDEnvRef i
    alg (LLCtorF c args) = do
      bindings <- mapM (\a -> (,a) <$> freshName "ctor_bind") args
      tag <- getCtorTag c
      pure (EDLet bindings (EDTaggedUnionExpr tag (fst <$> bindings)))
    alg (LLMkClosureF f env) = pure (EDMkClosure f env)
    alg (LLAppF f arg) = pure (EDApp f arg)
    alg (LLCaseF e cases) = do
      cases' <- mapM convertCase cases
      pure (EDCase e (M.fromList cases'))
    alg LLErasedTypeF = pure EDUnit

    convertCase :: ErasedCaseTermF ExplicitDataTerm -> m (Tag, ([Name], ExplicitDataTerm))
    convertCase (ECaseTermF ctor bs e) = (, (bs, e)) <$> getCtorTag ctor

getCtorTag :: (MonadReader [DataDecl] m, MonadError ExplicitDataError m) => Constructor -> m Tag
getCtorTag c = do
  datatypes <- ask
  Tag <$> (maybe (throwError (EDCtorNotFound c))  pure $ listToMaybe $ catMaybes (ctorIndex <$> datatypes))
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
  | HLASIf HighLevelAsmExpr HighLevelAsmStmt HighLevelAsmStmt --TODO: probably don't need
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

deriving instance Show a => Show (ExplicitDataTermF a)

type HighLevelAsm = TermAndFunctions (HighLevelAsmStmt, HighLevelAsmExpr)

toHLA :: MonadState GenVar m => ExplicitData -> m HighLevelAsm
toHLA = mapM (fmap swap . cataM alg)
  where
    alg :: MonadState GenVar m => Base ExplicitDataTerm (HighLevelAsmExpr, HighLevelAsmStmt) -> m (HighLevelAsmExpr, HighLevelAsmStmt)
    alg (EDVarF n) = pure $ (HLAEVar n, HLASNop)
    alg (EDEnvRefF i) = pure $ (HLAEEnvRef i, HLASNop)
    alg (EDTaggedUnionExprF t names) = do
      arr <- freshName "tagged_union_arr"
      let assigns = (\(n, i) -> HLASAssignArr arr i (HLAEVar n)) <$> zip names [0..]
      let stmt = HLASDeclareArr (Ptr Void) arr (length names) <> mconcat assigns
      pure $ (HLAETaggedUnionExpr t arr, stmt)
    alg (EDMkClosureF f env) = do
      ret <- freshName "closure_ret"
      envVar <- freshName "closure_env"
      let s = [HLASDeclareAssign (Ptr $ Ptr Void) envVar
               (HLAEMalloc (Ptr Void) (length env))]
            <> ((\(e, i) -> HLASAssignArr envVar i (HLAEVar e)) <$> zip env [0..])
            <> [ HLASDeclareAssign (Ptr Closure) ret (HLAEMalloc Closure 1)
               , HLASAssignArr ret 0 (HLAEMkClosure f envVar)]
      pure (HLAEVar ret, HLASBlock s)
    alg (EDAppF (f,s) (arg,s')) = pure (HLAEApp f arg, s <> s')
    alg (EDCaseF (scrutinee, s) cases) = do
      v <- freshName "case"
      let mkCase (bindings, (expr,s')) = HLASBlock $
            (s':) $
            mkBindings bindings scrutinee <>
            [ HLASAssign v expr
            ]
      let stmt = s
            <> HLASDeclare (Ptr Void) v
            <> HLASSwitch (HLAEStructMember scrutinee "tag") (mkCase <$> cases)
      pure $ (HLAEVar v, stmt)
    alg (EDLetF bs (t, s)) = do
      let s' = fmap (\(name,(e,s)) -> s <> HLASDeclareAssign (Ptr Void) name e) bs :: [HighLevelAsmStmt]
      pure (t, mconcat s' <> s)
    alg (EDUnitF) = pure (HLAEUnit, HLASNop)

    mkBindings :: [Name] -> HighLevelAsmExpr -> [HighLevelAsmStmt]
    mkBindings bindings expr = let bs' = zip bindings [(0 :: Int)..]
      in (\(name, i) -> HLASDeclareAssign (Ptr Void) name (HLAEIndexInto (HLAEStructMember expr "data") i)) <$> bs'


toC :: HighLevelAsm -> String
toC (TermAndFunctions t fs)
  = headers <> "\n" <> mkTaggedUnionStruct <> "\n" <> mkClosureStruct <> "\n" <> mkClosureCallFn
  <> "\n" <> decls
  <> "\n" <> intercalate "\n\n" (mkMain : (mkCFunction <$> fs))
  where
    decls = concatMap declareCFunction fs

    mkMain = cFunction "main" [] (toCStmt (fst t) <> "printf(\"%d\\n\", ((taggedunion*)" <> toCExpr (snd t) <> ")->tag);\n")

    headers = "#include <stdio.h>\n"
            <> "#include <stdlib.h>\n"

mkCFunction :: Function (HighLevelAsmStmt, HighLevelAsmExpr) -> String
mkCFunction (Function name arg _ (HLASNop, ret))
  = cFunction (toCFnName name) [(Ptr Void, toCName arg), (Ptr (Ptr Void), "env")] ("return " <> toCExpr ret <> ";\n")
mkCFunction (Function name arg _ (body, ret))
  = cFunction (toCFnName name) [(Ptr Void, toCName arg), (Ptr (Ptr Void), "env")] (toCStmt body <> "return " <> toCExpr ret <> ";\n")

toCStmt :: HighLevelAsmStmt -> String
toCStmt = cata alg where
  alg (HLASAssignF n e) = toCName n <> " = " <> toCExpr e <> ";\n"
  alg (HLASAssignArrF n i e) = toCName n <> "[" <> show i <> "] = " <> toCExpr e <> ";\n"
  alg (HLASDeclareF t n) = toCType t <> toCName n <> ";\n"
  alg (HLASDeclareArrF t n i) = toCType t <> toCName n <> "[" <> show i <> "];\n"
  alg (HLASDeclareAssignF t n e) = toCType t <> toCName n <> " = " <> toCExpr e <> ";\n"
  alg (HLASIfF cond t f) = "if (" <> toCExpr cond <> ") {\n" <> t <> "} else {\n" <> f <> "}\n"
  alg HLASNopF = ";\n"
  alg (HLASBlockF ss) = concat ss
  alg (HLASExprF e) = toCExpr e <> ";\n"
  alg (HLASSwitchF n cases) = "switch (" <> toCExpr n <> ") {\n" <> concat (toCCase <$> M.toList cases) <> "}\n"

  toCCase :: (Tag, String) -> String
  toCCase (Tag t, s) = "case " <> show t <> ":\n{\n" <> s <> "break;\n}\n"

toCExpr :: HighLevelAsmExpr -> String
toCExpr (HLAEVar n) = toCName n
toCExpr (HLAEEnvRef i) = "env[" <> show i <> "]"
toCExpr HLAEUnit = "null" --TODO: not sure what this should be
toCExpr (HLAETaggedUnionExpr (Tag tag) arr) = "&(taggedunion){.tag = " <> show tag <> ", .data = " <> toCName arr <> "}" --TODO: don't dereference, malloc
toCExpr (HLAEMkClosure f env) = "(closure){.f = " <> toCFnName f <> ", .env = " <> toCName env <> "}"
toCExpr (HLAEApp f x) = "__closure_call(" <> toCExpr f <> ", " <> toCExpr x <> ")"
  --toCFnName f <> "(" <> (intercalate ", " (toCName <$> params)) <> ")"
toCExpr (HLAEIndexInto e i) = "((taggedunion**)" <> toCExpr e <> ")[" <> show i <> "]"
toCExpr (HLAEStructMember e member) = "((taggedunion*)" <> toCExpr e <> ")->" <> member
toCExpr (HLAEMalloc t size) = "malloc(sizeof(" <> toCType t <> ") * " <> show size <> ")"

declareCFunction :: Function (HighLevelAsmStmt, HighLevelAsmExpr) -> String
declareCFunction (Function name arg _ (body, ret))
  = cFunDecl (toCFnName name) [(Ptr Void, toCName arg), (Ptr (Ptr Void), "env")]

cFunction :: String -> [(ASMType, String)] -> String -> String
cFunction name params body = "void* " <> name <> "(" <> mkParams params <> ") {\n" <> body <> "}"

cFunDecl :: String -> [(ASMType, String)] -> String
cFunDecl name params = "void* " <> name <> "(" <> mkParams params <> ");\n"

mkParams :: [(ASMType, String)] -> String
mkParams params = intercalate ", " ((\(t, v) -> toCType t <> " " <> v) <$> params)

toCName :: Name -> String
toCName (Specified n) = n
toCName (Generated c (GenVar n)) = "__" <> c <> "generated_" <> show n

toCFnName :: FunctionName -> String
toCFnName (FunctionName n) = "__fn" <> toCName n

toCType :: ASMType -> String
toCType = cata alg where
  alg :: Base ASMType String -> String
  alg VoidF = "void"
  alg ClosureF = "closure"
  alg TaggedUnionF = "taggedunion"
  alg (PtrF t) = t <> "*"

compileToC :: MonadError CompilerError m => [DataDecl] -> Term -> m String
compileToC ds t = toC <$> (flip evalStateT (GenVar 0) $ toHLA =<< (flip runReaderT ds $ (withError CEDError . toExplicitData) =<< (lambdaLift $ eraseTypes t)))

mkTaggedUnionStruct :: String
mkTaggedUnionStruct = "typedef struct {\n\tint tag;\n\tvoid* data;\n} taggedunion;\n"

mkClosureStruct :: String
mkClosureStruct = "typedef struct {\n\tvoid* (*f)(void*, void**);\n\tvoid** env;\n} closure;\n"

mkClosureCallFn :: String
mkClosureCallFn = "void* __closure_call(closure* f, void* arg) {\nreturn (f->f)(arg, f->env);\n}\n"

data CompilerError
  = CEDError ExplicitDataError
  deriving Show

-- to test
-- mapM @(Except _) (writeFile "testing.c") (compileToC [bool,nat] patternMatchNat')
