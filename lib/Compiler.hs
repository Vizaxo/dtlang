{-# LANGUAGE TemplateHaskell #-}
module Compiler where

import Control.Arrow
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Lens
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.List
import Data.Map (Map)
import Data.Maybe
import Data.Natural hiding (fold)
import qualified Data.Map as M

import Types
import Utils

type ErasedBindingF r = Name

data ErasedCaseTermF r = ECaseTermF
  { _ectConstructor :: Constructor
  , _ectBindings :: [ErasedBindingF r]
  , _ectExpression :: r
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)
makeLenses ''ErasedCaseTermF

-- | Terms but with types erased
data ErasedTerm
  = EVar Name
  | ECtor Constructor [ErasedTerm]
  | ELam (ErasedBindingF ErasedTerm) ErasedTerm
  | EApp ErasedTerm ErasedTerm
  | ECase ErasedTerm [ErasedCaseTermF ErasedTerm]
  | EErasedType
  deriving Show
makeBaseFunctor ''ErasedTerm

freeVarsE :: ErasedTerm -> [Name]
freeVarsE = cata alg where
  alg :: ErasedTermF [Name] -> [Name]
  alg (EVarF v) = [v]
  alg (ECtorF c args) = concat args
  alg (ELamF v body) = body \\ [v]
  alg (EAppF a b) = a ++ b
  alg (ECaseF e terms) = e ++ (concatMap freeVarsCaseTermE terms)
  alg EErasedTypeF = []

  freeVarsCaseTermE :: ErasedCaseTermF [Name] -> [Name]
  freeVarsCaseTermE (ECaseTermF _ bindings expr) = expr \\ bindings

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
  | LLCtor Constructor [LamLiftedTerm]
  | LLCurrFunc FunctionName [Name]
  | LLApp LamLiftedTerm [LamLiftedTerm]
  | LLCase LamLiftedTerm [ErasedCaseTermF LamLiftedTerm]
  | LLErasedType
  deriving Show
makeBaseFunctor ''LamLiftedTerm

freeVarsLL :: LamLiftedTerm -> [Name]
freeVarsLL = cata alg where
  alg :: LamLiftedTermF [Name] -> [Name]
  alg (LLVarF v) = [v]
  alg (LLCtorF c args) = concat args
  alg (LLCurrFuncF f frees) = frees
  alg (LLAppF f xs) = f ++ concat xs
  alg (LLCaseF e terms) = e ++ (concatMap freeVarsCaseTermE terms)
  alg LLErasedTypeF = []

  freeVarsCaseTermE :: ErasedCaseTermF [Name] -> [Name]
  freeVarsCaseTermE (ECaseTermF _ bindings expr) = expr \\ bindings

data DeBruijnLocal t = DBLocal Natural | DBTerm t
  deriving (Functor, Foldable, Traversable)
makeBaseFunctor ''DeBruijnLocal

data Function t = Function
  { name :: FunctionName
  , params :: [Name]
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

freshName :: MonadState GenVar m => m Name
freshName = do
  name <- get
  modify (\(GenVar i) -> GenVar (i+1))
  pure $ Generated name

freshFnName :: MonadState GenVar m => m FunctionName
freshFnName = FunctionName <$> freshName

evalGenVarState :: Monad m => StateT GenVar m a -> m a
evalGenVarState = flip evalStateT (GenVar 0)

lambdaLift :: ErasedTerm -> LamLifted
lambdaLift = uncurry TermAndFunctions . runWriter . evalGenVarState . cataM alg
  where
    alg :: (MonadWriter [Function LamLiftedTerm] m, MonadState GenVar m) => Base ErasedTerm LamLiftedTerm -> m LamLiftedTerm
    alg (EVarF n) = pure (LLVar n)
    alg (ECtorF ctor args) = pure (LLCtor ctor args)
    alg (ELamF arg body) = do
      name <- freshFnName
      let frees = freeVarsLL body \\ [arg]
      tell [Function name (arg:frees) body]
      return (LLCurrFunc name frees)
    alg (EAppF f x) = pure (LLApp f (x:(LLVar <$> freeVarsLL f)))
    alg (ECaseF e terms) = pure (LLCase e terms)
    alg EErasedTypeF = pure LLErasedType

data Tag = Tag Int
  deriving (Eq, Ord, Show)

data ExplicitDataData
  = EDClosure FunctionName [ExplicitDataData]
  | EDTaggedUnion Tag [Name]
  | EDUnit
  deriving Show

data ExplicitDataTerm
  = EDVar Name
  | EDFunc FunctionName
  | EDData ExplicitDataData
  | EDFuncall FunctionName [Name]
  | EDCase ExplicitDataTerm (Map Tag ([Name], ExplicitDataTerm))
  | EDLet [(Name, ExplicitDataTerm)] ExplicitDataTerm
  deriving Show

type ExplicitData = TermAndFunctions ExplicitDataTerm

toExplicitData :: forall m. (MonadReader [DataDecl] m, MonadPlus m, MonadState GenVar m) => LamLifted -> m ExplicitData
toExplicitData = (addFns <$>) . mapM (cataM alg)
  where
    alg :: Base LamLiftedTerm ExplicitDataTerm -> m ExplicitDataTerm
    alg (LLVarF n) = pure $ EDVar n
    alg (LLCtorF c args) = do
      bindings <- mapM (\a -> (,a) <$> freshName) args
      tag <- getCtorTag c
      pure (EDLet bindings (EDData $ EDTaggedUnion tag (fst <$> bindings)))
    alg (LLCurrFuncF f _) = pure (EDFunc f)
    alg (LLAppF f args) = do
      bindings <- mapM (\a -> (,a) <$> freshName) args
      name <- getName f
      pure (EDLet bindings (EDFuncall name (fst <$> bindings)))
    alg (LLCaseF e cases) = do
      cases' <- mapM convertCase cases
      pure (EDCase e (M.fromList cases'))
    alg LLErasedTypeF = pure (EDData EDUnit)

    convertCase :: ErasedCaseTermF ExplicitDataTerm -> m (Tag, ([Name], ExplicitDataTerm))
    convertCase (ECaseTermF ctor bs e) = (, (bs, e)) <$> getCtorTag ctor

    getName :: ExplicitDataTerm -> m FunctionName
    getName (EDFunc f) = pure f
    getName _ = mzero

    identityFn :: Function ExplicitDataTerm
    identityFn = Function (FunctionName $ Specified "identity") [Specified "a"] (EDVar (Specified "a"))

    addFns :: ExplicitData -> ExplicitData
    addFns = over funs (identityFn:)

getCtorTag :: (MonadReader [DataDecl] m, MonadPlus m) => Constructor -> m Tag
getCtorTag c = do
  datatypes <- ask
  Tag <$> (maybe mzero pure $ listToMaybe $ catMaybes (ctorIndex <$> datatypes))
  where
    ctorIndex :: DataDecl -> Maybe Int
    ctorIndex (DataDecl _ _ ((fst <$>) -> ctors))
      = elemIndex c ctors

compile :: (MonadReader [DataDecl] m, MonadPlus m, MonadState GenVar m) => Term -> m ExplicitData
compile = toExplicitData . lambdaLift . eraseTypes

runCompile :: [DataDecl] -> (ReaderT [DataDecl] (StateT GenVar Maybe)) a -> Maybe a
runCompile env ma = evalStateT (runReaderT ma env) (GenVar 0)

interpretED :: forall m. MonadPlus m => ExplicitData -> m ExplicitDataData
interpretED (TermAndFunctions t fs) = interpret' (M.empty) t
  where
    interpret' :: Map Name ExplicitDataData -> ExplicitDataTerm -> m ExplicitDataData
    interpret' env (EDFunc f) = pure (EDClosure f [])
    interpret' env (EDVar n) = maybeMPlus $ M.lookup n env
    interpret' env (EDData d) = pure d
    interpret' env (EDFuncall f args) = do
      (ps, b) <- maybeMPlus $ lookup f $ (\(Function n p b) -> (n, (p, b))) <$> fs
      args' <- maybeMPlus $ mapM (flip M.lookup env) args
      case compare (length ps) (length args) of
        LT -> mzero
        EQ -> interpret' (inserts ps args' env) b
        GT -> pure (EDClosure f args')
    interpret' env (EDCase e cases) = do
      interpret' env e >>= \case
        EDTaggedUnion t args -> do
          (bs, caseTerm) <- maybeMPlus $ M.lookup t cases
          args' <- maybeMPlus $ mapM (flip M.lookup env) args
          interpret' (inserts bs args' env) caseTerm
    interpret' env (EDLet bs t) = do
      bs' :: [(Name, ExplicitDataData)] <- traverseOf (each._2) (interpret' env) bs
      interpret' (uncurry inserts (unzip bs') env) t

    inserts ks vs = foldr (.) id (M.insert <$> ks <*> vs)
