module TC where

import Types
import Utils

import Control.Lens hiding (Context)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as M
import Data.Maybe
import Data.Natural

-- The monad in which type checking is performed
type MonadTypeCheck m = (MonadReader Context m, MonadState GenVar m, MonadError TypeError m)

-- A concrete version of MonadTypeCheck
type TC = ReaderT Context (StateT GenVar (Except TypeError))

data TypeError
  = TENotBetaEqual Term Term
  | TENoConstructor Name Context
  | TEExpectedTy Term
  | TEExpectedPi Term
  | TECaseWrongNumCtorArgs [Type] CaseTerm
  | TECtorWrongNumArgs Term [Term]
  | TEDataReturnsWrong Name Name
  | TEAppDataError
  | TENameAlreadyDefined
  | TEDoesntHaveType Term Type TypeError
  | TENotInContext Name Context
  | TEUnexpectedType Term
  | TENotSyntaxEq Term Term
  | TEAlphaVarsNotEq Name Name
  | TEAlphaCtorsNotEq Name Name
  | TEAlphaTypeUniversesNotEq Natural Natural
  | TEAlphaNotAlphaEq Term Term
  | TENotBetaEq Term Term
  | TEWhnfUnmatchedCase Name Term
  deriving Show

-- The context can be extended with a new binding.

extendCtx :: MonadTypeCheck m=> Binding -> m a -> m a
extendCtx (n,v) = local (insertCtx n v)


extendCtxs :: MonadTypeCheck m => [Binding] -> m a -> m a
extendCtxs = foldr (\b -> (extendCtx b .)) id

-- Generate a name guaranteed to be unused.
fresh :: [Name] -> TC Name
fresh avoid = do
  v <- get
  ctx <- ask
  let existingGens = catMaybes $ (fromEnum <$>) . getGen <$> (fst <$> (getCtx ctx)) ++ avoid
  let nextVar = toEnum $ max (fromEnum v) (1 + maximumOr (-1) (existingGens))
  put $ succ nextVar
  return $ Generated "fresh" nextVar
  where getGen (Generated "fresh" v) = Just v
        getGen _ = Nothing

-- Fresh should produce a variable that is not already present in the
-- context.
prop_freshIsFresh :: Context -> [Name] -> Bool
prop_freshIsFresh ctx existing = runTCProp $ runTC ctx $ do
  z <- fresh existing
  case elem z existing of
    True -> return False
    False -> return True
  case lookupCtx z ctx of
    Nothing -> return True
    Just _ -> return False
  where
    runTCProp (Left _ ) = False
    runTCProp (Right b) = b

emptyCtx :: Context
emptyCtx = Context [] [] []

lookupCtx :: Name -> Context -> Maybe Term
lookupCtx n (Context ctx _ _) = lookup n ctx

insertCtx :: Name -> Term -> Context -> Context
insertCtx n t (Context ctx env ds) = Context ((n,t):ctx) env ds

insertEnv :: Name -> Term -> Context -> Context
insertEnv n t (Context ctx env ds) = Context ctx ((n,t):env) ds

lookupEnv :: Name -> Context -> Maybe Term
lookupEnv n (Context _ env _) = lookup n env

insertDataDecl :: DataDecl -> Context -> Context
insertDataDecl d (Context ctx env ds) = Context ctx env (d:ds)

lookupData' :: Name -> Context -> Maybe DataDecl
lookupData' n (Context _ _ ds) = listToMaybe $ filter (\(DataDecl n' _ _) -> n == n') ds

lookupData :: Name -> TC DataDecl
lookupData n = do
  ctx <- ask
  case lookupData' n ctx of
    Nothing -> throwError $ TENotInContext n ctx
    Just d -> return d

lookupCtor :: (MonadError TypeError m, MonadReader Context m) => Constructor -> m Type
lookupCtor c = do
  ctx <- ask
  case listToMaybe $ catMaybes $ map findCtor (datatypes ctx) of
    Nothing -> throwError $ TENoConstructor c ctx
    Just ty -> return ty
  where findCtor (DataDecl _ _ ctors) = M.lookup c ctors

-- Run the TC monad, outputting all information. This is useful for debugging purposes.
debugTC :: Context -> TC a -> Either TypeError (a, GenVar)
debugTC ctx = runExcept . flip runStateT (toEnum @GenVar 0) . flip runReaderT ctx

-- Get the context that was generated from a TC computation.
getCtxTC :: Context ->  TC Context -> Either TypeError Context
getCtxTC = ((^. _1) <$>) .: debugTC

-- Run the TC monad
runTC :: Context -> TC a -> Either TypeError a
runTC ctx = ((^. _1) <$>) . (debugTC ctx)

retRead :: MonadReader r m => m a -> m (a, r)
retRead m = (,) <$> m <*> ask

-- For functions returning a `TC ()`, writing `success` is clearer than
-- writing `return ()`.
success :: Monad m => m ()
success = return ()
