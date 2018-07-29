module TypeCheck where

import Term
import Utils

import Control.Monad.Except
import Control.Monad.State
import Data.Either
import Data.List
import Debug.Trace

-- | A map from variables to their types.
type Context v = [(v, Term v)]

-- | Predicate of whether a given term is well-typed in the given context.
wellTyped :: (Eq v, Show v, Enum v) => Context v -> Term v -> Bool
wellTyped = isRight .: typeCheck

-- | Check the type of a term in the given context. Returns the type
--   if the term is well-typed, and gives an error otherwise.
typeCheck :: forall v. (Eq v, Show v, Enum v) => Context v -> Term v -> Either String (Term v)
typeCheck gamma (Var v) =
  case lookup v gamma of
    Nothing -> Left $ "Could not find " <> show v <> " in context."
    Just ty -> Right ty
typeCheck gamma (Lam (x,xTy) body) =
  typeCheck gamma xTy >>= \case
    Ty -> Pi (x,xTy) <$> typeCheck ((x,xTy):gamma) body
    t  -> Left $ "Expected type " <> show (Ty :: Term v) <> ", got type " <> show t
typeCheck gamma (Pi (x,xTy) ret) =
  typeCheck gamma xTy >>= \case
    Ty -> do
       typeCheck ((x,xTy):gamma) ret >>= \case
         Ty -> return Ty
         t      -> Left $ "Expected type " <> show (Ty :: Term v) <> ", got type " <> show t
    t -> Left $ "Expected type " <> show (Ty :: Term v) <> ", got type " <> show t
typeCheck gamma (App a b) =
  typeCheck gamma a >>= \case
    Pi (x,xTy) ret -> do
      bTy <- typeCheck gamma b
      unify gamma bTy xTy
      return (subst x b ret)
    _ -> Left "Trying to apply a non-function type."
typeCheck gamma Ty = Right Ty
typeCheck gamma (Let NoRec bindings body) = do
  --Type-check the bindings without any of the bindings in scope
  sequence $ typeCheckBinding gamma <$> bindings
  let gamma' = (fst <$> bindings) ++ gamma
  let body' = substLet bindings body
  typeCheck gamma' body'
typeCheck gamma (Let Rec bindings body) = do
  let gamma' = (fst <$> bindings) ++ gamma
  --Type-check the bindings with the bindings recursively in scope
  sequence $ typeCheckBinding gamma' <$> bindings
  notType gamma' body >>= (\t -> isType gamma t >> return t)

-- | Helper function to substitute the bindings of a let expression into the body.
substLet :: Eq v => [(Binding v, Term v)] -> Term v -> Term v
substLet xs body = foldr (\((v,_),val) term -> subst v val term) body xs

-- | Returns () if the given term is not a type; throws an error otherwise.
notType gamma t = do
  typeCheck gamma t >>= \case
    Ty -> throwError $ "Expected something not a type, got " <> show t <> ":Type"
    term -> return term

-- | Returns () if the given term is a type; throws an error otherwise.
isType gamma t = do
  typeCheck gamma t >>= \case
    Ty -> return ()
    term -> throwError $ "Expected a type, got " <> show t <> ":" <> show term

-- | Predicate of whether the given term is a type or not.
isType' :: (Eq v, Show v, Enum v) => Context v -> Term v -> Bool
isType' = isRight .: isType

-- | Helper function to type-check a single let binding.
typeCheckBinding gamma ((x,xTy),val) = do
  ty <- typeCheck gamma val
  isType gamma xTy
  unify gamma xTy ty

-- TODO: actually set unification constraints
type Unification v = StateT [(v, Term v)] (Either String)

lookupEnv :: Eq v => v -> Unification v (Maybe (Term v))
lookupEnv v = lookup v <$> get

insertEnv :: v -> Term v -> Unification v ()
insertEnv v x = do
  env <- get
  put ((v,x):env)

canUnify :: (Eq v, Show v, Enum v) => Context v -> Term v -> Term v -> Bool
canUnify ctx = isRight .: unify ctx

-- | Unify two terms. Returns () if they can be unified, and throws an
--   error if they can't.
unify a b ctx = fmap fst $ flip runStateT [] $ unify' a b ctx

unify' :: (Eq v, Show v, Enum v) => Context v -> Term v -> Term v -> Unification v ()
unify' ctx (Var u) (Var v) | v == u = return ()
unify' ctx (Var u) x =
  case lookup u ctx of
    Just y -> mzero
    Nothing ->
      lookupEnv u >>= \case
        Nothing -> insertEnv u x
        Just u' ->unify' ctx u' x
unify' ctx x (Var u) =
  case lookup u ctx of
    Just y -> mzero
    Nothing ->
      lookupEnv u >>= \case
        Nothing -> insertEnv u x
        Just u' ->unify' ctx x u'
unify' ctx a'@(Lam (x,xTy) a) b'@(Lam (y,yTy) b)
  | x == y =unify' ctx xTy yTy >>unify' ctx a b
  | otherwise = do let v = freshVar a' b'
                   unify' ctx (alpha x v a') (alpha y v b')
unify' ctx a'@(Pi (x,xTy) a) b'@(Pi (y,yTy) b)
  | x == y =unify' ctx xTy yTy >>unify' ctx a b
  | otherwise = do let v = freshVar a' b'
                   unify' ctx (alpha x v a') (alpha y v b')
unify' ctx (App a b) (App x y) = do
 unify' ctx a x
 unify' ctx b y
unify' ctx Ty Ty = return ()
unify' ctx (Let _ [] a) b =unify' ctx a b
unify' ctx a (Let _ [] b) =unify' ctx a b
unify' ctx a@(Let Rec _ _) b@(Let _ _ _) = throwError "Trying to unify a letrec"
unify' ctx a@(Let _ _ _) b@(Let Rec _ _) = throwError "Trying to unify a letrec"
unify' ctx a@(Let NoRec _ _) b@(Let NoRec _ _) =unify' ctx (inlineLet a) (inlineLet b)
unify' ctx a b = throwError $ "Could not unify " <> show a <> " and " <> show b
--TODO: case

--TODO: just make Term into a functor over v
alpha old new (Var v) | v == old = Var new
                      | otherwise = Var v
alpha old new (Lam (v,vTy) body)
  | v == old = Lam (new, vTy') body'
  | otherwise = Lam (v, vTy') body'
  where vTy' = alpha old new vTy
        body' = alpha old new body
alpha old new (Pi (v,vTy) ret)
  | v == old = Pi (new, vTy') ret'
  | otherwise = Pi (v, vTy') ret'
  where vTy' = alpha old new vTy
        ret' = alpha old new ret
alpha old new (App a b) = App (alpha old new a) (alpha old new b)
alpha old new Ty = Ty
alpha old new (Let rec xs body) = Let rec (alphaBinds <$> xs) (alpha old new body)
  where alphaBinds ((v,vTy),val) | v == old = ((new, vTy'), val')
                                 | otherwise = ((v, vTy'), val')
                                 where vTy' = alpha old new vTy'
                                       val' =  alpha old new val

-- | Generate a fresh variable that isn't used in either of the given terms.
freshVar :: (Eq v, Enum v) => Term v -> Term v -> v
freshVar a b = toEnum $ (+1) $ maximum $ fmap fromEnum $ allVars a ++ allVars b

-- | Inline a non-recursive let expression.
inlineLet :: Eq v => Term v -> Term v
inlineLet (Let NoRec [] body) = body
inlineLet (Let NoRec xs body) = foldr inline body xs
  where inline ((x,_),val) body = subst x val body

-- | Get a list of all the bound and free variables in a term.
allVars :: Eq v => Term v -> [v]
allVars t = freeVars t ++ boundVars t

-- | Get a list of all the free variables in a term.
freeVars :: Eq v => Term v -> [v]
freeVars (Var v) = [v]
freeVars (Lam (v,ty) body) = (freeVars body ++ freeVars ty) \\ [v]
freeVars (Pi (v,a) ret) = (freeVars ret ++ freeVars a) \\ [v]
freeVars (App a b) = freeVars a ++ freeVars b
freeVars Ty = []
freeVars (Let _ xs body) = freeVars body \\ fmap (fst . fst) xs
  --TODO: free vars in let bindings

-- | Get a list of all the bound variables in a term.
boundVars :: Eq v => Term v -> [v]
boundVars (Var v) = []
boundVars (Lam (v,_) body) = v:boundVars body
boundVars (Pi (v,_) ret) = v:boundVars ret
boundVars (App a b) = boundVars a ++ boundVars b
boundVars Ty = []
boundVars (Let _ xs body) = fmap (fst . fst) xs ++ boundVars body
