module TypeCheck where

import Term
import Utils

import Control.Monad.Except
import Control.Monad.State
import Data.Either
import Data.List
import Debug.Trace

-- | A map from variables to their types
type Context v = [(v, Term v)]

wellTyped :: (Eq v, Show v) => Context v -> Term v -> Bool
wellTyped = isRight .: typeCheck

typeCheck :: forall v. (Eq v, Show v) => Context v -> Term v -> Either String (Term v)
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
      unify bTy xTy
      return (subst x b ret)
    _ -> Left "Trying to apply a non-function type."
typeCheck gamma Ty = Right Ty
typeCheck gamma (Let NoRec bindings body) = do
  --Type-check the bindings without any of the bindings in scope
  sequence $ typeCheckBinding gamma <$> bindings
  let gamma' = (fst <$> bindings) ++ gamma
  typeCheck gamma' body
typeCheck gamma (Let Rec bindings body) = do
  let gamma' = (fst <$> bindings) ++ gamma
  --Type-check the bindings with the bindings recursively in scope
  sequence $ typeCheckBinding gamma' <$> bindings
  notType gamma' body >>= (\t -> isType gamma t >> return t)

notType gamma t = do
  typeCheck gamma t >>= \case
    Ty -> throwError $ "Expected something not a type, got " <> show t <> ":Type"
    term -> return term

isType gamma t = do
  typeCheck gamma t >>= \case
    Ty -> return ()
    term -> throwError $ "Expected a type, got " <> show t <> ":" <> show term

isType' :: (Eq v, Show v, Enum v) => Context v -> Term v -> Bool
isType' = isRight .: isType

typeCheckBinding gamma ((x,xTy),val) = do
  ty <- typeCheck gamma val
  isType gamma xTy
  unify xTy ty

-- TODO: actually set unification constraints
type Unification v = StateT [(v, Term v)] (Either String)

lookupEnv :: Eq v => v -> Unification v (Maybe (Term v))
lookupEnv v = lookup v <$> get

insertEnv :: v -> Term v -> Unification v ()
insertEnv v x = do
  env <- get
  put ((v,x):env)

unify a b = fmap fst $ flip runStateT [] $ unify' a b

unify' :: (Eq v, Show v) => Term v -> Term v -> Unification v ()
unify' (Var u) (Var v) | v == u = return ()
unify' (Var u) x =
  lookupEnv u >>= \case
    Nothing -> insertEnv u x
    Just u' -> unify' u' x
unify' x (Var u) =
  lookupEnv u >>= \case
    Nothing -> insertEnv u x
    Just u' -> unify' x u'
unify' (Lam (x,xTy) a) (Lam (y,yTy) b)
  | x == y = unify' xTy yTy >> unify' a b
  | otherwise = lift . Left $ "unify' " <> show x <> " and " <> show y --TODO: eta-substitution
unify' (Pi (x,xTy) a) (Pi (y,yTy) b)
  | x == y = unify' xTy yTy >> unify' a b
  | otherwise = lift . Left $ "unify' " <> show x <> " and " <> show y --TODO: eta-substitution
unify' (App a b) (App x y) = do
  unify' a x
  unify' b y
unify' Ty Ty = return ()
unify' (Let _ [] a) b = unify' a b
unify' a (Let _ [] b) = unify' a b
unify' a@(Let Rec _ _) b@(Let _ _ _) = throwError "Trying to unify a letrec"
unify' a@(Let _ _ _) b@(Let Rec _ _) = throwError "Trying to unify a letrec"
unify' a@(Let NoRec _ _) b@(Let NoRec _ _) = unify' (inlineLet a) (inlineLet b)
unify' a b = lift . Left $ "Could not unify " <> show a <> " and " <> show b
--TODO: case

inlineLet :: Eq v => Term v -> Term v
inlineLet (Let NoRec [] body) = body
inlineLet (Let noRec xs body) = foldr inline body xs
  where inline ((x,_),val) body = subst x val body
        isRec ((x,_),val) = elem x (freeVars val)

freeVars :: Eq v => Term v -> [v]
freeVars (Var v) = [v]
freeVars (Lam (v,_) body) = freeVars body \\ [v]
freeVars (Pi (v,_) ret) = freeVars ret \\ [v]
freeVars (App a b) = freeVars a ++ freeVars b
freeVars Ty = []
freeVars (Let _ xs body) = freeVars body \\ fmap (fst . fst) xs
