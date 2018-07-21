module TypeCheck where

import Types

import Control.Monad.Except
import Control.Monad.State
import Data.Either

type Context v = [(v, Term v)]

wellTyped :: (Eq v, Show v) => Term v -> Bool
wellTyped = isRight . typeCheck []

typeCheck :: (Eq v, Show v) => Context v -> Term v -> Either String (Term v)
typeCheck gamma (Var v) =
  case lookup v gamma of
    Nothing -> Left $ "Could not find " <> show v <> " in environment."
    Just ty -> Right ty
typeCheck gamma (Lam x body) = Pi x <$> typeCheck (x:gamma) body
typeCheck gamma (Pi (x,xTy) ret) = do
  (Ty n) <- typeCheck gamma xTy
  (Ty n) <- typeCheck ((x,xTy):gamma) ret
  return $ Ty n --TODO: check universes
typeCheck gamma (App a b) = do
  typeCheck gamma a >>= \case
    Pi (x,xTy) ret -> do
      bTy <- typeCheck gamma b
      unify bTy xTy
      return (subst x b ret)
    _ -> Left "Trying to apply a non-function type."
typeCheck gamma (Ty n) = Right $ Ty (n+1)

--subst for with in
subst :: Eq v => v -> Term v -> Term v -> Term v
subst v with (Var u) | v == u    = with
                     | otherwise = Var u
subst v with lam@(Lam (u,uTy) body)
  | v /= u = Lam (u,(subst v with uTy)) (subst v with body)
  | otherwise = lam
subst v with pi@(Pi (u,uTy) ret)
  | v /= u = Pi (u,(subst v with uTy)) (subst v with ret)
  | otherwise = pi
subst v with (App a b) = App (subst v with a) (subst v with b)
subst v with (Ty n) = (Ty n)

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
  | otherwise = error $ "unify' " <> show x <> " and " <> show y
unify' (Pi (x,xTy) a) (Pi (y,yTy) b)
  | x == y = unify' xTy yTy >> unify' a b
  | otherwise = error $ "unify' " <> show x <> " and " <> show y
unify' (App a b) (App x y) = do
  unify' a x
  unify' b y
unify' (Ty n) (Ty m) = if n == m then return () else mzero
unify' _ _ = mzero
{-
unify (Let [] a) b = unify a b
unify a (Let [] b) = unify a b
unify (Let (x:xs) a) (Let ys b) = unify (Let xs (inline x a) ) (Let ys b)
unify (Let xs a) (Let (y:ys) b) = unify (Let xs a) (Let ys (inline y b))
-}
--TODO: case

