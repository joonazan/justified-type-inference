import Unify
import LType
import Substitution
import Control.ST

%default total

public export
Identifier : Type
Identifier = String

public export
data Expr : Type where
  Variable : Identifier -> Expr
  Lambda : Identifier -> Expr -> Expr
  App : Expr -> Expr -> Expr

public export
Env : Type
Env = Identifier -> Maybe LType

extend : Identifier -> LType -> Env -> Env
extend id t env x =
  if x == id then
    Just t
  else
    env x

subEnv : Subst -> Env -> Env
subEnv s e x =
  map (apply s) $ e x

{-
The function below follows the algorithmic typing rules defined in

A proof of correctness for the Hindley-Milner
type inference algorithm
https://web.archive.org/web/20120324105848/http://www.cs.ucla.edu/~jeff/docs/hmproof.pdf
-}
infer' : (nextId : Var) -> Env -> Expr -> ST Maybe (Subst, LType) [nextId ::: State Nat]

infer' _ env (Variable x) = do
  t <- lift $ env x
  pure (neutral, t)

infer' ctx env (App f x) = do
  (fSubst, fType) <- infer' ctx env f
  (xSubst, xType) <- infer' ctx (subEnv fSubst env) x

  returntype <- freshTVar ctx
  (unifier ** _) <- lift $ eitherToMaybe $
    unify (apply xSubst fType) (xType ~> returntype)

  pure (unifier <+> xSubst <+> fSubst, apply unifier returntype)

infer' ctx env (Lambda argname body) = do
  argtype <- freshTVar ctx
  (s, returntype) <- infer' ctx (extend argname argtype env) body
  pure (s, apply s argtype ~> returntype)

inferWrapper : Env -> Expr -> ST Maybe (Subst, LType) []
inferWrapper env expr = do
  nextId <- new 0
  res <- infer' nextId env expr
  delete nextId

  pure res

export
infer : Env -> Expr -> Maybe LType
infer env expr = do
  (s, t) <- run $ inferWrapper env expr
  pure $ apply s t
