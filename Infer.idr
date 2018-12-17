import Unify
import LType
import Substitution
import Counter

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
Env = Identifier -> Maybe (List TypeVarName, LType)

extend : Identifier -> (List TypeVarName, LType) -> Env -> Env
extend id t env x =
  if x == id then
    Just t
  else
    env x

subEnv : Subst -> Env -> Env
subEnv s e x =
  map (map (apply s)) $ e x

freshAssignment : TypeVarName -> Counter Subst
freshAssignment k = map ((|->) k) freshTVar

{-
The function below follows the algorithmic typing rules defined in

A proof of correctness for the Hindley-Milner
type inference algorithm
https://web.archive.org/web/20120324105848/http://www.cs.ucla.edu/~jeff/docs/hmproof.pdf
-}
export
infer : Env -> Expr -> Counter (Maybe (Subst, LType))

infer env (Variable x) = do
  let Just (vars, t) = env x
    | Nothing => pure Nothing

  instantiation <- foldl (<+>) neutral <$> traverse freshAssignment vars
  pure $ Just (neutral, apply instantiation t)

infer env (App f x) = do
  Just (fSubst, fType) <- infer env f
    | Nothing => pure Nothing

  Just (xSubst, xType) <- infer (subEnv fSubst env) x
    | Nothing => pure Nothing

  returntype <- freshTVar
  let Just (unifier ** _) = eitherToMaybe $
    unify (apply xSubst fType) (xType ~> returntype)
    | Nothing => pure Nothing

  pure $ Just (unifier <+> xSubst <+> fSubst, apply unifier returntype)

infer env (Lambda argname body) = do
  argtype <- freshTVar
  Just (s, returntype) <- infer (extend argname ([], argtype) env) body
    | Nothing => pure Nothing
  pure $ Just (s, apply s argtype ~> returntype)

export
typeOf : Env -> Expr -> Maybe LType
typeOf env expr = map snd $ run $ infer env expr
