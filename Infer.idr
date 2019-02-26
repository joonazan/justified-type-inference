import Unify
import LType
import Substitution
import Counter
import Control.ST
import StronglyConnected
import Data.SortedSet
import Data.SortedMap
import Environment

public export
data Expr : Type where
  Variable : Identifier -> Expr
  Lambda : Identifier -> Expr -> Expr
  App : Expr -> Expr -> Expr
  Let : List (Identifier, Expr) -> Expr -> Expr

variables : Expr -> SortedSet Identifier
variables (Variable x) = insert x empty
variables (Lambda x body) = delete x (variables body)
variables (App a b) = union (variables a) (variables b)
variables (Let defs body) = foldr delete (variables body) (map fst defs)

implementation Graph Identifier (SortedMap Identifier Expr) where
  neighbors v g = fromMaybe [] $ map (SortedSet.toList . variables) (lookup v g)
  vertices g = keys g

{-
The function below follows the algorithmic typing rules defined in

A proof of correctness for the Hindley-Milner
type inference algorithm
https://web.archive.org/web/20120324105848/http://www.cs.ucla.edu/~jeff/docs/hmproof.pdf
-}
mutual
  export
  infer : (nextTypeVar : Var)
  -> Env -> Expr
  -> ST Maybe (Subst, LType) [nextTypeVar ::: State Nat]

  infer counter env (Variable x) = do
    generalT <- lift $ lookup x env

    instantiated <- instantiate counter generalT
    pure (neutral, instantiated)

  infer counter env (App f x) = do
    (fSubst, fType) <- infer counter env f
    (xSubst, xType) <- infer counter (subEnv fSubst env) x

    returntype <- freshTVar counter
    (unifier ** _) <- lift $ eitherToMaybe $
      unify (apply xSubst fType) (xType ~> returntype)

    pure (unifier <+> xSubst <+> fSubst, apply unifier returntype)

  infer counter env (Lambda argname body) = do
    argtype <- freshTVar counter
    (s, returntype) <- infer counter (extend argname ([], argtype) env) body
    pure (s, apply s argtype ~> returntype)

  infer counter env (Let defs body) = do
    let defsByName = fromList defs
    let mutuallyRecursiveGroups =
        -- TODO: get rid of unnecessary fromMaybe
        map (map $ \n => (n, fromMaybe (Variable "") $ lookup n defsByName)) (scc defsByName)

    (s, withDefs) <- addAll counter env mutuallyRecursiveGroups
    (s2, bodyTipe) <- infer counter withDefs body
    pure (s2 <+> s, bodyTipe)

  addDefs' : (nextTypeVar : Var) -> Env -> List (Identifier, LType, Expr) -> ST Maybe (Subst, Env) [nextTypeVar ::: State Nat]
  addDefs' _ env [] = pure (neutral, env)
  addDefs' counter env ((name, placeholder, expr)::rest) = do
    (s, tipe) <- infer counter env expr
    (s2 ** _) <- lift $ eitherToMaybe (unify (apply s tipe) (apply s placeholder))

    (s3, env') <- addDefs' counter (subEnv (s2 <+> s) env) rest

    generalized <- generalize counter env' tipe
    pure (s3 <+> s2 <+> s, extend name generalized env')

  addDefs : (nextTypeVar : Var) -> Env -> List (Identifier, Expr) -> ST Maybe (Subst, Env) [nextTypeVar ::: State Nat]
  addDefs count env defs = do
      defsWithVars <- hlp defs
      let envWithPlaceholders =
        foldr (\(n, tvar, _) => extend n ([], tvar)) env defsWithVars
      addDefs' count envWithPlaceholders defsWithVars
    where
      hlp : List (Identifier, Expr) -> ST m (List (Identifier, LType, Expr)) [count ::: State Nat]
      hlp [] = pure []
      hlp ((n,e)::t) = do
        tv <- freshTVar count
        rest <- hlp t
        pure ((n, tv, e) :: rest)

  addAll : (nextTypeVar : Var) -> Env -> List (List (Identifier, Expr)) -> ST Maybe (Subst, Env) [nextTypeVar ::: State Nat]
  addAll v env (h::t) = do
    (s, env') <- addDefs v env h
    (s2, env'') <- addAll v env' t
    pure (s2 <+> s, env'')

inferWrapper : Env -> Expr -> ST Maybe (Subst, LType) []
inferWrapper env expr = do
  counter <- new 0
  res <- infer counter env expr
  delete counter
  pure res

export
typeOf : Env -> Expr -> Maybe LType
typeOf env expr = map snd $ run $ inferWrapper env expr
