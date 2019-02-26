module Environment

import LType
import Substitution
import Control.ST
import Data.SortedSet
import Data.SortedMap

public export
QuantifiedType : Type
QuantifiedType = (List TypeVarName, LType)

public export
Identifier : Type
Identifier = String

export
Env : Type
Env = SortedMap Identifier QuantifiedType

export
empty : Env
empty = Data.SortedMap.empty

export
lookup : Identifier -> Env -> Maybe QuantifiedType
lookup = Data.SortedMap.lookup

export
extend : Identifier -> QuantifiedType -> Env -> Env
extend = insert

{-
This function is incorrect. It should only substitute free type variables.
However, it always works because in generalization the variables quantified
over are changed to ones that aren't used anywhere else.
-}
export
subEnv : Subst -> Env -> Env
subEnv s env =
  fromList $ map (map (map (apply s))) (toList env)

freshNat : (x : Var) -> ST m Nat [x ::: State Nat]
freshNat x = do
  res <- read x
  write x (res + 1)
  pure res

export
freshTVar : (x : Var) -> ST m LType [x ::: State Nat]
freshTVar v = do
  x <- freshNat v
  pure (TVar x)

instantiation : (x : Var) -> List TypeVarName -> ST m Subst [x ::: State Nat]
instantiation _ [] = pure neutral
instantiation v (h::t) = do
  x <- freshTVar v
  rest <- instantiation v t
  pure ((h |-> x) <+> rest)

export
instantiate : (x : Var) -> QuantifiedType -> ST m LType [x ::: State Nat]
instantiate v (quantified, tipe) = do
  inst <- instantiation v quantified
  pure (apply inst tipe)

typeVariables : LType -> SortedSet TypeVarName
typeVariables (TVar x) = insert x empty
typeVariables (TConst _) = empty
typeVariables (TApp a b) = typeVariables a <+> typeVariables b

typeVariablesEnv : Env -> SortedSet TypeVarName
typeVariablesEnv env =
  foldr (<+>) empty $ map (typeVariables . snd) (values env)

normalGeneralize : Env -> LType -> QuantifiedType
normalGeneralize env tipe =
  (Data.SortedSet.toList $ difference (typeVariables tipe) (typeVariablesEnv env), tipe)

export
generalize : (x : Var) -> Env -> LType -> ST m QuantifiedType [x ::: State Nat]
generalize v env tipe = do
  withOwnVars <- instantiate v (normalGeneralize env tipe)
  pure (normalGeneralize env withOwnVars)
