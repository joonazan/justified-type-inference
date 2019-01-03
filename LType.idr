module LType

import Pruviloj.Derive.DecEq

public export
TypeVarName : Type
TypeVarName = Nat

infixr 10 ~>

public export
data LType : Type where
  (~>) : LType -> LType -> LType
  TVar : TypeVarName -> LType
  Primitive : String -> LType

%language ElabReflection

decEqForLType : (a : LType) -> (b : LType) -> Dec (a = b)
%runElab (deriveDecEq `{decEqForLType})

export
implementation DecEq LType where
  decEq = decEqForLType

export
fstEqIfEq : a ~> b = c ~> d -> a = c
fstEqIfEq Refl = Refl

export
sndEqIfEq : a ~> b = c ~> d -> b = d
sndEqIfEq Refl = Refl

public export
data LTypeContains : LType -> LType -> Type where
  Here : LTypeContains x x
  InArgument : LTypeContains x t -> LTypeContains x (t ~> r)
  InReturn : LTypeContains x t -> LTypeContains x (a ~> t)

neitherBranch : (LTypeContains x a -> Void) -> (LTypeContains x r -> Void)
  -> (x = (a ~> r) -> Void)
  -> LTypeContains x (a ~> r) -> Void

neitherBranch notInArg _ _ (InArgument inArg) = notInArg inArg
neitherBranch _ notInReturn _ (InReturn inReturn) = notInReturn inReturn
neitherBranch {x = w ~> y} _ _ notHere Here = notHere Refl
neitherBranch {x = TVar _} _ _ _ Here impossible
neitherBranch {x = Primitive _} _ _ _ Here impossible

noTVarInPrimitive : LTypeContains (TVar x) (Primitive y) -> Void
noTVarInPrimitive Here impossible
noTVarInPrimitive (InArgument _) impossible
noTVarInPrimitive (InReturn _) impossible

export
tvarNotInDifferentTvar : (a = b -> Void) -> LTypeContains (TVar a) (TVar b) -> Void
tvarNotInDifferentTvar contra Here = contra Refl
tvarNotInDifferentTvar _ (InArgument _) impossible
tvarNotInDifferentTvar _ (InReturn _) impossible

alsoContainsArg : LTypeContains (x1 ~> x2) t -> LTypeContains x1 t
alsoContainsArg Here = InArgument Here
alsoContainsArg (InArgument x) = InArgument $ alsoContainsArg x
alsoContainsArg (InReturn x) = InReturn $ alsoContainsArg x

alsoContainsRet : LTypeContains (x1 ~> x2) t -> LTypeContains x2 t
alsoContainsRet Here = InReturn Here
alsoContainsRet (InArgument x) = InArgument $ alsoContainsRet x
alsoContainsRet (InReturn x) = InReturn $ alsoContainsRet x

mutual
  export
  notInLarger : LTypeContains x a -> x = (a ~> r) -> Void
  notInLarger Here Refl impossible
  notInLarger {x = x1 ~> x2} (InArgument rest) eq =
    notInLarger (alsoContainsArg rest) $ fstEqIfEq eq

  notInLarger {x = x1 ~> x2} (InReturn rest) eq =
    notInLarger2 (alsoContainsArg rest) (fstEqIfEq eq)

  notInLarger {x = Primitive _} (InArgument rest) Refl impossible
  notInLarger {x = TVar _} (InArgument rest) Refl impossible
  notInLarger {x = Primitive _} (InReturn rest) Refl impossible
  notInLarger {x = TVar _} (InReturn rest) Refl impossible

  export
  notInLarger2 : LTypeContains x r -> x = (a ~> r) -> Void
  notInLarger2 Here Refl impossible
  notInLarger2 {x = x1 ~> x2} (InArgument rest) eq =
    notInLarger (alsoContainsRet rest) $ sndEqIfEq eq

  notInLarger2 {x = x1 ~> x2} (InReturn rest) eq =
    notInLarger2 (alsoContainsRet rest) (sndEqIfEq eq)

  notInLarger2 {x = Primitive _} (InArgument rest) Refl impossible
  notInLarger2 {x = TVar _} (InArgument rest) Refl impossible
  notInLarger2 {x = Primitive _} (InReturn rest) Refl impossible
  notInLarger2 {x = TVar _} (InReturn rest) Refl impossible

export
decLTypeContains : (x : LType) -> (t : LType) -> Dec (LTypeContains x t)
decLTypeContains x y with (decEq x y)
  decLTypeContains x y | (Yes prf) = rewrite prf in Yes Here
  decLTypeContains x (a ~> r) | (No notEqual) =
    case decLTypeContains x a of
      Yes prf => Yes $ InArgument prf
      No notInArg =>
        case decLTypeContains x r of
          Yes prf => Yes $ InReturn prf
          No notInReturn => No $ neitherBranch notInArg notInReturn notEqual

  decLTypeContains x (TVar y) | (No notEqual) = No $ \claim => case claim of
    Here => notEqual Refl
  decLTypeContains x (Primitive y) | (No notEqual) = No $ \claim => case claim of
    Here => notEqual Refl
