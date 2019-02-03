module LType

import Pruviloj.Derive.DecEq

%default total

public export
TypeVarName : Type
TypeVarName = Nat

public export
data LType : Type where
  TVar : TypeVarName -> LType
  TConst : String -> LType
  TApp : LType -> LType -> LType

infixr 10 ~>

export
(~>) : LType -> LType -> LType
(~>) a b = TApp (TApp (TConst "->") a) b

%language ElabReflection

decEqForLType : (a : LType) -> (b : LType) -> Dec (a = b)
%runElab (deriveDecEq `{decEqForLType})

export
implementation DecEq LType where
  decEq = decEqForLType

export
fstEqIfEq : TApp a b = TApp c d -> a = c
fstEqIfEq Refl = Refl

export
sndEqIfEq : TApp a b = TApp c d -> b = d
sndEqIfEq Refl = Refl

public export
data LTypeContains : LType -> LType -> Type where
  Here : LTypeContains x x
  OnLeft : LTypeContains x t -> LTypeContains x (TApp t _)
  OnRight : LTypeContains x t -> LTypeContains x (TApp _ t)

export
tvarNotInConst : LTypeContains (TVar x) (TConst _) -> Void
tvarNotInConst Here impossible
tvarNotInConst (OnLeft _) impossible
tvarNotInConst (OnRight _) impossible

export
tvarNotInDifferentTvar : (a = b -> Void) -> LTypeContains (TVar a) (TVar b) -> Void
tvarNotInDifferentTvar contra Here = contra Refl
tvarNotInDifferentTvar _ (OnLeft _) impossible
tvarNotInDifferentTvar _ (OnRight _) impossible

export
decLTypeContains : (x : LType) -> (t : LType) -> Dec (LTypeContains x t)
decLTypeContains x y with (decEq x y)
  decLTypeContains x y | (Yes prf) = rewrite prf in Yes Here

  decLTypeContains x (TApp a b) | (No notEqual) =
    case decLTypeContains x a of
      Yes prf => Yes (OnLeft prf)
      No notOnLeft => case decLTypeContains x b of
        Yes prf => Yes (OnRight prf)

        No notOnRight => No $ \x => case x of
          Here => notEqual Refl
          OnLeft prf => notOnLeft prf
          OnRight prf => notOnRight prf

  decLTypeContains x (TVar y) | (No notEqual) = No $ \claim => case claim of
    Here => notEqual Refl

  decLTypeContains _ (TConst x) | (No notEqual) = No $ \claim => case claim of
    Here => notEqual Refl

export
containmentIsTransitive : LTypeContains a b -> LTypeContains b c -> LTypeContains a c
containmentIsTransitive p Here = p
containmentIsTransitive p (OnLeft p2) = OnLeft (containmentIsTransitive p p2)
containmentIsTransitive p (OnRight p2) = OnRight (containmentIsTransitive p p2)

export
noContainmentLoops : LTypeContains a b -> LTypeContains b a -> (a = b -> Void) -> Void
noContainmentLoops Here _ neq = neq Refl
noContainmentLoops (OnLeft x) y neq =
  let badRec = containmentIsTransitive y x
  in noContainmentLoops badRec (OnLeft Here) (\Refl impossible)
noContainmentLoops (OnRight x) y neq =
  let badRec = containmentIsTransitive y x
  in noContainmentLoops badRec (OnRight Here) (\Refl impossible)
