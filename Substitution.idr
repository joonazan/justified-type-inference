module Substitution

import LType

-- must be public for lookup to work
public export
Subst : Type
Subst = TypeVarName -> LType

-- should be just export, but Idris does not allow it
public export
lookup : TypeVarName -> Subst -> LType
lookup x s = s x

public export
apply : Subst -> LType -> LType
apply s (x ~> y) = apply s x ~> apply s y
apply s (TVar x) = lookup x s
apply s (Primitive x) = Primitive x

export
implementation Semigroup Subst where
  a <+> b = \x => apply a $ apply b $ TVar x

export
implementation Monoid Subst where
  neutral x = TVar x

infix 5 |->
export
(|->) : TypeVarName -> LType -> Subst
(|->) k v x with (decEq k x)
  (|->) k v x | (Yes _) = v
  (|->) k v x | (No _) = TVar x

%auto_implicits off
export
nullsubstIsNoOp : (x : LType) -> apply neutral x = x
nullsubstIsNoOp (TVar k) = Refl
nullsubstIsNoOp (Primitive x) = Refl
nullsubstIsNoOp (x ~> y) =
  rewrite nullsubstIsNoOp x in
  rewrite nullsubstIsNoOp y in Refl
%auto_implicits on

export
noOpSubst : (z : LType) -> (LTypeContains (TVar x) y -> Void) -> apply (x |-> z) y = y
noOpSubst {y = (a ~> r)} z xNotInY =
  rewrite noOpSubst z (xNotInY . InArgument) in
  rewrite noOpSubst z (xNotInY . InReturn) in Refl

noOpSubst {x} {y = (TVar k)} z xNotInY with (decEq x k)
  noOpSubst {x} {y = (TVar k)} z xNotInY | (No contra) = Refl
  noOpSubst {x} {y = (TVar k)} z xNotInY | (Yes prf) =
    absurd $ xNotInY $ rewrite prf in Here

noOpSubst {y = (Primitive x)} _ _ = Refl

export
applySeqIsApplyApply : (a : Subst) -> (b : Subst) -> (x : LType) -> apply (a <+> b) x = apply a (apply b x)
applySeqIsApplyApply a b (x ~> y) =
  rewrite applySeqIsApplyApply a b x in
  rewrite applySeqIsApplyApply a b y in Refl
applySeqIsApplyApply a b (TVar x) = Refl
applySeqIsApplyApply a b (Primitive x) = Refl

export
singletonSub : apply (a |-> b) (TVar a) = b
singletonSub {a} = rewrite decEqSelfIsYes {x = a} in Refl

export
singletonNoSub : (LTypeContains (TVar a) x -> Void) -> apply (a |-> b) x = x
singletonNoSub {x = (arg ~> ret)} {b} aNotInX =
  rewrite singletonNoSub {b} (aNotInX . InArgument) in
  rewrite singletonNoSub {b} (aNotInX . InReturn) in Refl

singletonNoSub {a} {x = (TVar k)} aNotInX with (decEq a k)
  singletonNoSub {x = (TVar k)} aNotInX | (Yes Refl) = absurd (aNotInX Here)
  singletonNoSub {x = (TVar k)} aNotInX | (No _) = Refl
singletonNoSub {x = (Primitive x)} aNotInX = Refl
