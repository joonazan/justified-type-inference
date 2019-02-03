module Substitution

import LType
import Data.Vect

%default total

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
apply s (TVar x) = lookup x s
apply s orig@(TConst name) = orig
apply s (TApp a b) = TApp (apply s a) (apply s b)

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
nullsubstIsNoOp (TConst n) = Refl
nullsubstIsNoOp (TApp a b) =
  rewrite nullsubstIsNoOp a in
  rewrite nullsubstIsNoOp b in Refl

%auto_implicits on

export
noOpSubst : (z : LType) -> (LTypeContains (TVar x) y -> Void) -> apply (x |-> z) y = y
noOpSubst {y = (TConst name)} z xNotInY = Refl

noOpSubst {y = (TApp a b)} z xNotInY =
  rewrite noOpSubst z (xNotInY . OnLeft) in
  rewrite noOpSubst z (xNotInY . OnRight) in Refl

noOpSubst {x} {y = (TVar k)} z xNotInY with (decEq x k)
  noOpSubst {x} {y = (TVar k)} z xNotInY | (No contra) = Refl
  noOpSubst {x} {y = (TVar k)} z xNotInY | (Yes prf) =
    absurd $ xNotInY $ rewrite prf in Here

export
applySeqIsApplyApply : (a : Subst) -> (b : Subst) -> (x : LType) -> apply (a <+> b) x = apply a (apply b x)
applySeqIsApplyApply a b (TApp x y) =
  rewrite applySeqIsApplyApply a b x in
  rewrite applySeqIsApplyApply a b y in Refl
applySeqIsApplyApply a b (TVar x) = Refl
applySeqIsApplyApply a b (TConst x) = Refl

export
singletonSubst : apply (a |-> b) (TVar a) = b
singletonSubst {a} = rewrite decEqSelfIsYes {x = a} in Refl
