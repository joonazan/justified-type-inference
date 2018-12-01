%default total

Identifier : Type
Identifier = String

data Expr : Type where
  Variable : Identifier -> Expr
  Lambda : Identifier -> Expr -> Expr
  App : Expr -> Expr -> Expr

TypeVarName : Type
TypeVarName = Nat

infixr 10 ~>

data LType : Type where
  (~>) : LType -> LType -> LType
  TVar : TypeVarName -> LType
  Primitive : String -> LType

implementation DecEq LType where
  decEq (x ~> y) (z ~> w) with (decEq x z, decEq y w)
    decEq (x ~> y) (z ~> w) | (Yes q, Yes p) = Yes $
      rewrite q in cong p
    decEq (x ~> y)(z ~> w)|(No t, _) = No $
      \Refl => t Refl
    decEq (x ~> y)(z ~> w)|(_, No t) = No $
      \Refl => t Refl

  decEq (TVar x) (TVar y) with (decEq x y)
    decEq (TVar x) (TVar y) | (Yes prf) =
      Yes $ cong prf
    decEq (TVar x) (TVar y) | (No contra) =
      No $ \Refl => contra Refl

  decEq (Primitive x) (Primitive y) with (decEq x y)
    decEq (Primitive x) (Primitive y) | (Yes prf) =
      Yes $ cong prf
    decEq (Primitive x) (Primitive y) | (No contra) =
      No $ \Refl => contra Refl

  decEq (TVar x) (Primitive y) = No $ \Refl impossible
  decEq (Primitive x) (y ~> z) = No $ \Refl impossible
  decEq (Primitive x) (TVar y) = No $ \Refl impossible
  decEq (x ~> y) (TVar z) = No $ \Refl impossible
  decEq (x ~> y) (Primitive z) = No $ \Refl impossible
  decEq (TVar x) (y ~> z) = No $ \Refl impossible

Subst : Type
Subst = TypeVarName -> LType

nullsubst : Subst
nullsubst x = TVar x

apply : Subst -> LType -> LType
apply s (x ~> y) = apply s x ~> apply s y
apply s (TVar x) = s x
apply s (Primitive x) = Primitive x

sequenceS : Subst -> Subst -> Subst
sequenceS s s2 x =
  apply s2 $ apply s $ TVar x

applySeqIsApplyApply : (a : Subst) -> (b : Subst) -> (x : LType) -> apply (sequenceS a b) x = apply b (apply a x)
applySeqIsApplyApply a b (x ~> y) =
  rewrite applySeqIsApplyApply a b x in
  rewrite applySeqIsApplyApply a b y in Refl
applySeqIsApplyApply a b (TVar x) = Refl
applySeqIsApplyApply a b (Primitive x) = Refl

data ContainsTVar : TypeVarName -> LType -> Type where
  Here : ContainsTVar x (TVar x)
  InArgument : ContainsTVar x t -> ContainsTVar x (t ~> r)
  InReturn : ContainsTVar x t -> ContainsTVar x (a ~> t)

notInDifferentTVar : ((x = y) -> Void) -> ContainsTVar x (TVar y) -> Void
notInDifferentTVar xIsNotY Here = xIsNotY Refl

neitherBranch : (ContainsTVar x a -> Void) -> (ContainsTVar x r -> Void)
  -> ContainsTVar x (a ~> r) -> Void

neitherBranch notInArg _ (InArgument inArg) = notInArg inArg
neitherBranch _ notInReturn (InReturn inReturn) = notInReturn inReturn

noTVarInPrimitive : ContainsTVar x (Primitive y) -> Void
noTVarInPrimitive Here impossible
noTVarInPrimitive (InArgument _) impossible
noTVarInPrimitive (InReturn _) impossible

decContainsTVar : (v : TypeVarName) -> (t : LType) -> Dec (ContainsTVar v t)
decContainsTVar x (a ~> r) =
  case decContainsTVar x a of
    Yes prf => Yes $ InArgument prf
    No contra =>
      case decContainsTVar x r of
        Yes prf => Yes $ InReturn prf
        No contra2 => No $ neitherBranch contra contra2

decContainsTVar x (TVar y) =
  case decEq x y of
    Yes prf => rewrite prf in Yes Here
    No contra => No $ notInDifferentTVar contra

decContainsTVar x (Primitive y) = No noTVarInPrimitive

infix 5 |->
(|->) : TypeVarName -> LType -> TypeVarName -> LType
(|->) k v x with (decEq k x)
  (|->) k v x | (Yes _) = v
  (|->) k v x | (No _) = TVar x

fstEqIfEq : a ~> b = c ~> d -> a = c
fstEqIfEq Refl = Refl

sndEqIfEq : a ~> b = c ~> d -> a = c
sndEqIfEq Refl = Refl

noOpSubst : (z : LType) -> (ContainsTVar x y -> Void) -> apply (x |-> z) y = y
noOpSubst {y = (a ~> r)} z xNotInY =
  rewrite noOpSubst z (xNotInY . InArgument) in
  rewrite noOpSubst z (xNotInY . InReturn) in Refl

noOpSubst {x} {y = (TVar k)} z xNotInY with (decEq x k)
  noOpSubst {x} {y = (TVar k)} z xNotInY | (No prf) = Refl
  noOpSubst {x} {y = (TVar k)} z xNotInY | (Yes prf) =
    absurd $ xNotInY $ rewrite prf in Here

noOpSubst {y = (Primitive x)} _ _ = Refl

occurs : ContainsTVar x (a ~> b) -> (s : Subst) -> s x = (apply s a) ~> apply s b -> Void
occurs (InArgument Here) s = ?lsvg
occurs (InReturn x) s = ?lv_2

bind : (a : TypeVarName) -> (b : LType)
  -> Either
    ((s : Subst) -> apply s (TVar a) = apply s b -> Void)
    (s : Subst ** apply s (TVar a) = apply s b)
bind x y =
  case decContainsTVar x y of
    No contra => Right (x |-> y **
      rewrite decEqSelfIsYes {x} in
      rewrite noOpSubst y contra in Refl)

    Yes xInY =>
      case y of
        TVar yvar => Right (nullsubst **
          case xInY of
            Here => Refl
        )
        a ~> b => Left $ occurs xInY
        Primitive _ impossible

unify : (a : LType) -> (b : LType)
  -> Either
    ((s : Subst) -> apply s a = apply s b -> Void)
    (s : Subst ** apply s a = apply s b)

unify (x ~> y) (z ~> w) =
  case unify x z of
    Left contra => Left $ \s => contra s . fstEqIfEq

    Right (s**prf) =>
      case unify (apply s y) (apply s w) of
        Left contra => Left $ \s2, claim => ?pulma
        Right (s2**prf2) => Right (sequenceS s s2 **
        rewrite applySeqIsApplyApply s s2 x in
        rewrite applySeqIsApplyApply s s2 y in
        rewrite applySeqIsApplyApply s s2 z in
        rewrite applySeqIsApplyApply s s2 w in
        rewrite prf in
        rewrite prf2 in Refl)

unify (Primitive x) (Primitive y) =
  case decEq (Primitive x) (Primitive y) of
    Yes prf => Right (nullsubst ** prf)
    No contra => Left (\_ => contra)

unify (TVar x) y = bind x y
unify x (TVar y) =
  case bind y x of
    Left contra => Left $ \s => negEqSym $ contra s
    Right (s ** prf) => Right (s ** sym prf)

-- Mismatch cases

unify (x ~> y) (Primitive z) = Left $ \_ => \Refl impossible
unify (Primitive x) (y ~> z) = Left $ \_ => \Refl impossible
