%default total

Identifier : Type
Identifier = String

data Expr : Type where
  Variable : Identifier -> Expr
  Lambda : Identifier -> Expr -> Expr
  App : Expr -> Expr -> Expr

TypeVarName : Type
TypeVarName = Integer

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

unify : (a : LType) -> (b : LType)
  -> Either
    ((s : Subst) -> apply s a = apply s b -> Void)
    (s : Subst ** apply s a = apply s b)

unify (x ~> y) (z ~> w) =
  case unify x z of
    Left contra => ?p
    Right (s**prf) =>
      case unify (apply s y) (apply s w) of
        Left contra => Left ?l
        Right (s2**prf2) => Right(sequenceS s s2 **
        rewrite applySeqIsApplyApply s s2 x in
        rewrite applySeqIsApplyApply s s2 y in
        rewrite applySeqIsApplyApply s s2 z in
        rewrite applySeqIsApplyApply s s2 w in
        rewrite prf in
        rewrite prf2 in Refl)

unify (Primitive x) (Primitive y) =
  case decEq (Primitive x) (Primitive y) of
    Yes prf => Right (\x => TVar x ** prf)
    No contra => Left(\_ => contra)

unify (TVar x) y = ?x_1
unify x (TVar y) = ?x_7
unify _ _ = ?x
