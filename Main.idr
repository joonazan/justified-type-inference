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
Subst = TypeVarName -> Maybe LType

apply : Subst -> LType -> LType
apply s (x ~> y) = apply s x ~> apply s y
apply s (TVar x) =
  case s x of
    Nothing => TVar x
    Just y => y
apply s (Primitive x) = Primitive x

unify : (a : LType) -> (b : LType)
  -> Either
    ((s : Subst) -> apply s a = apply s b -> Void)
    (s : Subst ** apply s a = apply s b)

unify (x ~> y) (z ~> w) =
  -- s1 <- unify x z
  -- s2 <- unify y w
  -- let a = apply s x = apply s z
  ?r

unify (Primitive x) (Primitive y) =
  case decEq (Primitive x) (Primitive y) of
    Yes prf => Right (\_ => Nothing ** prf)
    No contra => Left(\_ => contra)
unify (TVar x) y = ?x_1
unify x (TVar y) = ?x_7
unify _ _ = ?x
