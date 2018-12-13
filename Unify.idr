module Unify

import Control.ST

%default total

export
TypeVarName : Type
TypeVarName = Nat

infixr 10 ~>

public export
data LType : Type where
  (~>) : LType -> LType -> LType
  TVar : TypeVarName -> LType
  Primitive : String -> LType

export
freshTVar : (x : Var) -> ST m LType [x ::: State Nat]
freshTVar x = do
  i <- read x
  write x (i + 1)
  pure (TVar i)

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

fstEqIfEq : a ~> b = c ~> d -> a = c
fstEqIfEq Refl = Refl

sndEqIfEq : a ~> b = c ~> d -> b = d
sndEqIfEq Refl = Refl

export
Subst : Type
Subst = TypeVarName -> LType

export
nullsubst : Subst
nullsubst x = TVar x

export
apply : Subst -> LType -> LType
apply s (x ~> y) = apply s x ~> apply s y
apply s (TVar x) = s x
apply s (Primitive x) = Primitive x

nullsubstIsNoOp : (x : LType) -> apply Unify.nullsubst x = x
nullsubstIsNoOp (x ~> y) =
  rewrite nullsubstIsNoOp x in
  rewrite nullsubstIsNoOp y in Refl

nullsubstIsNoOp (TVar k) = Refl
nullsubstIsNoOp (Primitive x) = Refl

export
sequenceS : Subst -> Subst -> Subst
sequenceS s s2 x =
  apply s2 $ apply s $ TVar x

applySeqIsApplyApply : (a : Subst) -> (b : Subst) -> (x : LType) -> apply (sequenceS a b) x = apply b (apply a x)
applySeqIsApplyApply a b (x ~> y) =
  rewrite applySeqIsApplyApply a b x in
  rewrite applySeqIsApplyApply a b y in Refl
applySeqIsApplyApply a b (TVar x) = Refl
applySeqIsApplyApply a b (Primitive x) = Refl

data LTypeContains : LType -> LType -> Type where
  Here : LTypeContains x x
  InArgument : LTypeContains x t -> LTypeContains x (t ~> r)
  InReturn : LTypeContains x t -> LTypeContains x (a ~> t)

neitherBranch : (LTypeContains x a -> Void) -> (LTypeContains x r -> Void)
  -> (x = (a ~> r) -> Void)
  -> LTypeContains x (a ~> r) -> Void

neitherBranch notInArg _ _ (InArgument inArg) = notInArg inArg
neitherBranch _ notInReturn _ (InReturn inReturn) = notInReturn inReturn

noTVarInPrimitive : LTypeContains (TVar x) (Primitive y) -> Void
noTVarInPrimitive Here impossible
noTVarInPrimitive (InArgument _) impossible
noTVarInPrimitive (InReturn _) impossible

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

infix 5 |->
(|->) : TypeVarName -> LType -> TypeVarName -> LType
(|->) k v x with (decEq k x)
  (|->) k v x | (Yes _) = v
  (|->) k v x | (No _) = TVar x

noOpSubst : (z : LType) -> (LTypeContains (TVar x) y -> Void) -> apply (x |-> z) y = y
noOpSubst {y = (a ~> r)} z xNotInY =
  rewrite noOpSubst z (xNotInY . InArgument) in
  rewrite noOpSubst z (xNotInY . InReturn) in Refl

noOpSubst {x} {y = (TVar k)} z xNotInY with (decEq x k)
  noOpSubst {x} {y = (TVar k)} z xNotInY | (No prf) = Refl
  noOpSubst {x} {y = (TVar k)} z xNotInY | (Yes prf) =
    absurd $ xNotInY $ rewrite prf in Here

noOpSubst {y = (Primitive x)} _ _ = Refl

alsoContainsArg : LTypeContains (x1 ~> x2) t -> LTypeContains x1 t
alsoContainsArg Here = InArgument Here
alsoContainsArg (InArgument x) = InArgument $ alsoContainsArg x
alsoContainsArg (InReturn x) = InReturn $ alsoContainsArg x

alsoContainsRet : LTypeContains (x1 ~> x2) t -> LTypeContains x2 t
alsoContainsRet Here = InReturn Here
alsoContainsRet (InArgument x) = InArgument $ alsoContainsRet x
alsoContainsRet (InReturn x) = InReturn $ alsoContainsRet x

mutual
  notInLarger : LTypeContains x a -> x = (a ~> r) -> Void
  notInLarger Here Refl impossible
  notInLarger {x = x1 ~> x2} (InArgument rest) eq =
    notInLarger (alsoContainsArg rest) $ fstEqIfEq eq

  notInLarger {x = x1 ~> x2} (InReturn rest) eq =
    notInLarger2 (alsoContainsArg rest) (fstEqIfEq eq)

  notInLarger2 : LTypeContains x r -> x = (a ~> r) -> Void
  notInLarger2 Here Refl impossible
  notInLarger2 {x = x1 ~> x2} (InArgument rest) eq =
    notInLarger (alsoContainsRet rest) $ sndEqIfEq eq

  notInLarger2 {x = x1 ~> x2} (InReturn rest) eq =
    notInLarger2 (alsoContainsRet rest) (sndEqIfEq eq)

mapContains : LTypeContains x a -> (s : Subst) -> LTypeContains (apply s x) (apply s a)
mapContains Here s = Here
mapContains (InArgument loc) s = InArgument $ mapContains loc s
mapContains (InReturn loc) s = InReturn $ mapContains loc s

occurs : LTypeContains (TVar x) (a ~> b) -> (s : Subst) -> s x = (apply s a) ~> apply s b -> Void
occurs (InArgument loc) s = notInLarger $ mapContains loc s
occurs (InReturn loc) s = notInLarger2 $ mapContains loc s

tvarNotInPrim : LTypeContains (TVar _) (Primitive _) -> Void

export
MGU : Subst -> LType -> LType -> Type
MGU s a b =
  ( apply s a = apply s b
  , (s2 : Subst) -> apply s2 a = apply s2 b -> (s3 ** ((x:LType)-> apply s2 x = apply s3 $ apply s x))
  )

bindPrf : (s2 : Nat -> LType) -> (s2prf : s2 x = apply s2 y) -> (any : LType) -> apply s2 any = apply s2 (apply (x |-> y) any)
bindPrf s2 s2prf (y ~> z) =
  rewrite bindPrf s2 s2prf y in
  rewrite bindPrf s2 s2prf z in
  Refl

bindPrf {x} s2 s2prf (TVar k) with (decEq x k)
  bindPrf {x} s2 s2prf (TVar k) | (No _) = Refl
  bindPrf {x} s2 s2prf (TVar k) | (Yes prf) = rewrite sym prf in s2prf

bindPrf s2 s2prf (Primitive y) = Refl

bind : (a : TypeVarName) -> (b : LType)
  -> Either
    ((s : Subst) -> apply s (TVar a) = apply s b -> Void)
    (s : Subst ** MGU s (TVar a) b)
bind x y =
  case decLTypeContains (TVar x) y of
    No contra => Right (x |-> y **
      ( rewrite decEqSelfIsYes {x} in
        rewrite noOpSubst y contra in Refl
      , \s2, s2prf => (s2 ** \any => bindPrf s2 s2prf any)
      )
    )

    Yes xInY =>
      case y of
        TVar yvar => Right (nullsubst **
          ( case xInY of
              Here => Refl
          , \s2, _ => (s2 ** \any => rewrite nullsubstIsNoOp any in Refl)
          )
        )
        a ~> b => Left $ occurs xInY
        Primitive _ => Left $ absurd $ tvarNotInPrim xInY

export
unify : (a : LType) -> (b : LType)
  -> Either
    ((s : Subst) -> apply s a = apply s b -> Void)
    (s : Subst ** MGU s a b)

unify (x ~> y) (z ~> w) =
  case unify x z of
    Left contra => Left $ \s => contra s . fstEqIfEq

    Right (s ** (prf, mguprf)) =>
      case unify (apply s y) (apply s w) of
        Left contra => Left $ \s2, claim =>
          let
            (x1 ** k) = mguprf s2 $ fstEqIfEq claim
          in contra x1 $
            rewrite sym $ k y in
            rewrite sym $ k w in
            sndEqIfEq claim

        Right (s2 ** (prf2, mguprf2)) => Right (sequenceS s s2 **
          ( rewrite applySeqIsApplyApply s s2 x in
            rewrite applySeqIsApplyApply s s2 y in
            rewrite applySeqIsApplyApply s s2 z in
            rewrite applySeqIsApplyApply s s2 w in
            rewrite prf in
            rewrite prf2 in Refl
          , \unifier, uniprf =>
            let
              (sToUnifier ** sToUnifierPrf) = mguprf unifier $ fstEqIfEq uniprf
              (sAnds2sToUnifier ** sAnds2sToUnifierPrf) = mguprf2 sToUnifier $
                rewrite sym $ sToUnifierPrf y in
                rewrite sym $ sToUnifierPrf w in sndEqIfEq uniprf
            in (sAnds2sToUnifier ** \x =>
              rewrite sToUnifierPrf x in
              rewrite sAnds2sToUnifierPrf (apply s x) in
              rewrite applySeqIsApplyApply s s2 x in Refl
            )
          )
        )

unify (Primitive x) (Primitive y) =
  case decEq (Primitive x) (Primitive y) of
    Yes prf => Right (nullsubst **
      ( prf
      , \s2, _ => (s2 ** \t => rewrite nullsubstIsNoOp t in Refl)
      )
    )
    No contra => Left (\_ => contra)

unify (TVar x) y = bind x y
unify x (TVar y) =
  case bind y x of
    Left contra => Left $ \s => negEqSym $ contra s
    Right (s ** (prf, mguprf)) =>
      Right (s ** (sym prf, \s2, s2prf => mguprf s2 $ sym s2prf))

-- Mismatch cases

unify (x ~> y) (Primitive z) = Left $ \_ => \Refl impossible
unify (Primitive x) (y ~> z) = Left $ \_ => \Refl impossible
