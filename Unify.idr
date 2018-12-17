module Unify

import Control.ST
import LType
import Substitution

%default total

export
freshTVar : (x : Var) -> ST m LType [x ::: State Nat]
freshTVar x = do
  i <- read x
  write x (i + 1)
  pure (TVar i)

mapContains : LTypeContains x a -> (s : Subst) -> LTypeContains (apply s x) (apply s a)
mapContains Here s = Here
mapContains (InArgument loc) s = InArgument $ mapContains loc s
mapContains (InReturn loc) s = InReturn $ mapContains loc s

occurs : LTypeContains (TVar x) (a ~> b) -> (s : Subst) -> lookup x s = (apply s a) ~> apply s b -> Void
occurs (InArgument loc) s = notInLarger $ mapContains loc s
occurs (InReturn loc) s = notInLarger2 $ mapContains loc s

tvarNotInPrim : LTypeContains (TVar _) (Primitive _) -> Void
tvarNotInPrim Here impossible
tvarNotInPrim (InArgument _) impossible
tvarNotInPrim (InReturn _) impossible

export
MGU : Subst -> LType -> LType -> Type
MGU s a b =
  ( apply s a = apply s b
  , (s2 : Subst) -> apply s2 a = apply s2 b
    -> (s3 ** ((x:LType)-> apply s2 x = apply s3 $ apply s x))
  )

bindPrf : (s2 : Subst) -> (s2prf : apply s2 (TVar x) = apply s2 y)
  -> (any : LType) -> apply s2 any = apply s2 (apply (x |-> y) any)
bindPrf s2 s2prf (y ~> z) =
  rewrite bindPrf s2 s2prf y in
  rewrite bindPrf s2 s2prf z in
  Refl

bindPrf {x} {y} s2 s2prf (TVar k) with (decEq x k)
  bindPrf {x} {y} s2 s2prf (TVar k) | (No contra) =
    rewrite singletonNoSub {b=y} (tvarNotInDifferentTvar contra) in Refl
  bindPrf {x} {y} s2 s2prf (TVar k) | (Yes prf) =
    rewrite sym prf in
    rewrite singletonSub {a=x} {b=y} in s2prf

bindPrf s2 s2prf (Primitive y) = Refl

bind : (a : TypeVarName) -> (b : LType)
  -> Either
    ((s : Subst) -> apply s (TVar a) = apply s b -> Void)
    (s : Subst ** MGU s (TVar a) b)
bind x y =
  case decLTypeContains (TVar x) y of
    No contra => Right (x |-> y **
      ( rewrite singletonSub {a=x} {b=y} in
        rewrite singletonNoSub {b=y} contra in Refl
      , \s2, s2prf => (s2 ** \any => bindPrf s2 s2prf any)
      )
    )

    Yes xInY =>
      case y of
        TVar yvar => Right (nullsubst **
          ( rewrite nullsubstIsNoOp (TVar x) in
            rewrite nullsubstIsNoOp (TVar yvar) in
            case xInY of
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
    Left contra => Left $ \s, claim => absurd $ contra s $ fstEqIfEq claim

    Right (s ** (prf, mguprf)) =>
      case unify
        (assert_smaller (x ~> y) (apply s y))
        (assert_smaller (z ~> w) (apply s w)) of
      {- I am not sure if the assert_smaller calls here are valid,
         as `apply s` may increase size.
         Progress is always made because either
          `apply s` does nothing, so the size decreases
          or it decreases the number of type variables.
      -}

        Left contra => Left $ \s2, s2Unifies =>
          let
            (x1 ** k) = mguprf s2 $ fstEqIfEq s2Unifies
          in contra x1 $
            rewrite sym $ k y in
            rewrite sym $ k w in
            sndEqIfEq s2Unifies

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
