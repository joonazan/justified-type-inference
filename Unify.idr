module Unify

import LType
import Substitution

import Data.Vect
import Data.HVect

%default total

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

public export
Unifies : Subst -> LType -> LType -> Type
Unifies s a b =
  apply s a = apply s b

UnifiesAll : Subst -> Vect _ (LType, LType) -> Type
UnifiesAll s = HVect . map (uncurry $ Unifies s)

public export
IsMGU : Subst -> LType -> LType -> Type
IsMGU s a b =
  ( Unifies s a b
  , (s2 : Subst) -> Unifies s2 a b
    -> (s3 ** ((x:LType)-> apply s2 x = apply s3 $ apply s x))
  )

public export
UnificationResult : LType -> LType -> Type
UnificationResult a b =
  Either
    ((s : Subst) -> Unifies s a b -> Void)
    (s : Subst ** IsMGU s a b)

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

bind : (a : TypeVarName) -> (b : LType) -> UnificationResult (TVar a) b
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
        TVar yvar => Right (neutral **
          ( rewrite nullsubstIsNoOp (TVar x) in
            rewrite nullsubstIsNoOp (TVar yvar) in
            case xInY of
              Here => Refl

          , \s2, _ => (s2 ** \any => rewrite nullsubstIsNoOp any in Refl)
          )
        )
        a ~> b => Left $ occurs xInY
        Primitive _ => Left $ absurd $ tvarNotInPrim xInY

canTransformMore : (pairs : Vect _ (LType, LType)) -> UnifiesAll s pairs -> UnifiesAll (s2 <+> s) pairs
canTransformMore [] x = x
canTransformMore {s} {s2} ((a, b) :: t) (unifiesH :: unifiesT) =
  ( rewrite applySeqIsApplyApply s2 s a in
    rewrite applySeqIsApplyApply s2 s b in
    cong unifiesH
  ) :: canTransformMore t unifiesT

mutual
  unifyMany :
    (pairs : Vect _ (LType, LType))
    -> Either
      ((s : Subst) -> UnifiesAll s pairs -> Void)
      (s : Subst **
        ( UnifiesAll s pairs
        , (s2 : Subst) -> UnifiesAll s2 pairs
          -> (s3 : Subst ** (x : LType) -> apply s2 x = apply s3 $ apply s x)
        )
      )

  unifyMany [] = Right (neutral **
    ([], \s2, _ =>
      (s2 ** (\x => rewrite nullsubstIsNoOp x in Refl))
    )
  )

  unifyMany ((a, b) :: rest) = case unifyMany rest of
    Left contra =>
      Left $ \s, (_ :: sUnifiesRest) => contra s sUnifiesRest

    Right (s ** (sUnifies, sMGUprf)) =>
      case assert_total $ unify (apply s a) (apply s b) of
        {- If the substitution does something, the number of
           different type variables in the type decreases. Thus
           progress is always made.
        -}

        Left contra => Left $ \unicorn, (unifiesThis :: unifiesRest) =>
          let (sToUnicorn ** sToUnicornPrf) = sMGUprf unicorn unifiesRest
          in contra sToUnicorn $
            rewrite sym $ sToUnicornPrf a in
            rewrite sym $ sToUnicornPrf b in unifiesThis

        Right (s2 ** (prf, mguprf)) =>
          Right $ (s2 <+> s **
            ( rewrite applySeqIsApplyApply s2 s a in
              rewrite applySeqIsApplyApply s2 s b in
              prf :: canTransformMore rest sUnifies

            , \unifier, (unifiesThis :: unifiesRest) =>
              let
                (sToUnifier ** sToUnifierPrf) = sMGUprf unifier unifiesRest
                (s2ToUnifier ** s2ToUnifierPrf) = mguprf sToUnifier $
                  rewrite sym $ sToUnifierPrf a in
                  rewrite sym $ sToUnifierPrf b in unifiesThis
              in
                (s2ToUnifier ** \x =>
                  rewrite sToUnifierPrf x in
                  rewrite s2ToUnifierPrf (apply s x) in
                  rewrite applySeqIsApplyApply s2 s x in Refl
                )
            )
          )

  export
  unify : (a : LType) -> (b : LType) -> UnificationResult a b

  unify (x ~> y) (z ~> w) =
    case unifyMany [(x, z), (y, w)] of
      Left contra => Left $ \s, eq => contra s [fstEqIfEq eq, sndEqIfEq eq]
      Right (s ** ([unifiesXZ, unifiesYW], mguprf)) => Right (s **
        ( rewrite unifiesXZ in
          rewrite unifiesYW in Refl
        , \s2, eq => mguprf s2 [fstEqIfEq eq, sndEqIfEq eq]
        )
      )

  unify (Primitive x) (Primitive y) =
    case decEq (Primitive x) (Primitive y) of
      Yes prf => Right (neutral **
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
