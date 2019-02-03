module Unify

import LType
import Substitution

import Data.Vect
import Data.HVect

%default total

subbedContains : (s : Subst) -> LTypeContains x a -> LTypeContains (apply s x) (apply s a)
subbedContains s Here = Here
subbedContains s (OnLeft loc) = OnLeft $ subbedContains s loc
subbedContains s (OnRight loc) = OnRight $ subbedContains s loc

hlp : TApp a b = a -> Void
hlp Refl impossible

hlp2 : TApp a b = b -> Void
hlp2 Refl impossible

occurs : LTypeContains (TVar x) t -> (TVar x = t -> Void)
  -> (s : Subst) -> lookup x s = apply s t -> Void

occurs Here notHere _ _ = notHere Refl

occurs (OnLeft xOnLeft) _ s claim =
  noContainmentLoops
    (subbedContains s xOnLeft)
    (rewrite claim in OnLeft Here)
    (rewrite claim in hlp)

occurs (OnRight xOnRight) _ s claim =
  noContainmentLoops
    (subbedContains s xOnRight)
    (rewrite claim in OnRight Here)
    (rewrite claim in hlp2)

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
bindPrf s2 s2prf (TApp y z) =
  rewrite bindPrf s2 s2prf y in
  rewrite bindPrf s2 s2prf z in
  Refl

bindPrf {x} {y} s2 s2prf (TVar k) with (decEq x k)
  bindPrf {x} {y} s2 s2prf (TVar k) | (No contra) =
    rewrite noOpSubst y (tvarNotInDifferentTvar contra) in Refl
  bindPrf {x} {y} s2 s2prf (TVar k) | (Yes prf) =
    rewrite sym prf in
    rewrite singletonSubst {a=x} {b=y} in s2prf

bindPrf s2 s2prf (TConst y) = Refl

bind : (a : TypeVarName) -> (b : LType) -> UnificationResult (TVar a) b
bind x y =
  case decLTypeContains (TVar x) y of
    No contra => Right (x |-> y **
      ( rewrite singletonSubst {a=x} {b=y} in
        rewrite noOpSubst y contra in Refl
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

        TApp a b => Left $ occurs xInY (\Refl impossible)

        TConst _ => Left $ absurd $ tvarNotInConst xInY

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

  unify (TApp x y) (TApp z w) =
    case unifyMany [(x, z), (y, w)] of
      Left contra => Left $ \s, eq => contra s [fstEqIfEq eq, sndEqIfEq eq]
      Right (s ** ([unifiesXZ, unifiesYW], mguprf)) => Right (s **
        ( rewrite unifiesXZ in
          rewrite unifiesYW in Refl
        , \s2, eq => mguprf s2 [fstEqIfEq eq, sndEqIfEq eq]
        )
      )

  unify (TConst x) (TConst y) =
    case decEq x y of
      Yes prf => Right (neutral **
        ( cong prf
        , \s2, _ => (s2 ** \t => rewrite nullsubstIsNoOp t in Refl)
        )
      )
      No contra => Left $ \_, Refl => contra Refl

  unify (TVar x) y = bind x y
  unify x (TVar y) =
    case bind y x of
      Left contra => Left $ \s => negEqSym $ contra s
      Right (s ** (prf, mguprf)) =>
        Right (s ** (sym prf, \s2, s2prf => mguprf s2 $ sym s2prf))

  -- Mismatch cases

  unify (TApp _ _) (TConst _) = Left $ \_ => \Refl impossible
  unify (TConst _) (TApp _ _) = Left $ \_ => \Refl impossible
