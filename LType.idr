module LType

import Pruviloj.Derive.DecEq
import Data.Vect

public export
TypeVarName : Type
TypeVarName = Nat

public export
data LType : Type where
  TVar : TypeVarName -> LType
  TCons : String -> Vect _ LType -> LType

infixr 10 ~>

export
(~>) : LType -> LType -> LType
(~>) a b = TCons "->" [ a, b ]

%language ElabReflection

decEqForLType : (a : LType) -> (b : LType) -> Dec (a = b)
%runElab (deriveDecEq `{decEqForLType})

export
implementation DecEq LType where
  decEq = decEqForLType

export
fstEqIfEq : a ~> b = c ~> d -> a = c
fstEqIfEq Refl = Refl

export
sndEqIfEq : a ~> b = c ~> d -> b = d
sndEqIfEq Refl = Refl

public export
data LTypeContains : LType -> LType -> Type where
  Here : LTypeContains x x
  InArguments : LTypeContains x t -> Elem t args
    -> LTypeContains x (TCons name args)

export
tvarNotInDifferentTvar : (a = b -> Void) -> LTypeContains (TVar a) (TVar b) -> Void
tvarNotInDifferentTvar contra Here = contra Refl
tvarNotInDifferentTvar _ (InArguments _ _) impossible

mutual
  vectContains : (x : LType) -> (args : Vect n LType)
    -> Dec (t : LType ** (LTypeContains x t, Elem t args))

  vectContains x [] = No $ \(_ ** (_, hasEl)) => noEmptyElem hasEl
  vectContains x (first::rest) = case decLTypeContains x first of
    Yes prf => Yes (first ** (prf, Here))
    No notInFirst => case vectContains x rest of
      Yes (t ** (prf, at)) => Yes (t ** (prf, There at))
      No notInRest => No $ \(t ** (hasX, at)) =>
        case at of
          Here => notInFirst hasX
          There inRest => notInRest (t ** (hasX, inRest))

  export
  decLTypeContains : (x : LType) -> (t : LType) -> Dec (LTypeContains x t)
  decLTypeContains x y with (decEq x y)
    decLTypeContains x y | (Yes prf) = rewrite prf in Yes Here
    decLTypeContains x (TCons name args) | (No notEqual) =
      case vectContains x args of
        Yes (t ** (xInT, tInArgs)) => Yes (InArguments xInT tInArgs)
        No contra => No $ \claim => case claim of
          InArguments {t} xInT tInArgs => contra (t ** (xInT, tInArgs))

    decLTypeContains x (TVar y) | (No notEqual) = No $ \claim => case claim of
      Here => notEqual Refl
