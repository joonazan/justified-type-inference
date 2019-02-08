import Data.IOArray
import Data.Fin

export
data Array : Nat -> Type -> Type where
  MkArray : IOArray t -> Array length t

export
makeArray : (n : Nat) -> t -> IO (Array n t)
makeArray n val = map MkArray $ newArray (toIntNat n) val

readArray : Fin n -> Array n a -> IO a
readArray x (MkArray arr) =
  unsafeReadArray arr $ toIntNat $ finToNat x
