module Counter

import LType

export
data Counter t = MkCounter (Nat -> (Nat, t))

export
implementation Functor Counter where
  map f (MkCounter fa) = MkCounter (\count => map f (fa count))

export
implementation Applicative Counter where
  pure a = ?holePureApplicative

  (MkCounter ctr) <*> (MkCounter ctr2) = MkCounter $ \count =>
    let (count', f) = ctr count
    in map f (ctr2 count')

export
implementation Monad Counter where
  (MkCounter ctr) >>= f = MkCounter $ \count =>
    let
      (count', val) = ctr count
      MkCounter ctr2 = f val
    in ctr2 count'

export
freshTVar : Counter LType
freshTVar = map TVar $ MkCounter $ \x => (S x, S x)

export
run : Counter t -> t
run (MkCounter ctr) = snd (ctr Z)
