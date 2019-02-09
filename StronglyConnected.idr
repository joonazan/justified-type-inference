import Data.Fin

%language UniquenessTypes

Array : Type -> Nat -> UniqueType

makeArray : (n : Nat) -> Array t n

readArray : Fin n -> Borrowed (Array t n) -> t

writeArray : Fin n -> t -> Array t n -> Array t n

Graph : Nat -> UniqueType
Graph n = Array (List (Fin n)) n

data Tree a = Node a (List (Tree a))


data UTuple2 : UniqueType -> Type -> UniqueType where
  UTup2 : {a : UniqueType} -> a -> b -> UTuple2 a b

dfs' : Array Bool n -> Borrowed (Graph n) -> List (Fin n) -> UTuple2 (Array Bool n) (List (Tree (Fin n)))
dfs' visited _ [] = UTup2 visited []
dfs' visited g (x :: otherTrees) with (readArray x (lend visited))
  dfs' visited g (_ :: otherTrees) | True =
    dfs' visited g otherTrees

  dfs' visited g (x :: otherTrees) | False =
    let
      UTup2 v2 children' = dfs' (writeArray x True visited) g (readArray x g)
      UTup2 v3 otherTrees' = dfs' v2 g otherTrees
    in
      UTup2 v3 (Node x children' :: otherTrees')

dfs : Graph n -> List (Fin n) -> List (Tree (Fin n))
dfs {n} g l = let UTup2 _ tree = dfs' (makeArray n) (lend g) l in tree

reversePostorder' : List a -> Tree a -> List a
reversePostorder' acc (Node root children) =
  root :: foldl reversePostorder' acc children

reversePostorder : Graph n -> List (Fin n)
reversePostorder {n = Z} _ = []
reversePostorder {n = S n} g =
  let trees = dfs g [0 .. last]
  in concatMap (reversePostorder' []) $ reverse trees

transposeGraph : Borrowed (Graph n) -> Graph n

scc : Graph n -> List (Tree (Fin n))
scc g = dfs (transposeGraph (lend g)) (reversePostorder g)
