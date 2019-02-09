import Data.Fin

Array : Type -> Nat -> Type

makeArray : (n : Nat) -> Array t n

readArray : Fin n -> Array t n -> t

writeArray : Fin n -> t -> Array t n -> Array t n

Graph : Nat -> Type
Graph n = Array (List (Fin n)) n

data Tree a = Node a (List (Tree a))

dfs' : Array Bool n -> Graph n -> List (Fin n) -> (Array Bool n, List (Tree (Fin n)))
dfs' visited _ [] = (visited, [])
dfs' visited g (x :: otherTrees) =
  if readArray x visited then
    dfs' visited g otherTrees
  else
    let
      (v2, children') = dfs' (writeArray x True visited) g (readArray x g)
      (v3, otherTrees') = dfs' v2 g otherTrees
    in
      (v3, Node x children' :: otherTrees')

dfs : Graph n -> List (Fin n) -> List (Tree (Fin n))
dfs {n} g = snd . dfs' (makeArray n) g

reversePostorder' : List a -> Tree a -> List a
reversePostorder' acc (Node root children) =
  root :: foldl reversePostorder' acc children

reversePostorder : Graph n -> List (Fin n)
reversePostorder {n = Z} _ = []
reversePostorder {n = S n} g =
  let trees = dfs g [0 .. last]
  in concatMap (reversePostorder' []) $ reverse trees

transposeGraph : Graph n -> Graph n

scc : Graph n -> List (Tree (Fin n))
scc g = dfs (transposeGraph g) (reversePostorder g)
