import Data.Fin
import Data.SortedSet
import Data.SortedMap

export
interface Ord v => Graph v g where
  neighbors : v -> g -> List v
  vertices : g -> List v

data Tree a = Node a (List (Tree a))

dfs' : Graph v g => SortedSet v -> g -> List v -> (SortedSet v, List (Tree v))
dfs' visited _ [] = (visited, [])
dfs' visited g (x :: otherTrees) =
  if contains x visited then
    dfs' visited g otherTrees
  else
    let
      (v2, children') = dfs' (insert x visited) g (neighbors x g)
      (v3, otherTrees') = dfs' v2 g otherTrees
    in
      (v3, Node x children' :: otherTrees')

dfs : Graph v g => g -> List v -> List (Tree v)
dfs g = snd . dfs' empty g

reversePostorder' : List a -> Tree a -> List a
reversePostorder' acc (Node root children) =
  root :: foldl reversePostorder' acc children

reversePostorder : Graph v g => g -> List v
reversePostorder g =
  concatMap (reversePostorder' []) $ reverse $ dfs g (vertices g)

Transposed : Type -> Type
Transposed v = (List v, SortedMap v (List v))

implementation Ord v => Graph v (Transposed v) where
  neighbors v (_, g) = fromMaybe [] $ lookup v g
  vertices (vs, _) = vs

reverseEdges : Graph v g => g -> SortedMap v (List v)
reverseEdges g = foldl (mergeWith (++)) empty $ map graphTo (vertices g)
  where graphTo : v -> SortedMap v (List v)
        graphTo x = fromList $ map (\n => (n, [x])) (neighbors x g)

transposeGraph : Graph v g => g -> Transposed v
transposeGraph g = ( vertices g, reverseEdges g )

flattenTree : Tree v -> List v
flattenTree (Node a c) = a :: concatMap flattenTree c

export
scc : Graph v g => g -> List (List v)
scc g = map flattenTree $ dfs g $ reversePostorder $ transposeGraph g
