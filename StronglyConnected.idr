data Graph = Integer

data Tree a = Node a (List (Tree a))

generate : Graph n -> Fin n -> Lazy (Tree (Fin n))
generate g v = Node v $ map (generate g) (readArray v g)

chop visited [] = pure []
chop visited (Node v children :: otherTrees) = do
  if !(readArray v visited) then
    chop visited otherTrees
  else do
    writeArray v True visited
    chop visited children
    chop visited otherTrees

reversePostorder : List a -> Tree a -> List a
reversePostorder acc (Node root children) =
  root :: foldl reversePostorder acc children
