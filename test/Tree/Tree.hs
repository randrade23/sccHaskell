module Tree where

data Tree a = Node a (Tree a) (Tree a)
  | Leaf

depth :: Tree Int -> Int
depth Leaf = 0
depth (Node _ a b) = 1 + (if (depth a) > (depth b) then depth a else depth b)
