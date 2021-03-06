module Tree where

import Cons

data Tree a = Node a (Tree a) (Tree a)
  | Leaf

depth :: Tree Int -> Int
depth Leaf = 0
depth (Node _ a b) = 1 + (if (depth a) > (depth b) then depth a else depth b)

collapse :: Tree Int -> List Int
collapse Leaf = Nil
collapse (Node n a b) = append' (append' (collapse a) (Cons n Nil)) (collapse b)

mapTree :: (Int -> Int) -> Tree Int -> Tree Int
mapTree _ Leaf = Leaf
mapTree f (Node x r l) = Node (f x) (mapTree f r) (mapTree f l)
