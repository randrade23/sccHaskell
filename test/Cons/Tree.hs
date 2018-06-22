module Tree where

data List a = Cons a (List a) | Nil

length' :: List Int -> Int
length' Nil = 0
length' (Cons _ y) = 1 + length' y

append' :: List Int -> List Int -> List Int
append' Nil ys = ys
append' (Cons x xs) ys = Cons x (append' xs ys)

data Tree a = Node a (Tree a) (Tree a)
  | Leaf

depth :: Tree Int -> Int
depth Leaf = 0
depth (Node _ a b) = 1 + (if (depth a) > (depth b) then depth a else depth b)

collapse :: Tree Int -> List Int
collapse Leaf = Nil
collapse (Node n a b) = append' (append' (collapse a) (Cons n Nil)) (collapse b)

count :: Tree Int -> Int
count Leaf = 0
count (Node _ a b) = 1 + count a + count b

mapTree :: (Int -> Int) -> Tree Int -> Tree Int
mapTree f Leaf = Leaf
mapTree f (Node x r l) = Node (f x) (mapTree f r) (mapTree f l)
