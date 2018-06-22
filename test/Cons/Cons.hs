module Cons where

data List a = Cons a (List a) | Nil

not' :: Bool -> Bool
not' False = True
not' True = False

null' :: List Int -> Bool
null' Nil = True
null' (Cons _ _) = False

head' :: List Int -> Int
head' (Cons n l) = n

length' :: List Int -> Int
length' Nil = 0
length' (Cons _ y) = 1 + length' y

append' :: List Int -> List Int -> List Int
append' Nil ys = ys
append' (Cons x xs) ys = Cons x (append' xs ys)

reverse' :: List Int -> List Int
reverse' Nil = Nil
reverse' (Cons x xs) = append' (reverse' xs) (Cons x Nil)

map' :: (Int -> Int) -> List Int -> List Int
map' f Nil = Nil
map' f (Cons x xs) = Cons (f x) (map' f xs)

app = append' Nil (Cons 3 Nil)
app2 = append' (Cons 3 Nil) Nil
