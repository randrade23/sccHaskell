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

length2 :: List Int -> Int
length2 Nil = 0
length2 (Cons _ k) = 1 + length2 k

length3 :: List Int -> Int
length3 Nil = 0
length3 (Cons _ w) = 1 + length3 w

append' :: List Int -> List Int -> List Int
append' Nil ys = ys
append' (Cons x xs) ys = Cons x (append' xs ys)

app = append' Nil (Cons 3 Nil)
app2 = append' (Cons 3 Nil) Nil
