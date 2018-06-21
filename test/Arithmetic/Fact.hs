module Fact where

fact :: Int -> Int
fact n = case n == 0 of
  True -> 1
  False -> case n > 0 of
    True -> n * fact (n-1)
    False -> error "Invalid argument"
