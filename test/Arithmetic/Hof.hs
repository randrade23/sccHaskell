module Hello where

f1 :: (Int -> Int) -> Int
f1 g = (g 1) - 1

f2 :: Int
f2 = f1 (\x -> x - 1)
