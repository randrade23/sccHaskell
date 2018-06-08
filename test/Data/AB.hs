module AB where

data A = A1 | A2
data B = B1 | B2

noA2 :: A -> Bool
noA2 A1 = True
noA2 A2 = False

yesA2 :: A -> Bool
yesA2 A1 = False
yesA2 A2 = True

h1 :: A -> A
h1 A1 = A2
h1 A2 = A2

g1 :: A -> A
g1 A1 = A1
g1 A2 = A1

test = h1 (g1 A2)
