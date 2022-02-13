module ReverseVec

import Data.Vect

reverseProof : Vect (k + 1) elem -> Vect (S k) elem
reverseProof {k} xs = rewrite plusCommutative 1 k in xs

myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse {n = S k} (x :: xs) = reverseProof $ myReverse xs ++ [x]

append_xs : Vect (S (m + k)) elem -> Vect (m + (S k)) elem
append_xs {m} {k} xs =
  rewrite sym (plusSuccRightSucc m k) in xs


myAppend : Vect n elem -> Vect m elem -> Vect (m + n) elem
myAppend {m} [] ys = rewrite plusZeroRightNeutral m in ys
myAppend {n = S k} {m} (x :: xs) ys =
  append_xs (x :: myAppend xs ys)


myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite plusZeroRightNeutral m in Refl
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in
                         rewrite plusSuccRightSucc m k in Refl

consPrf : Vect (S (plus k j)) elem -> Vect (plus k (S j)) elem
consPrf {k} {j} xs = rewrite sym (plusSuccRightSucc k j) in xs


myReverse' : Vect n elem -> Vect n elem
myReverse' xs = reverse' [] xs
  where
    reverse' : (acc : Vect k elem) -> (xs : Vect j elem) -> Vect (k + j) elem
    reverse' {k} acc [] = let result = acc
                          in rewrite plusZeroRightNeutral k in result
    reverse' acc (x :: xs) = let result = reverse' (x :: acc) xs
                             in consPrf result
