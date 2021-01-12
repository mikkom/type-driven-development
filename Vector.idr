module Vector

import Data.Vect

data Vector : Nat -> Type -> Type where
     Nil    : Vector Z a
     (::) : a -> Vector k a -> Vector (S k) a

%name Vector xs, ys, zs

length : Vector k a -> Nat
length {k} xs = k

append : Vector m a -> Vector n a -> Vector (m + n) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

zip : Vector n a -> Vector n b -> Vector n (a, b)
zip [] [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

index : Fin n -> Vector n a -> a
index FZ (x :: xs) = x
index (FS k) (x :: xs) = index k xs

take : (n : Nat) -> Vector (n + m) a -> Vector n a
take Z xs = Nil
take (S k) (x :: xs) = x :: take k xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys =
  (\i => index i xs + index i ys) <$> integerToFin pos n
