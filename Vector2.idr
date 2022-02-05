module Vector2

import Data.Vect

data Vector : Nat -> Type -> Type where
     Nil    : Vector Z a
     (::) : a -> Vector k a -> Vector (S k) a

%name Vector xs, ys, zs

zip : Vector n a -> Vector n b -> Vector n (a, b)
zip [] [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex i {n} v = case integerToFin i n of
                   Nothing => Nothing
                   Just f => Just $ index f v

tryIndex' : Integer -> Vect n a -> Maybe a
tryIndex' i {n} v = (flip index) v <$> integerToFin i n

flap : Functor f => f (a -> b) -> a -> f b
flap f x = map (\f => f x) f

tryIndex'' : Integer -> Vect n a -> Maybe a
tryIndex'' i {n} = flap $ index <$> integerToFin i n

vectTake : (len : Fin (S n)) -> Vect n a -> Vect (finToNat len) a
vectTake FZ _ = []
vectTake (FS len') (x :: xs) = x :: vectTake len' xs

sumEntries : Num a => (pos: Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = case integerToFin pos n of
                           Nothing => Nothing
                           Just pos => Just $ index pos xs + index pos ys
