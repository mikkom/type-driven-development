import Data.Vect

fourInts : Vect 4 Int
fourInts = [0, 1, 2, 3]

sixInts : Vect 6 Int
sixInts = [4, 5, 6, 7, 8, 9]

tenInts : Vect 10 Int
tenInts = fourInts ++ sixInts

total allLengths : Vect len String -> Vect len Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words

insSort : Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) = insert x (insSort xs)
  where
    insert : elem -> Vect k elem -> Vect (S k) elem
    insert x [] = [x]
    insert x (y :: ys) = if x < y then x :: y :: ys
                                  else y :: insert x ys
