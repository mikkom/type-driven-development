module Streams

import Data.Primitives.Views

labelFrom : Integer -> List a -> List (Integer, a)
labelFrom n [] = []
labelFrom n (x :: xs) = (n, x) :: labelFrom (n + 1) xs

labelSimple : List a -> List (Integer, a)
labelSimple = labelFrom 0

data InfList : Type -> Type where
     (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

%name InfList xs, ys, zs

countFrom' : Integer -> InfList Integer
countFrom' n = n :: countFrom' (n + 1)

getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z lst = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith s [] = []
labelWith (l :: ls) (x :: xs) = (l, x) :: labelWith ls xs

label : List a -> List (Integer, a)
label = labelWith [0..]

quiz : Stream Int -> (score : Nat) -> IO ()
quiz (num1 :: num2 :: nums) score = do
  putStrLn ("Score so far: " ++ show score)
  putStr (show num1 ++ " * " ++ show num2 ++ "? ")
  answer <- getLine
  if answer == ""
     then pure ()
  else if cast answer == num1 * num2
          then do
            putStrLn "Correct!"
            quiz nums (score + 1)
          else do
            putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
            quiz nums score

randoms : Int -> Stream Int
randoms seed =
  let seed' = 1664525 * seed + 1013904223 in
      (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12)
          bound ((12 * div) + rem) | (DivBy prf) = rem + 1

everyOther : Stream a -> Stream a
everyOther (x :: y :: ys) = y :: everyOther ys

Functor InfList where
  map f (value :: xs) = f value :: map f xs

data Face = Heads | Tails

total
getFace : Int -> Face
getFace num with (divides num 2)
  getFace ((2 * div) + 0) | (DivBy prf) = Heads
  getFace ((2 * div) + _) | (DivBy prf) = Tails

coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips count stream = take count $ map getFace stream

squareRootApprox : (number : Double) -> (approx : Double) -> Stream Double
squareRootApprox number approx = approx :: squareRootApprox number next
  where
    next : Double
    next = (approx + (number / approx)) / 2

squareRootBound : (max : Nat) -> (number : Double) -> (bound : Double) ->
                  (approxs : Stream Double) -> Double
squareRootBound Z number bound (value :: xs) = value
squareRootBound (S max) number bound (value :: xs) =
  if abs (value * value - number) < bound
    then value
    else squareRootBound max number bound xs

squareRoot : (number : Double) -> Double
squareRoot number =
  squareRootBound 100 number 0.00000000001
    (squareRootApprox number number)
