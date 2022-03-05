module ConsoleIO

import Data.Primitives.Views
import System

%default total

data Fuel = Dry | More (Lazy Fuel)

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

partial
forever : Fuel
forever = More forever

data Command : Type -> Type where
     PutStr : String -> Command ()
     GetLine : Command String

data ConsoleIO : Type -> Type where
     Quit : a -> ConsoleIO a
     Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

(>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
(>>=) = Do

runCommand : Command a -> IO a
runCommand (PutStr str) = putStr str
runCommand GetLine = getLine

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run Dry actions = pure Nothing
run (More fuel) (Quit x) = pure (Just x)
run (More fuel) (Do cmd cont) = do
  res <- runCommand cmd 
  run fuel (cont res)

mutual
  correct : Stream Int -> (score : Nat) -> ConsoleIO Nat
  correct nums score = do
    PutStr "Correct!\n"
    quiz nums (score + 1)

  wrong: Stream Int -> Int -> (score : Nat) -> ConsoleIO Nat
  wrong nums ans score = do
    PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
    quiz nums score

  quiz : Stream Int -> (score : Nat) -> ConsoleIO Nat
  quiz (num1 :: num2 :: nums) score = do
    PutStr ("Score so far: " ++ show score ++ "\n")
    PutStr (show num1 ++ " * " ++ show num2 ++ "? ")
    answer <- GetLine
    let ans = num1 * num2
    if toLower answer == "quit"
      then Quit score
      else if cast answer == ans
        then correct nums score
        else wrong nums ans score

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

partial
main : IO ()
main = do
  seed <- time
  let inputStream = arithInputs $ fromInteger seed
  Just score <- run forever (quiz inputStream 0)
    | Nothing => putStrLn "Ran out of fuel"
  putStrLn ("Final score: " ++ show score)
