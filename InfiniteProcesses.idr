module InfiniteProcesses

import Data.Primitives.Views
import System

%default total

data InfIO : Type where
     Do : IO a -> (a -> Inf InfIO) -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

loopPrint : String -> InfIO
loopPrint msg = do
  putStrLn msg
  loopPrint msg

partial
runNonTotal : InfIO -> IO ()
runNonTotal (Do action cont) = do
  res <- action
  runNonTotal (cont res)

data Fuel = Dry | More (Lazy Fuel)

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

run : Fuel -> InfIO -> IO ()
run Dry actions = putStrLn "Out of fuel"
run (More fuel) (Do action cont) = do
  res <- action
  run fuel (cont res)

partial
forever : Fuel
forever = More forever

quiz : Stream Int -> (score : Nat) -> InfIO
quiz (num1 :: num2 :: nums) score = do
  putStrLn ("Score so far: " ++ show score)
  putStr (show num1 ++ " * " ++ show num2 ++ "? ")
  answer <- getLine
  if cast answer == num1 * num2
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

partial
main : IO ()
main = do
  seed <- time
  let inputStream = arithInputs $ fromInteger seed
  run forever (quiz inputStream 0)

totalRepl : (prompt : String) -> (action : String -> String) -> InfIO
totalRepl prompt action = do
  putStr prompt
  line <- getLine
  putStrLn $ action line
  totalRepl prompt action
