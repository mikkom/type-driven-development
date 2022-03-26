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
     ReadFile : String -> Command (Either FileError String)
     WriteFile : String -> String -> Command (Either FileError ())
     Pure : ty -> Command ty
     Bind : Command a -> (a -> Command b) -> Command b

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

mutual
  Functor Command where
    map f cmd = do
      x <- cmd
      pure (f x)

  Applicative Command where
    pure = Pure
    mf <*> mx = do
      f <- mf
      x <- mx
      pure (f x)
  
  Monad Command where
    (>>=) = Bind

data ConsoleIO : Type -> Type where
     Quit : a -> ConsoleIO a
     Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

runCommand : Command a -> IO a
runCommand (PutStr str) = putStr str
runCommand GetLine = getLine
runCommand (ReadFile filename) = readFile filename
runCommand (WriteFile filename contents) = writeFile filename contents
runCommand (Pure x) = pure x
runCommand (Bind c f) = do
  res <- runCommand c
  runCommand (f res)

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run Dry actions = pure Nothing
run (More fuel) (Quit x) = pure (Just x)
run (More fuel) (Do cmd cont) = do
  res <- runCommand cmd 
  run fuel (cont res)

data Input = Answer Int | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do
  PutStr prompt
  answer <- GetLine
  if toLower answer == "quit"
     then Pure QuitCmd
     else Pure (Answer (cast answer))

showScore : (Nat, Nat) -> String
showScore (score, attempts) = show score ++ " / " ++ show attempts

mutual
  correct : Stream Int -> (score: (Nat, Nat)) -> ConsoleIO (Nat, Nat)
  correct nums (score, attempts) = do
    PutStr "Correct!\n"
    quiz nums ((score + 1), (attempts + 1))

  wrong: Stream Int -> Int -> (score : (Nat, Nat)) -> ConsoleIO (Nat, Nat)
  wrong nums ans (score, attempts) = do
    PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
    quiz nums (score, (attempts + 1))

  quiz : Stream Int -> (score : (Nat, Nat)) -> ConsoleIO (Nat, Nat)
  quiz (num1 :: num2 :: nums) score = do
    PutStr ("Score so far: " ++ showScore score ++ "\n")
    input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
    case input of
      Answer answer =>
        if answer == num1 * num2
           then correct nums score
           else wrong nums (num1 * num2) score
      QuitCmd => Quit score

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
  Just score <- run forever (quiz inputStream (0, 0))
    | Nothing => putStrLn "Ran out of fuel"
  putStrLn ("Final score: " ++ showScore score)

shell : ConsoleIO ()
shell = do
  PutStr "> "
  command <- GetLine
  case split (== ' ') command of
    ["cat", filename] => do
      Right contents <- ReadFile filename | Left error => Quit ()
      PutStr contents
      shell
    ["copy", source, destination] => do
      Right contents <- ReadFile source | Left error => Quit ()
      Right () <- WriteFile destination contents | Left error => Quit ()
      shell
    ["exit"] => Quit ()
    _ => do
      PutStr "Invalid command\n"
      shell
