module Main

import System

main : IO ()
main = do
  putStr "Enter your name: "
  x <- getLine
  putStrLn ("Hello " ++ x ++ "!")

printLength : IO ()
printLength = getLine >>= \result => let len = length result in
                                         putStrLn (show len)

printLonger : IO ()
printLonger = do putStr "Input string 1: "
                 input1 <- getLine
                 putStr "Input string 2: "
                 input2 <- getLine
                 let [length1, length2] = map length [input1, input2]
                 let maxLen = max length1 length2
                 putStrLn ("Longer length is " ++ (show maxLen))

printLonger' : IO ()
printLonger' = putStr "First string: "
               >>= \_ => getLine
               >>= \input1 => putStr "Second string: "
               >>= \_ => getLine
               >>= \input2 =>
                 let [length1, length2] = map length [input1, input2]
                     maxLen = max length1 length2 in
                     putStrLn ("Longer length is " ++ (show maxLen))

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
     then pure (Just (cast input))
     else pure Nothing

readNumbers : IO (Maybe (Nat, Nat))
readNumbers =
  do Just num1 <- readNumber | Nothing => pure Nothing
     Just num2 <- readNumber | Nothing => pure Nothing
     pure (Just (num1, num2))

countdown : (secs : Nat) -> IO ()
countdown Z = putStrLn "Lift off!"
countdown (S secs) = do printLn (S secs)
                        usleep 1000000
                        countdown secs

guess : (target : Nat) -> (guessCount : Nat) -> IO ()
guess target guessCount =
  do putStr "Guess the number: "
     Just num <- readNumber | Nothing => putStrLn "Not a number"
     if num < 1 || num > 100
        then do putStrLn "Number has to be between 1 and 100"
                guess target guessCount
     else if num < target
        then do putStrLn "Too low"
                guess target (S guessCount)
     else if num > target
        then do putStrLn "Too high"
                guess target (S guessCount)
    else putStrLn $ "You got it with " ++ show (S guessCount) ++ " guesses!"

randomGuess : IO ()
randomGuess =
  do t <- time
     let target = mod t 100 + 1
     guess (cast target) Z

repl' : (prompt: String) -> (onInput: String -> String) -> IO ()
repl' prompt onInput =
  do putStr (prompt ++ ": ")
     input <- getLine
     putStrLn (onInput input)
     repl' prompt onInput

replWith' : (state: a) -> (prompt: String) -> (onInput: a -> String -> Maybe (String, a)) -> IO ()
replWith' state prompt onInput =
  do putStr (prompt ++ ": ")
     input <- getLine
     let Just (output, state') = onInput state input | Nothing => pure ()
     replWith' state' prompt onInput
