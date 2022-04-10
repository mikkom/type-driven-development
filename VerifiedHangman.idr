module VerifiedHangman

import Data.Vect

%default total

data GameState : Type where
     NotRunning : GameState
     Running : (guesses : Nat) -> (letters : Nat) -> GameState

letters : String -> List Char
letters str = nub (map toUpper (unpack str))

data GuessResult = Correct | Incorrect

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
     NewGame : (word : String) -> GameCmd () NotRunning
                                  (const (Running 6 (length (letters word))))
     Won : GameCmd () (Running (S guesses) 0) (const NotRunning)
     Lost : GameCmd () (Running 0 (S letters)) (const NotRunning)
     Guess : (c : Char) -> GameCmd GuessResult (Running (S guesses) (S letters))
                           (\res => case res of
                                         Correct => (Running (S guesses) letters)
                                         Incorrect => (Running guesses (S letters)))
     Pure : (res : ty) -> GameCmd ty (f res) f
     (>>=) : GameCmd a state f ->
             ((res : a) -> GameCmd b (f res) f') ->
             GameCmd b state f'
     ShowState : GameCmd () state (const state)
     Message : String -> GameCmd () state (const state)
     ReadGuess : GameCmd Char state (const state)

namespace Loop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
       (>>=) : GameCmd a state f ->
               ((res : a) -> Inf (GameLoop b (f res) f')) ->
               GameLoop b state f'
       Exit : GameLoop () NotRunning (const NotRunning)

gameLoop : GameLoop () (Running (S guesses) (S letters)) (const NotRunning)
gameLoop {guesses} {letters} = do
  ShowState
  g <- ReadGuess
  ok <- Guess g
  case ok of
    Correct =>
      case letters of
        Z => do
          Won
          ShowState
          Exit
        S k => do
          Message "Correct"
          gameLoop
    Incorrect =>
      case guesses of
        Z => do
          Lost
          ShowState
          Exit
        S k => do
          Message "Incorrect"
          gameLoop

hangman : GameLoop () NotRunning (const NotRunning)
hangman = do
  NewGame "testing"
  gameLoop

data Game : GameState -> Type where
  GameStart : Game NotRunning
  GameWon : (word : String) -> Game NotRunning
  GameLost : (word : String) -> Game NotRunning
  InProgress : (word : String) -> (guesses : Nat) ->
               (missing : Vect letters Char) ->
               Game (Running guesses letters)

Show (Game g) where
  show GameStart = "Starting"
  show (GameWon word) = "Game won: word was " ++ word
  show (GameLost word) = "Game lost: word was " ++ word
  show (InProgress word guesses missing) =
    "\n" ++ pack (map hideMissing (unpack word)) ++
    "\n" ++ show guesses ++ " guesses left"
    where
      hideMissing : Char -> Char
      hideMissing c = if c `elem` missing then '-' else c

data Fuel = Dry | More (Lazy Fuel)

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
  OK : (res : ty) -> Game (f res) -> GameResult ty f
  OutOfFuel : GameResult ty f

ok : (res : ty) -> Game (f res) -> IO (GameResult ty f)
ok res st = pure (OK res st)

removeElem : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs}
             -> Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: []) {prf = (There later)} = absurd later
removeElem {n = (S k)} value (y :: ys) {prf = (There later)} =
  y :: removeElem value ys

runCmd : Fuel -> Game inState -> GameCmd ty inState f ->
         IO (GameResult ty f)
runCmd fuel state (NewGame word) =
  ok () (InProgress (toUpper word) _ (fromList (letters word)))
runCmd fuel (InProgress word _ missing) Won = ok () (GameWon word)
runCmd fuel (InProgress word _ missing) Lost = ok () (GameLost word)
runCmd fuel (InProgress word _ missing) (Guess c) =
  case isElem c missing of
    (Yes prf) => ok Correct (InProgress word _ (removeElem c missing))
    (No contra) => ok Incorrect (InProgress word _ missing)
runCmd fuel state (Pure res) = ok res state
runCmd fuel state (cmd >>= next) = do
  OK cmdRes state' <- runCmd fuel state cmd
    | OutOfFuel => pure OutOfFuel
  runCmd fuel state' (next cmdRes)
runCmd fuel state ShowState = do
  printLn state
  ok () state
runCmd fuel state (Message str) = do
  putStrLn str
  ok () state
runCmd (More fuel) st ReadGuess = do
  putStr "Guess: "
  input <- getLine
  case unpack input of
    [x] =>
      if isAlpha x
        then ok (toUpper x) st
        else do
          putStrLn "Invalid input"
          runCmd fuel st ReadGuess
    _ => do
      putStrLn "Invalid input"
      runCmd fuel st ReadGuess
runCmd Dry _ _ = pure OutOfFuel        

run : Fuel ->
      Game inState ->
      GameLoop ty inState outState ->
      IO (GameResult ty outState)
run Dry _ _ = pure OutOfFuel
run (More fuel) st (cmd >>= next) = do
  OK cmdRes st' <- runCmd fuel st cmd
    | OutOfFuel => pure OutOfFuel
  run fuel st' (next cmdRes)
run (More fuel) st Exit = ok () st

%default partial

forever : Fuel 
forever = More forever

main : IO ()
main = do
  run forever GameStart hangman
  pure ()
