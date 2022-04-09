module ATM

import Data.Vect

Pin : Type
Pin = Vect 4 Char

data AtmState = Ready | CardInserted | Session

data PinCheck = CorrectPin | IncorrectPin

data HasCard : AtmState -> Type where
     HasCI : HasCard CardInserted
     HasSession : HasCard Session

data AtmCmd : (ty : Type) -> AtmState -> (ty -> AtmState) -> Type where
     InsertCard : AtmCmd () Ready (const CardInserted)
     EjectCard : {auto prf : HasCard state} -> AtmCmd () state (const Ready)
     GetPin: AtmCmd Pin CardInserted (const CardInserted)
     CheckPin : Pin -> AtmCmd PinCheck CardInserted
                       (\check => case check of
                                       CorrectPin => Session
                                       IncorrectPin => CardInserted)
     GetAmount : AtmCmd Nat state (const state)
     Dispense : (amount : Nat) -> AtmCmd () Session (const Session)

     Message : String -> AtmCmd () state (const state)
     Pure : (res : ty) -> AtmCmd ty (f res) f
     (>>=) : AtmCmd a state f ->
             ((res : a) -> AtmCmd b (f res) f') ->
             AtmCmd b state f'

atm : AtmCmd () Ready (const Ready)
atm = do
  InsertCard
  pin <- GetPin
  pinOk <- CheckPin pin
  Message "Checking Card"
  case pinOk of
       CorrectPin => do
         amount <- GetAmount
         Dispense amount
         EjectCard 
         Message "Please remove your card and cash"
       IncorrectPin => do
         Message "Incorrect PIN"
         EjectCard 

testPin : Pin
testPin = ['1', '2', '3', '4']

readVect : (n : Nat) -> IO (Vect n Char)
readVect Z = pure []
readVect (S k) = do
  c <- getChar
  cs <- readVect k
  pure (c :: cs)

runAtm : AtmCmd res state f -> IO res
runAtm InsertCard = do
  putStrLn "Please insert your card (press enter)"
  ignore getLine
runAtm EjectCard = putStrLn "Card ejected"
runAtm GetPin = do
  putStr "Enter PIN: "
  readVect 4
runAtm (CheckPin pin) =
  if pin == testPin
     then pure CorrectPin
     else pure IncorrectPin
runAtm GetAmount = do
  putStr "How much would you like? "
  x <- getLine
  pure (cast x)
runAtm (Dispense amount) = putStrLn ("Here is " ++ show amount)
runAtm (Message msg) = putStrLn msg
runAtm (Pure res) = pure res
runAtm (x >>= f) = do
  x' <- runAtm x
  runAtm (f x')
