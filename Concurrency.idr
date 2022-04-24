module Concurrency

import System.Concurrency.Channels

%default total

data MessagePID = MkMessage PID

data Message = Add Nat Nat

data Process : Type -> Type where
  Request : MessagePID -> Message -> Process (Maybe Nat)
  Respond : ((msg : Message) -> Process Nat) -> Process (Maybe Message)
  Spawn : Process () -> Process (Maybe MessagePID)
  Loop : Inf (Process a) -> Process a
  Action : IO a -> Process a
  Pure : a -> Process a
  (>>=) : Process a -> (a -> Process b) -> Process b  

data Fuel = Dry | More (Lazy Fuel)

data Option a = None | Some a

run : Fuel -> Process t -> IO (Option t)
run Dry _ = pure None
run fuel (Action act) = do
  res <- act
  pure $ Some res
run fuel (Pure val) = pure (Some val)
run fuel (act >>= next) = do
  Some val <- run fuel act
    | None => pure None
  run fuel (next val)
run fuel (Spawn proc) = do
  Just pid <- spawn (run fuel proc *> pure ())
    | Nothing => pure None
  pure (Some $ Just $ MkMessage pid)
run fuel (Request (MkMessage pid) msg) = do
  Just chan <- connect pid
    | Nothing => pure (Some Nothing)
  ok <- unsafeSend chan msg
  if ok then do
    Just val <- unsafeRecv Nat chan
      | Nothing => pure (Some Nothing)
    pure (Some (Just val))
  else
    pure (Some Nothing)
run fuel (Respond f) = do
  Just chan <- listen 1
    | Nothing => pure (Some Nothing)
  Just msg <- unsafeRecv Message chan
    | Nothing => pure (Some Nothing)
  Some res <- run fuel (f msg)
    | None => pure None
  unsafeSend chan res
  pure (Some (Just msg))
run (More fuel) (Loop act) = run fuel act

procAdder : Process ()
procAdder = do
  Respond (\msg => case msg of
    Add x y => Pure (x + y))
  Loop procAdder

procMain : Process ()
procMain = do
  Just adderId <- Spawn procAdder
    | Nothing => Action (putStrLn "Failed to spawn adder")
  Just answer <- Request adderId (Add 2 3)
    | Nothing => Action (putStrLn "Request failed")
  Action (putStrLn $ "The answer is " ++ show answer)

partial
forever : Fuel
forever = More forever

partial
runProc : Process () -> IO ()
runProc proc = do
  run forever proc
  pure ()

procAdderBad1 : Process ()
procAdderBad1 = do
  Action (putStrLn "I'm out of the office today")
  Loop procAdderBad1
