module Concurrency

import System.Concurrency.Channels

%default total

data ProcState = NoRequest | Sent | Complete

data MessagePID = MkMessage PID

data Message = Add Nat Nat

data Process : Type ->
               (inState : ProcState) ->
               (outState : ProcState) ->
               Type where
  Request : MessagePID -> Message -> Process Nat st st
  Respond : ((msg : Message) -> Process Nat NoRequest NoRequest) ->
            Process (Maybe Message) st Sent
  Spawn : Process () NoRequest Complete -> Process (Maybe MessagePID) st st
  Loop : Inf (Process a NoRequest Complete) -> Process a Sent Complete
  Action : IO a -> Process a st st
  Pure : a -> Process a st st
  (>>=) : Process a st1 st2 -> (a -> Process b st2 st3) -> Process b st1 st3

data Fuel = Dry | More (Lazy Fuel)

data Option a = None | Some a

run : Fuel -> Process t st st' -> IO (Option t)
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
    | _ => pure None 
  ok <- unsafeSend chan msg
  if ok then do
    Just val <- unsafeRecv Nat chan
      | _ => pure None
    pure (Some val)
  else
    pure None
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

Service : Type -> Type
Service a = Process a NoRequest Complete

Client : Type -> Type
Client a = Process a NoRequest NoRequest

procAdder : Service ()
procAdder = do
  Respond (\msg => case msg of
    Add x y => Pure (x + y))
  Loop procAdder

procMain : Client ()
procMain = do
  Just adderId <- Spawn procAdder
    | Nothing => Action (putStrLn "Failed to spawn adder")
  answer <- Request adderId (Add 2 3)
  Action (putStrLn $ "The answer is " ++ show answer)

partial
forever : Fuel
forever = More forever

partial
runProc : Process () st st' -> IO ()
runProc proc = do
  run forever proc
  pure ()
