module ProcessLib

import System.Concurrency.Channels

%default total

public export
data ProcState = NoRequest | Sent | Complete

export
data MessagePID : (iface : reqType -> Type) -> Type where
  MkMessage : PID -> MessagePID iface

data Message = Add Nat Nat

AdderType : Message -> Type
AdderType (Add x y) = Nat

public export
data Process : (iface : reqType -> Type) ->
               Type ->
               (inState : ProcState) ->
               (outState : ProcState) ->
               Type where
  Request : MessagePID iSvc ->
            (msg : svcReqType) ->
            Process iface (iSvc msg) st st
  Respond : ((msg : reqType) ->
              Process iface (iface msg) NoRequest NoRequest) ->
            Process iface (Maybe reqType) st Sent
  Spawn : Process iSvc () NoRequest Complete ->
          Process iface (Maybe (MessagePID iSvc)) st st
  Loop : Inf (Process iface a NoRequest Complete) ->
         Process iface a Sent Complete
  Action : IO a -> Process iface a st st
  Pure : a -> Process iface a st st
  (>>=) : Process iface a st1 st2 ->
          (a -> Process iface b st2 st3) ->
          Process iface b st1 st3

public export
data Fuel = Dry | More (Lazy Fuel)

public export
data Option a = None | Some a

export
run : Fuel -> Process iface t st st' -> IO (Option t)
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
run fuel (Request {iSvc} (MkMessage pid) msg) = do
  Just chan <- connect pid
    | _ => pure None 
  ok <- unsafeSend chan msg
  if ok then do
    Just val <- unsafeRecv (iSvc msg) chan
      | _ => pure None
    pure (Some val)
  else
    pure None
run fuel (Respond {reqType} f) = do
  Just chan <- listen 1
    | Nothing => pure (Some Nothing)
  Just msg <- unsafeRecv reqType chan
    | Nothing => pure (Some Nothing)
  Some res <- run fuel (f msg)
    | None => pure None
  unsafeSend chan res
  pure (Some (Just msg))
run (More fuel) (Loop act) = run fuel act

public export
Service : (iface: reqType -> Type) -> Type -> Type
Service iface a = Process iface a NoRequest Complete

public export
NoRecv : Void -> Type
NoRecv = const Void

public export
Client : Type -> Type
Client a = Process NoRecv a NoRequest NoRequest

procAdder : Service AdderType ()
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

export partial
forever : Fuel
forever = More forever

export partial
runProc : Process iface () inState outState -> IO ()
runProc proc = do
  run forever proc
  pure ()
