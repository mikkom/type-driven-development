module HandlingErrors

data DoorResult = OK | Jammed

data DoorState = DoorClosed | DoorOpen

data DoorCmd : (ty: Type) -> DoorState -> (ty -> DoorState) -> Type where
    Open : DoorCmd DoorResult DoorClosed
           (\res => case res of
                         OK => DoorOpen
                         Jammed => DoorClosed)
    Close : DoorCmd () DoorOpen (const DoorClosed)
    RingBell : DoorCmd () DoorClosed (const DoorClosed)

    Display : String -> DoorCmd () state (const state)

    Pure : (res : ty) -> DoorCmd ty (f res) f
    (>>=) : DoorCmd a state1 f ->
            ((res : a) -> DoorCmd b (f res) f') ->
            DoorCmd b state1 f'

doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do
  RingBell
  OK <- Open | Jammed => Display "Door jammed"
  Display "Glad to be of service"
  Close

logOpen : DoorCmd DoorResult DoorClosed
          (\res => case res of
                        OK => DoorOpen
                        Jammed => DoorClosed)
logOpen = do
  Display "Trying to open the door"
  OK <- Open | Jammed => do
    Display "Jammed"
    Pure Jammed
  Display "Success"
  Pure OK 
