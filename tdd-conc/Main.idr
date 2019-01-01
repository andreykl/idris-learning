module Main

%language UniquenessTypes

data DoorState = Open | Closed

data DoorH : DoorState -> UniqueType

infixl 5 @@

data Res : (a : Type*) -> (a -> Type*) -> Type* where
  (@@) : (val : a) -> k val -> Res a k

data DoorCmd : UniqueType -> UniqueType where
  OpenDoor : DoorH Closed -> DoorCmd (Res Bool (\ok => if ok then DoorH Open else DoorH Closed))
  CloseDoor : DoorH Open -> DoorCmd (DoorH Closed)
  Knock : DoorH Closed -> DoorCmd (DoorH Closed)

data DoorLang : UniqueType -> UniqueType where
  Return : {a : UniqueType} -> a -> DoorLang a
  Action : DoorCmd a -> DoorLang a
  (>>=) : DoorLang a -> (a -> DoorLang b) -> DoorLang b

doorOK : DoorH Closed -> DoorLang (DoorH Closed)
doorOK closedDoor = do
  h <- Action (Knock closedDoor)
  (True @@ h) <- Action (OpenDoor h)
    | (False @@ h) => Return h
  h <- Action (CloseDoor h)
  Return h

doorBad : DoorH Closed -> DoorLang (DoorH Closed)
doorBad doorClosed = do
  h <- Action (Knock doorClosed)
  (True @@ h) <- Action (OpenDoor h)
    | (False @@ h) => Return h
  h <- Action (CloseDoor h)
  Return h
