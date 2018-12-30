module Main

%language UniquenessTypes

data DoorState = Open | Closed

data DoorH : DoorState -> UniqueType

data DoorCmd : UniqueType -> UniqueType where
  OpenDoor : DoorH Closed -> DoorCmd (DoorH Open)
  CloseDoor : DoorH Open -> DoorCmd (DoorH Closed)
  Knock : DoorH Closed -> DoorCmd (DoorH Closed)

data DoorLang : Type* -> Type* where
  Return : a -> DoorLang a
  Action : DoorCmd a -> DoorLang a
  (>>=) : DoorLang a -> (a -> DoorLang b) -> DoorLang b

doorOK : DoorH Closed -> DoorLang ()
doorOK closedDoor = do
  h <- Action (Knock closedDoor)
  h <- Action (OpenDoor h)
  Action (CloseDoor h)
  Return ()

doorBad : DoorH Closed -> DoorLang ()
doorBad doorClosed = do
  h <- Action (Knock doorClosed)
  h <- Action (OpenDoor h)
  h <- Action (CloseDoor h)
  Return ()
