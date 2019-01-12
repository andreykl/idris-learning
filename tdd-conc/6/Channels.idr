module Channels

import Data.List
import Protocol

%default total

data Channel : proc -> proc -> Actions -> Type

data RChannel : proc -> Actions -> Type

infixr 5 @@

data Res : (a : Type) -> (a -> Type) -> Type where
  (@@) : (val : a) -> k val -> Res a k


data CIO : proc -> List proc -> List proc -> Type -> Type where
  Fork : (proto : Protocol [c, s] ()) -> 
         (Channel s c (protoAs s proto) -> 
           CIO s (c :: xs) xs ()) -> 
         CIO c xs (s :: xs) (Channel c s (protoAs c proto))
  StartServer : (proto : Protocol [c, s] ()) -> 
         (Channel s c (protoAs c proto) -> 
           CIO s (c :: xs) (c :: xs) Void) -> 
         CIO c xs xs (RChannel s (protoAs c proto))

  Send : (val : a) -> Channel me t (DoSend t a k) ->
         CIO me xs xs (Channel me t (k val))
  Recv : Channel me t (DoRecv t a k) ->
         CIO me xs xs (Res a (\val => Channel me t (k val)))
  Listen : Channel me t (DoListen t acts) -> CIO me xs xs (Channel me t acts)

  Connect : RChannel t acts -> CIO me xs (t :: xs) (Channel me t acts)
  Close : Channel me t End -> {auto prf : Elem t xs} -> CIO me xs (dropElem xs prf) ()

  Pure : a -> CIO me xs xs a
  (>>=) : CIO me xs xs' a -> (a -> CIO me xs' xs'' b) -> CIO me xs xs'' b

reset : Channel c s (DoRec acts) -> Channel c s acts

Server : (s, c : proc) -> Protocol [c, s] () -> Type
Server s c proto = {xs : _} -> Channel s c (protoAs s (serverLoop c proto)) -> CIO s (c :: xs) (c :: xs) Void

Client : (c, s : proto) -> Protocol [c, s] () -> Type
Client c s proto = {xs : _} -> RChannel c (protoAs c proto) -> CIO c xs xs ()

echo_server : Server 'S 'C Protocol.echo
echo_server chan = do
  chan <- Listen chan
  (msg @@ chan) <- Recv chan
  chan <- Send (MkLit msg) chan
  chan <- Send (length msg) chan
  ?next  
  -- let ch = reset chan
  -- echo_server chan
