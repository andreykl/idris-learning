module Channels

import Data.List
import Protocol

data Channel : (src : proc) -> (dst : proc) -> Actions -> Type

data RChannel : (dst : proc) -> Actions -> Type

infixr 5 @@

data Res : (a : Type) -> (a -> Type) -> Type where
  (@@) : (val : a) -> k val -> Res a k

data CIO : (p : proc) -> List proc -> List proc -> Type -> Type where
  Fork : (proto : Protocol [c, s] ()) ->
         (Channel s c (protoAs s (serverLoop c proto)) ->
                  CIO s (c :: xs) (c :: xs) Void) ->
         CIO c xs xs (RChannel s (protoAs c proto))
  StartServer : (proto : Protocol [c, s] ()) ->
                (Channel s c (protoAs s (serverLoop c proto)) ->
                  CIO s (c :: xs) (c :: xs) Void) ->
                CIO c xs (s :: xs) (Channel c s (protoAs c proto))
  Send : (val : a) -> Channel me t (DoSend t a k) ->
         CIO me xs xs (Channel me t (k val))
  Recv : (c : Channel me t (DoRecv t a k)) -> 
         CIO me xs xs (Res a (\v => Channel me t (k v)))
  Listen : Channel me t (DoListen t act) -> 
           {auto prf : Elem t xs} ->
           CIO me xs xs (Channel me t act)

  Connect : RChannel t acts -> CIO me xs (t :: xs) (Channel me t acts)
  Close : Channel me t End -> {auto prf : Elem t xs} -> CIO me xs (dropElem xs prf) ()

  Pure : a -> CIO me xs xs a
  (>>=) : CIO me xs xs' a -> (a -> CIO me xs' xs'' b) -> CIO me xs xs'' b
  -- Pure
  -- (>>=)
  
reset : Channel xs xs' (DoRec act) -> Channel xs xs' act
reset ch = ?reset_rhs_1

Server : (s, c : proc) -> Protocol [c, s] () -> Type
Server s c proto = {xs : _} -> Channel s c (protoAs s (serverLoop c proto)) 
                            -> CIO s (c :: xs) (c :: xs) Void

Client : (c, s : proc) -> Protocol [c, s] () -> Type
Client c s proto = {xs : _} -> RChannel s (protoAs c proto) -> CIO c xs xs ()

echo_server : Server 'S 'C Protocol.echo
echo_server chan = 
  do chan <- Listen chan
     (msg @@ chan) <- Recv chan
     chan <- Send (MkLit msg) chan
     chan <- Send (length msg) chan
     let chan86 = reset chan
     ?next
     --echo_server chan86
