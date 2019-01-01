module CCP

import Data.List
import Protocol
import Channels

%language UniquenessTypes

data CIO : (p : proc) -> List proc -> List proc -> Type* -> Type* where

listenRes : proc -> proc -> Actions -> Bool -> Type*
listenRes me t k True = Channel me t k
listenRes me t k False = Channel me t (DoListen t k)

fork : (proto : Protocol [c, s] ())   ->
    (Channel s c (protoAs s proto) ->
      CIO s (c :: xs) xs ())      ->
    CIO c xs xs (RChannel s (protoAs c proto))

start_server : (proto : Protocol [c, s] ()) ->
               (Channel s c (protoAs s (serverLoop c proto)) ->
                 CIO s (c :: xs) (c :: xs) Void) ->
               CIO c xs xs (RChannel s (protoAs c proto))

send : (val : a) -> 
       Channel me t (DoSend t a k) ->
       CIO me xs xs (Channel me t (k val))
-- recv : (c : Channel me t (DoRecv t a k)) ->
--        CIO me xs xs (Res a (\v => Channel me t (k v)))
recv : (c : Channel me t (DoRecv t a k)) -> 
       CIO me xs xs (Res a (\v => Channel me t (k v)))       
listen : (c : Channel me t (DoListen t k)) ->
         {auto prf : Elem t xs} ->
         CIO me xs xs (Res Bool (listenRes me t k))
connect : (c : RChannel t p) -> 
          CIO me xs (t :: xs) (Channel me t p)
close : (c : Channel me t End) -> 
        {auto prf : Elem t xs} ->
        CIO me xs (dropElem xs prf) ()

reset : Channel s t (DoRec act) -> Channel s t act

(>>=) : CIO me xs xs' a ->
        (a -> CIO me xs' xs'' b) ->
        CIO me xs xs'' b

Conc : Type -> Type -> Type
Conc p r = {xs : _} -> CIO p xs xs r

-- Server : (s, c : proc) -> Protocol [c, s] () -> Type*
-- Server s c p = {xs : _} -> 
--                Channel s c (protoAs s (serverLoop c p)) ->
--                CIO s (c :: xs) (c :: xs) Void
Server : (s, c : proc) -> Protocol [c, s] () -> Type*
Server s c p = {xs : _} ->
               Channel s c (protoAs s (serverLoop c p)) ->
               CIO s (c :: xs) (c :: xs) Void

-- Client : (c, s : proc) -> Protocol [c, s] () -> Type*
-- Client c s p = {xs : _} -> RChannel s (protoAs c p) -> CIO c xs xs ()
Client : (c, s : proc) -> Protocol [c, s] () -> Type*
Client c s p = {xs : _} ->
               RChannel s (protoAs c p) ->
               CIO c xs xs ()

echo_server : Server 'S 'C Protocol.echo
echo_server  chan
  = do (True @@ chan) <- listen  chan
             | (False  @@ chan) => echo_server  chan
       (msg @@ chan) <- recv  chan
       chan  <- send (MkLit  msg) chan
       chan <- send 25 chan
       let  chan = reset  chan
       echo_server  chan
