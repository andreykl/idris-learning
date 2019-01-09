module Channels

import Protocol
import Data.List

infixr 5 @@

data Res : (a : Type) -> (a -> Type) -> Type where
  (@@) : (val : a) -> k val -> Res a k
 
data Channel : (src : proc) -> (dest : proc) -> Actions -> Type where

data RChannel : (dest : proc) -> Actions -> Type where
  
data CIO : proc -> List proc -> List proc -> Type -> Type where
  Fork : (proto : Protocol [c, s] ()) ->
         (Channel s c (protoAs proto s) -> CIO s (c :: xs) xs ()) ->
         CIO s xs (s :: xs) (Channel c s (protoAs proto c))
  StartServer : (proto : Protocol [c, s] ()) ->
                (Channel s c (protoAs (serverLoop c proto) s) ->
                  CIO s (c :: xs) (c :: xs) Void) ->
                CIO c xs xs (RChannel s (protoAs proto c))
 
  Send : (val : a) -> Channel me t (DoSend t a k) ->
         CIO me xs xs (Channel me t (k val))
  Recv : Channel me t (DoRecv t a k) ->
         CIO me xs xs (Res a (\val => Channel me t (k val)))
  Listen : (c : Channel me t (DoListen t k)) ->
           {auto prf : Elem t xs} ->
           CIO me xs xs (Res Bool (\ok => if ok then Channel me t k else Channel me t (DoListen t k)))
  Connect : (c : RChannel t p) -> CIO me xs (t :: xs) (Channel me t p)
  Close : (c : Channel me t End) -> CIO me xs (dropElem xs prf) ()

  Pure : a -> CIO me xs xs a
  (>>=) : CIO me xs xs' a -> (a -> CIO me xs' xs'' b) -> CIO me xs xs'' b

reset : Channel s t (DoRec act) -> Channel s t act

Server : (s, c : proc) -> Protocol [c, s] () -> Type
Server s c p = {xs : _} -> Channel s c (protoAs (serverLoop c p) s) -> CIO s (c :: xs) (c :: xs) Void

Client : (c, s : proc) -> Protocol [c, s] () -> Type
Client c s p = {xs : _} -> RChannel s (protoAs p c) -> CIO c xs xs ()

echo_server : Server 'C 'S echo
echo_server chan = do
  (True @@ chan) <- Listen chan
    | (False @@ chan) => echo_server chan
  (msg @@ chan) <- Recv chan
  ?next
