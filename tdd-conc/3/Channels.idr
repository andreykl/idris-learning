module Channels

import Data.List

%language UniquenessTypes

data Actions : Type where
  DoListen : (t : proc) -> Actions -> Actions
  DoSend : (dst : proc) -> 
           (a : Type) -> (a -> Actions) -> Actions
  DoRecv : (src : proc) -> 
           (a : Type) -> (a -> Actions) -> Actions
  DoRec : Inf Actions -> Actions
  End : Actions

infixr 5 @@

data Res : (ty : Type) -> (ty -> Type*) -> Type* where
  (@@) : (a : ty) -> {k : ty -> Type} -> k a -> Res ty k

data Channel : (src : proc) -> (dest : proc) -> Actions -> UniqueType

data RChannel : (dest : proc) -> Actions -> Type

-- data Cmd : proc -> List proc -> List proc -> Type* -> Type* where
--   CConnect : RChannel srv p -> Cmd me xs (srv :: xs) (Channel me srv p)
--   CClose : Channel me srv End -> 
--           {auto prf : Elem srv xs} ->
--           Cmd me xs (dropElem xs prf) ()
--   CListen : Channel me t (DoListen t k) -> {auto prf : Elem t xs} -> 
--            Cmd me xs xs 
--              (Res Bool (\ok => 
--                if ok 
--                  then Channel me t k 
--                  else Channel me t (DoListen t k)))
--   CSend : (val : a) -> Channel me t (DoSend t a k) -> 
--          Cmd me xs xs (Channel me t (k val))
--   CRecv : Channel me t (DoRecv t a k) -> 
--          Cmd me xs xs (Res a (\val => Channel me t (k val)))
  
--   CPrint : String -> Cmd me xs xs ()
--   CGetLine : Cmd me xs xs String
  -- Pure : a -> Cmd me xs xs a
  -- (>>=) : Cmd me xs xs' a -> (a -> Cmd me xs' xs'' b) -> Cmd me xs xs'' b

data Protocol : List proc -> Type -> Type where
  Initiate : (c : proc) -> (s : proc) -> Protocol [c, s] () -> Protocol xs ()
  Send : (src : proc) -> (dst : proc) -> (a : Type) -> 
         {auto prf : Elem src xs} ->
         {auto prf : Elem dst xs} ->
         Protocol xs a
  Done : Protocol xs ()

  Rec : Inf (Protocol xs a) -> Protocol xs a
  Pure : a -> Protocol xs a
  (>>=) : Protocol xs a -> (a -> Protocol xs b) -> Protocol xs b


data Literal : String -> Type where
  MkLit : (msg : String) -> Literal msg

syntax [from] "==>" [to] "|" [ty] = Send from to ty

echo : Protocol ['C, 'S] ()
echo = do
  msg <- 'C ==> 'S | String
  'S ==> 'C | Literal msg
  'S ==> 'C | Nat
  Done

protoAs : Protocol xs a -> (pr : proc) -> 
          {auto prf : Elem pr xs} -> Actions
protoAs proto pr = protoAsHelper proto pr (\_ => End) where
  protoAsHelper : Protocol xs a -> (x : proc) -> (a -> Actions) -> Actions
  protoAsHelper (Initiate c s proto1) x k with (prim__syntactic_eq _ _ s x)
    protoAsHelper (Initiate c s proto1) x k | Nothing = protoAsHelper proto1 x k
    protoAsHelper (Initiate c x proto1) x k | (Just Refl) = DoListen c (protoAsHelper proto1 x k)
  protoAsHelper (Send from to a) x k with (prim__syntactic_eq _ _ from x)
    protoAsHelper (Send from to a) x k | Nothing = DoRecv from a (\val => k val)
    protoAsHelper (Send x to a) x k | (Just Refl) = DoSend to a (\val => k val)
  protoAsHelper Done x k = k () -- should be k () because we just do not have any other actions to add
  protoAsHelper (Rec y) x k = DoRec (protoAsHelper y x k)
  protoAsHelper (Pure y) x k = k y
  protoAsHelper (y >>= f) x k = protoAsHelper y x (\val => protoAsHelper (f val) x k)

serverLoop : (c : proc) -> Protocol [c, s] () -> Protocol [c, s] ()
serverLoop c {s} proto = do
  Initiate c s (do proto; Rec (serverLoop c proto))

namespace CIO
  data CIO : proc -> List proc -> List proc -> Type* -> Type* where
    Fork : (proto : Protocol [c, s] ())                             -> 
           (Channel s c (protoAs proto s) -> CIO s (c :: xs) xs ()) ->
           CIO c xs (s :: xs) (Channel c s (protoAs proto c))
    StartServer : (proto : Protocol [c, s] ())                      ->
                  (Channel s c (protoAs (serverLoop c proto) s) -> 
                    CIO s (c :: xs) (c :: xs) Void)                 ->
                  CIO c xs xs (RChannel s (protoAs proto c))

    Send : (val : a) -> Channel me t (DoSend t a k) ->
           CIO me xs xs (Channel me t (k val))
    Recv : Channel me t (DoRecv t a k) -> 
           CIO me xs xs (Res a (\val => Channel me t (k val)))
    Listen : (c : Channel me t (DoListen t k)) ->
             {auto prf : Elem t xs} ->
             CIO me xs xs (Res Bool (\ok => 
               if ok 
               then Channel me t k 
               else Channel me t (DoListen t k)))
    Connect : (c : RChannel t p) ->
              CIO me xs (t :: xs) (Channel me t p)
    Close : (c : Channel me t End) -> 
            {auto prf : Elem t xs} -> 
            CIO me xs (dropElem xs prf) ()
    
    Pure : a -> CIO me xs xs a
    (>>=) : CIO me xs xs' a -> (a -> CIO me xs' xs'' b) -> CIO me xs xs'' b

reset : Channel s t (DoRec act) -> Channel s t act

Server : (s, c : proc) -> Protocol [c, s] () -> Type*
Server s c p = {xs : _} -> Channel s c (protoAs (serverLoop c p) s) ->
               CIO s (c :: xs) (c :: xs) Void

Client : (c, s : proc) -> Protocol [c, s] () -> Type*
Client c s p = {xs : _} -> RChannel s (protoAs p c) -> CIO c xs xs ()

echo_server : Server 'C 'S echo
echo_server chan = do
  (True @@ chan) <- Listen chan
    | (False @@ chan) => echo_server chan
  ?next
  -- (msg @@ chan) <- Recv chan
  -- ?next
  -- chan <- Send (MkLit msg)
  -- chan <- Send 3
  -- let chan = reset chan
  -- echo_server chan
