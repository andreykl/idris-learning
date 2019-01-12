module Protocol

import Data.List

%default total
%access public export

data Protocol : List proc -> Type -> Type where
  Initiate : (c, s : proc) -> Protocol [c, s] () ->
             {auto cprf : Elem c xs} ->
             {auto sprf : Elem s xs} ->
             Protocol xs ()
  Send : (from : proc) -> 
         (to : proc) -> 
         (a : Type) ->
         {auto fprf : Elem from xs} ->
         {auto tprf : Elem to xs} ->
         Protocol xs a
  Done : Protocol xs ()
  
  Rec : Inf (Protocol xs a) -> Protocol xs a
  Pure : a -> Protocol xs a
  (>>=) : Protocol xs a -> (a -> Protocol xs b) -> Protocol xs b

syntax [from] "==>" [to] "|" [ty] = Send from to ty

data Literal : String -> Type where
  MkLit : (msg : String) -> Literal msg

echo : Protocol ['C, 'S] ()
echo = do
  msg <- 'C ==> 'S | String
  'S ==> 'C | Literal msg
  'S ==> 'C | Nat
  Done

serverLoop : (c : proc) -> Protocol [c, s] () -> Protocol [c, s] ()
serverLoop c {s} proto = do
  Initiate c s (do proto; Rec (serverLoop c proto))

data Actions : Type where
  DoListen : proc -> Actions -> Actions
  DoSend : (to : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRecv : (from : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRec : Inf Actions -> Actions
  End : Actions

protoAs : (p : proc) -> Protocol xs a -> {auto prf : Elem p xs} -> Actions
protoAs pr proto = protoAsHelper pr proto (\_ => End) where
  protoAsHelper : (p : proc) -> Protocol xs a -> {auto prf : Elem p xs} -> (a -> Actions) -> Actions
  protoAsHelper proc (Initiate c s x) k with (prim__syntactic_eq _ _ proc s)
    protoAsHelper s (Initiate c s x) k | (Just Refl) = DoListen c (protoAsHelper s x k)
    protoAsHelper proc (Initiate c s x) k | Nothing with (prim__syntactic_eq _ _ proc c)
      protoAsHelper c (Initiate c s x) k | Nothing | (Just Refl) = k () --protoAsHelper c x k --here we have not the same thing as Brady does
      protoAsHelper proc (Initiate c s x) k | Nothing | Nothing = k () -- ?never_here2 --protoAsHelper proc x k
  protoAsHelper proc (Send from to a) k with (prim__syntactic_eq _ _ proc from)
    protoAsHelper from (Send from to a) k | (Just Refl) = DoSend to a k
    protoAsHelper proc (Send from to a) k | Nothing with (prim__syntactic_eq _ _ proc to)
      protoAsHelper to (Send from to a) k | Nothing | (Just Refl) = DoRecv from a k
      protoAsHelper proc (Send from to a) k | Nothing | Nothing = ?never_here_or_ -- ? we can be here if there are more then 2 parties of protocol and proc is neither client no server. Brady's version can deal with this
  protoAsHelper proc Done k = k ()
  protoAsHelper proc (Rec x) k = DoRec (protoAsHelper proc x k)
  protoAsHelper proc (Pure x) k = k x
  protoAsHelper proc (x >>= f) k = protoAsHelper proc x (\val => protoAsHelper proc (f val) k)
