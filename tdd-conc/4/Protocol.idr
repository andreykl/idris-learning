module Protocol

import Data.List

%default total

public export
data Protocol : List proc -> Type -> Type where
  Initiate : (c : proc) -> (s : proc) -> Protocol [c, s] () -> 
             {auto cprf : Elem c xs} ->
             {auto sprf : Elem s xs} ->
             Protocol xs ()
  Send : (src : proc) -> (dst : proc) -> (a : Type) ->
         {auto sprf : Elem src xs} ->
         {auto dprf : Elem dst xs} ->
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

public export
data Actions : Type where
  DoListen : (t : proc) -> Actions -> Actions
  DoSend : (to : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRecv : (from : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRec : Inf Actions -> Actions
  End : Actions

public export
protoAs : Protocol xs a -> (p : proc) -> {auto prf : Elem p xs} -> Actions
protoAs proto pr = protoAsHelper proto pr (\_ => End) where
  protoAsHelper : Protocol xs a -> (p : proc) -> {auto prf : Elem p xs} -> (a -> Actions) -> Actions
  protoAsHelper (Initiate c s y) proc k with (prim__syntactic_eq _ _ s proc)
    protoAsHelper (Initiate c proc y) proc k | (Just Refl) = DoListen c (protoAsHelper y proc k)
    protoAsHelper (Initiate c s y) proc k | Nothing with (prim__syntactic_eq _ _ c proc)
      protoAsHelper (Initiate proc s y) proc k | Nothing | (Just Refl) = protoAsHelper y proc k
      protoAsHelper (Initiate c s y) proc k | Nothing | Nothing = ?never_here2 -- k ()
  protoAsHelper (Send src dst a) proc k with (prim__syntactic_eq _ _ src proc)
    protoAsHelper (Send proc dst a) proc k | (Just Refl) = DoSend dst a k
    protoAsHelper (Send src dst a) proc k | Nothing with (prim__syntactic_eq _ _ dst proc)
      protoAsHelper (Send src proc a) proc k | Nothing | (Just Refl) = DoRecv src a k
      protoAsHelper (Send src dst a) proc k | Nothing | Nothing = ?never_here1 -- we should not be here?
  protoAsHelper Done proc k = k ()
  protoAsHelper (Rec x) proc k = DoRec (protoAsHelper x proc k)
  protoAsHelper (Pure x) proc k = k x
  protoAsHelper (x >>= f) proc k = protoAsHelper x proc (\val => protoAsHelper (f val) proc k)

public export
serverLoop : (c : proc) -> Protocol [c, s] () -> Protocol [c, s] ()
serverLoop c {s} proto = do
  Initiate c s (do proto; Rec (serverLoop c proto))
  
