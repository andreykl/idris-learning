module Protocol

import Data.List

%access public export

%default total

data Protocol : List proc -> Type -> Type where
  Initiate : (c, s : proc) -> Protocol [c, s] () ->
             {auto cprf : Elem c xs} ->
             {auto sprf : Elem s xs} ->
             Protocol xs ()
  Send : (from, to : proc) -> (a : Type) ->
         {auto fprf : Elem from xs} ->
         {auto tprf : Elem to xs} ->
         Protocol xs a
  Rec : Inf (Protocol xs a) -> Protocol xs a
  Done : Protocol xs ()
  
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
serverLoop c {s} proto = Initiate c s (do proto; Rec (serverLoop c proto))

data Actions : Type where
  DoListen : (t : proc) -> Actions -> Actions
  DoSend : (to : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRecv : (to : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRec : Inf Actions -> Actions
  End : Actions

protoAs : (process : proc) -> Protocol xs a -> {auto prf : Elem process xs} -> Actions
protoAs process proto = protoAsHelper process proto (\_ => End) where
  protoAsHelper : (p : proc) -> {auto prf : Elem p xs} ->
                  Protocol xs a -> (a -> Actions) -> Actions
  protoAsHelper x (Initiate c s y) k with (prim__syntactic_eq _ _ x s)
    protoAsHelper x (Initiate c s y) k | Nothing = k ()
    protoAsHelper s (Initiate c s y) k | (Just Refl) = DoListen c (protoAsHelper s y k)
  protoAsHelper x (Send from to a) k with (prim__syntactic_eq _ _ x from)
    protoAsHelper x (Send from to a) k | Nothing with (prim__syntactic_eq _ _ x to)
      protoAsHelper x (Send from to a) k | Nothing | Nothing = ?nothing_to_do
      protoAsHelper to (Send from to a) k | Nothing | (Just Refl) = DoRecv from a k
    protoAsHelper from (Send from to a) k | (Just Refl) = DoSend to a k
  protoAsHelper x (Rec y) k = DoRec (protoAsHelper x y k)
  protoAsHelper x Done k = k ()
  protoAsHelper x (Pure y) k = k y
  protoAsHelper x (y >>= f) k = protoAsHelper x y (\val => protoAsHelper x (f val) k)
