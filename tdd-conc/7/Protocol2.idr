module Protocol

import Data.List

%default total
%access public export

data Protocol : List proc -> Type -> Type where
  Initiate : (c, s : proc) -> Protocol [c, s] () ->
             {auto cprf : Elem c xs} ->
             {auto sprf : Elem s xs} ->
             Protocol xs ()

  Send : (from : proc) -> (to : proc) -> (a : Type) ->
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

serverLoop : (c : proc) -> Protocol [c, s] () ->
             Protocol [c, s] ()
serverLoop c {s} proto = Initiate c s (do proto; Rec (serverLoop c proto))

data Actions : Type where
  DoListen : (c : proc) -> Actions -> Actions
  DoSend : (to : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRecv : (from : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRec : Inf Actions -> Actions
  End : Actions

protoAs : (p : proc) -> Protocol xs a -> {auto prf : Elem p xs} -> Actions
protoAs p proto = protoAsHelper p proto (\_ => End) where
  protoAsHelper : (p : proc) -> Protocol xs a -> {auto prf : Elem p xs} -> (a -> Actions) -> Actions
  protoAsHelper p (Initiate c s x) k with (prim__syntactic_eq _ _ p s)
    protoAsHelper p (Initiate c s x) k | Nothing = k () -- protoAsHelper p x k
    protoAsHelper s (Initiate c s x) k | (Just Refl) = DoListen c (protoAsHelper s x k)
  protoAsHelper p (Send from to a) k with (prim__syntactic_eq _ _ p from)
    protoAsHelper p (Send from to a) k | Nothing with (prim__syntactic_eq _ _ p to)
      protoAsHelper p (Send from to a) k | Nothing | Nothing = ?nothing_to_do -- Brady's version can handle this
      protoAsHelper to (Send from to a) k | Nothing | (Just Refl) = DoRecv from a k
    protoAsHelper from (Send from to a) k | (Just Refl) = DoSend to a k
  protoAsHelper p Done k = k ()
  protoAsHelper p (Rec x) k = DoRec (protoAsHelper p x k)
  protoAsHelper p (Pure x) k = k x
  protoAsHelper p (x >>= f) k = protoAsHelper p x (\val => protoAsHelper p (f val) k)
