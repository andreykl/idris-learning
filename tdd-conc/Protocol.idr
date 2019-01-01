module Protocol 

import Data.List
import Channels

%access public export

-- data SendOK : (ty : Type)      -> 
--               (from : proc)    -> 
--               (to : proc)      -> 
--               (xs : List proc) -> 
--               (b : Type)       -> Type where
--   SOK : SendOK ty from to xs b

data SendOK : (transmitted : Type) -> 
              (from : proc) -> 
              (to : proc) -> 
              (participants : List proc) -> 
              (continuation : Type) -> Type where
     SendLR : SendOK a x y [x, y] a
     SendRL : SendOK a x y [y, x] a
     SendGhost : Elem x xs -> Elem y xs -> SendOK a x y xs ()

data Protocol : List proc -> Type -> Type where
  Initiate : (c : proc) -> (s : proc) ->
             {auto prfc : Elem c xs} ->
             {auto prfs : Elem s xs} ->
             Protocol [c, s] () -> Protocol xs ()
  Send : (from : proc) -> (to : proc) -> (ty : Type) ->
         {auto prf : SendOK ty from to xs b} ->
         Protocol xs b

  Rec : Inf (Protocol xs a) -> Protocol xs a
  Pure : a -> Protocol xs a
  (>>=) : Protocol xs a -> (a -> Protocol xs b) -> Protocol xs b

syntax [from] "==>" [to] "|" [ty] = Send from to ty

data Literal : String -> Type where
  MkLit : (x : String) -> Literal x

mkProcess : (x : proc) -> Protocol xs ty -> 
            {auto prf : Elem x xs} ->
            (ty -> Actions) -> Actions

mkProcess x (Initiate client server p) k with (prim__syntactic_eq _ _ x server)
  mkProcess x (Initiate client server p) k | Nothing = k () 
  mkProcess x (Initiate client x p) k | (Just Refl) = DoListen client (mkProcess x p k)
mkProcess x (Send from to ty {prf=SendGhost y z}) k with (prim__syntactic_eq _ _ x from)
  mkProcess x (Send from to ty {prf=SendGhost y z}) k | Nothing with (prim__syntactic_eq _ _ x to)
    mkProcess x (Send from to ty {prf=SendGhost y z}) k | Nothing | Nothing = k () 
    mkProcess x (Send from to ty {prf=SendGhost y z}) k | Nothing | (Just w) = DoRecv from ty (\x => k ())
  mkProcess x (Send from to ty {prf=SendGhost y z}) k | (Just w) = DoSend to ty (\x => k ())
mkProcess {xs = [from,to]} x (Send from to ty {prf=SendLR}) k with (prim__syntactic_eq _ _ x from)
      | Nothing = DoRecv from ty k 
      | (Just y) = DoSend to ty k
mkProcess {xs = [to,from]} x (Send from to ty {prf=SendRL}) k with (prim__syntactic_eq _ _ x from)
      | Nothing = DoRecv from ty k 
      | (Just y) = DoSend to ty k
-- mkProcess x (With' xs sub prot) k with (isElemSyn x xs)
--       | Nothing = k () 
--       | (Just prf) = mkProcess x prot k
mkProcess x (y >>= f) k = mkProcess x y (\cmd => mkProcess x (f cmd) k)
mkProcess x (Rec p) k = DoRec (mkProcess x p k)
mkProcess x (Pure y) k = k y

protoAs : (x : proc) -> Protocol xs () -> {auto prf : Elem x xs} -> Actions
protoAs x p = mkProcess x p (\k => End)

echo : Protocol ['C, 'S] ()
echo = do msg <- 'C ==> 'S | String
          'S ==> 'C | Literal msg
          'S ==> 'C | Nat

serverLoop : (c : proc) -> Protocol [c, s] () ->
             Protocol [c, s] ()
serverLoop c {s} proto = Initiate c s (do proto; Rec (serverLoop c proto))

