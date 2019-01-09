module Channels

import Data.List

%language UniquenessTypes

infixl 5 @@

data Res : (a : Type*) -> (a -> Type*) -> Type* where
  (@@) : (val : a) -> k val -> Res a k

data Actions : Type where
  DoListen : (client : proc) -> Actions -> Actions
  DoSend : (dest : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRecv : (dest : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRec : Inf (Actions) -> Actions
  End : Actions
 
data Channel : (src : proc) -> (dest : proc) -> Actions -> UniqueType where

data RChannel : (dest : proc) -> Actions -> Type where

data Cmd : proc -> List proc -> List proc -> Type* -> Type* where
  CConnect : RChannel srv p -> Cmd me xs (srv :: xs) (Channel me srv p)
  CClose : Channel me srv End -> {auto prf : Elem srv xs} ->
          Cmd me xs (dropElem xs prf) ()
  CListen : Channel me c (DoListen c k) ->
           Cmd me xs xs (Res Bool (\ok => 
                                       if ok then Channel me c k
                                             else Channel me c (DoListen c k)))
  CSend : (msg : ty) -> Channel me t (DoSend t ty k) -> Cmd me xs xs (Channel me t (k msg))
  CRecv : Channel me t (DoRecv t ty k) -> Cmd me xs xs (Res ty (\v => Channel me t (k v)))
  
  CPrint : String -> Cmd me xs xs ()
  CGetLine : Cmd me xs xs String

data SendOK : Type -> proc -> proc -> List proc -> Type -> Type 

data Protocol : List proc -> Type -> Type where
  Init : (c : proc) -> (s : proc) -> 
         Protocol [c, s] () -> 
         {auto prfc : Elem c xs} ->
         {auto prfs : Elem s xs} ->
         Protocol xs ()
  Send : {- {auto prf : SendOK ty from to xs b} -> -}
         (from : proc) -> (to : proc) -> (ty : Type) -> Protocol xs ty
  Done : Protocol xs ()

  Rec  : Inf (Protocol xs a) -> Protocol xs a
  Pure : a -> Protocol xs a
  (>>=) : Protocol xs a -> (a -> Protocol xs b) -> Protocol xs b

syntax [from] "==>" [to] "|" [ty] = Send from to ty
syntax "_|_" = Done

data Literal : String -> Type where
  MkLit : (msg : String) -> Literal msg

echo : Protocol ['C, 'S] ()
echo = do
  msg <- 'C ==> 'S | String
  'S ==> 'C | Literal msg
  'S ==> 'C | Nat
  _|_
  
serverLoop : (c : proc) -> Protocol [c, s] () -> Protocol [c, s] ()
serverLoop c {s} proto = Init c s (do proto; Rec (serverLoop c proto))

mkProcess : (p : proc) -> (proto : Protocol ps a) -> 
            {auto prf : Elem p ps} -> (a -> Actions) -> Actions
mkProcess p (Init c s proto) k with (prim__syntactic_eq _ _ p s)
  mkProcess p (Init c s proto) k | Nothing = k () -- connect??
  mkProcess s (Init c s proto) k | (Just Refl) = DoListen c (mkProcess s proto k)

mkProcess p (Send from to a) k with (prim__syntactic_eq _ _ p from)
  -- mkProcess p (Send from to a) k | Nothing with (prim__syntactic_eq _ _ p to)
  --   mkProcess p (Send from to a) k | Nothing | Nothing = k ()
  --   mkProcess p (Send from to a) k | Nothing | (Just _) = DoRecv from a k
  mkProcess p (Send from to a) k | Nothing  = DoRecv from a k  
  mkProcess p (Send from to a) k | (Just _) = DoSend to a k


mkProcess p Done k = End

mkProcess p (Rec x) k = DoRec (mkProcess p x k)
mkProcess p (Pure x) k = k x
mkProcess p (x >>= f) k = mkProcess p x (\cmd => mkProcess p (f cmd) k)

protoAs : (p : proc) -> Protocol xs a -> {auto prf : Elem p xs} -> Actions
protoAs proc proto = mkProcess proc proto (\_ => End)
