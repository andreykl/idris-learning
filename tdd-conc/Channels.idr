module Channels

import Data.List

%language UniquenessTypes

%access public export

infixl 5 @@

data Res : (a : Type*) -> (a -> Type*) -> Type* where
  (@@) : {k : a -> Type*} -> (val : a) -> k val -> Res a k

data Actions : Type where
  DoListen : (client : proc) -> Actions -> Actions
  DoSend : (dest : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRecv : (dest : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRec : Inf Actions -> Actions
  End : Actions

data Channel : (src : proc) -> (dest : proc) -> Actions -> UniqueType

data RChannel : (dest : proc) -> Actions -> Type

data Cmd : proc -> List proc -> List proc -> Type* -> Type* where
  Connect : RChannel srv p -> Cmd me xs (srv :: xs) (Channel me srv p)
  Close : Channel me srv End -> 
          {auto prf : Elem srv xs} ->
          Cmd me xs (dropElem xs prf) ()
  Listen : Channel me t (DoListen t k) ->
           {auto prf : Elem t xs} ->
           Cmd me xs xs (Res Bool (\ok =>
             if ok then Channel me t k
                   else Channel me t (DoListen t k)))
  Send : (val : a) ->
         Channel me t (DoSend t a k) ->
         Cmd me xs xs (Channel me t (k val))
  Recv : Channel me t (DoRecv t a k) ->
         Cmd me xs xs (Res a (\v => Channel me t (k v)))

