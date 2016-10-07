module Main


import Debug.Trace
import Debug.Error

import CFFI.Memory
import CFFI.Types
import Data.Bits
import Data.Vect

import Array

%include C "bsparrow.h"
%include C "msparrow.h"
%lib C "msparrow"


memset : Ptr -> Int -> Bits8 -> Int -> IO ()
memset x y z x1 = foreign FFI_C "idris_memset" (Ptr -> Int -> Bits8 -> Int -> IO ()) x y z x1

bsparrow_new : Bits64 -> Bits64 -> Bits32 -> Bits32 -> Bits32 ->  String -> IO Ptr
bsparrow_new x y z x1 y1 z1 = foreign FFI_C "bsparrow_new" (Bits64 -> Bits64 -> Bits32 -> Bits32 -> Bits32 ->  String -> IO Ptr) x y z x1 y1 z1

bsparrow_destroy : Ptr -> IO ()
bsparrow_destroy x = foreign FFI_C "bsparrow_destroy" (Ptr -> IO ()) x

bsparrow_wait : Ptr -> Ptr -> Bits32 -> IO ()
bsparrow_wait x y z = foreign FFI_C "bsparrow_wait" (Ptr -> Ptr -> Bits32 -> IO ()) x y z

bsparrow_socket_assign_id : Ptr -> Bits64 -> IO ()
bsparrow_socket_assign_id x y = foreign FFI_C "bsparrow_socket_assign_id" (Ptr -> Bits64 -> IO ()) x y


now : IO Bits64
now = foreign FFI_C "now" (IO Bits64)

scalloc : Int -> Int -> IO Ptr
scalloc x y = foreign FFI_C "scalloc" (Int -> Int -> IO Ptr) x y



bsparrow_event_get_id : Ptr -> IO Bits64
bsparrow_event_get_id x = foreign FFI_C "bsparrow_event_get_id" (Ptr -> IO Bits64) x

bsparrow_event_set_id : Ptr -> Bits64 -> IO ()
bsparrow_event_set_id x y = foreign FFI_C "bsparrow_event_set_id" (Ptr -> Bits64 -> IO ()) x y

bsparrow_event_get_event : Ptr -> IO Bits32
bsparrow_event_get_event x = foreign FFI_C "bsparrow_event_get_event" (Ptr -> IO Bits32) x

bsparrow_event_set_event : Ptr -> Bits32 -> IO ()
bsparrow_event_set_event x y = foreign FFI_C "bsparrow_event_set_event" (Ptr -> Bits32 -> IO ()) x y

bsparrow_event_get_bsock : Ptr -> IO Ptr
bsparrow_event_get_bsock x = foreign FFI_C "bsparrow_event_get_bsock" (Ptr -> IO Ptr) x

bsparrow_event_set_bsock : Ptr -> Ptr -> IO ()
bsparrow_event_set_bsock x y = foreign FFI_C "bsparrow_event_set_bsock" (Ptr -> Ptr -> IO ()) x y

sparrow_msg_get_data : Ptr -> IO Ptr
sparrow_msg_get_data x = foreign FFI_C "sparrow_msg_get_data" (Ptr -> IO Ptr) x

sparrow_msg_get_length : Ptr -> IO Bits64
sparrow_msg_get_length x = foreign FFI_C "sparrow_msg_get_length" (Ptr -> IO Bits64) x

bsparrow_send : Ptr -> Ptr -> Ptr -> Int -> IO ()
bsparrow_send x y z j = foreign FFI_C "bsparrow_send_idris" (Ptr -> Ptr -> Ptr -> Int -> IO ()) x y z j

msparrow_recv : Ptr -> Ptr -> IO ()
msparrow_recv x y = foreign FFI_C "msparrow_recv" (Ptr -> Ptr -> IO ()) x y


msparrow_get_msg : Ptr -> Ptr -> Ptr -> IO Int
msparrow_get_msg x y z = foreign FFI_C "msparrow_get_msg" (Ptr -> Ptr -> Ptr -> IO Int) x y z

msparrow_print_msg : Ptr -> IO ()
msparrow_print_msg x = foreign FFI_C "msparrow_print_msg" (Ptr -> IO ()) x

bsparrow_set_timeout : Ptr -> Int -> IO ()
bsparrow_set_timeout x y = foreign FFI_C "bsparrow_set_timeout" (Ptr -> Int -> IO ()) x y

ack_msg : IO (Ptr, Nat)
ack_msg = do
  ar <- pure $ newAsciiArray 100 
  ar2 <- pure $ fillArray ar $ intVectToBits {n=8} (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 92 :: Nil)
  ar3 <- pure $ pushString 25 "Got 5000, need mooooreee!" ar2
  pure $ give_memory ar3


get_msg : Ptr -> Ptr -> Ptr -> Ptr -> IO () 
get_msg bsp bsock bspev msg = ( do
  msparrow_recv bsp bsock
  inner_while bsp bsock bspev msg ) where 
      inner_while : Ptr -> Ptr -> Ptr -> Ptr -> IO ()
      inner_while bsp bsock bspev msg = do
        bsparrow_set_timeout bsp 5000
        bsparrow_wait bsp bspev 0
        ev_ <- bsparrow_event_get_event bspev
        ev <- pure $ MkBits {n=32} ev_
        if ev == (intToBits {n=32} 32)
           then do 
             error "Timeout error. The client must have crushed."
           else pure ()
        if ev == (intToBits {n=32} 4)
           then do bsparrow_set_timeout bsp (-1)
                   r <- msparrow_get_msg bsp bspev msg
                   if r == 0 
                      then inner_while bsp bsock bspev msg
                      else  pure ()
           else pure ()


msg_receive_loop : Ptr -> Ptr -> Ptr -> Integer -> Integer -> IO Integer
msg_receive_loop bsp bspev bsock loop_length msg_size = (do
      msg <- scalloc 1 30 -- This is a big enough number
      outer_loop bsp bspev bsock loop_length msg_size msg 0 ) where
        inner_loop: Ptr -> Ptr -> Ptr -> Integer -> Ptr -> Integer -> IO ()
        inner_loop bsp bspev bsock msg_size msg i = do
          if i == 5000
             then do 
               (ptr,l) <- ack_msg
               pure $ trace ("ack msg length: " ++ show l) ()
               bsparrow_send bsp bsock ptr $ toIntNat l
             else pure ()
          get_msg bsp bsock bspev msg
         -- msparrow_print_msg msg
          mfree !(sparrow_msg_get_data msg)
          if i == (10000 - 1)
             then return ()
             else inner_loop bsp bspev bsock msg_size msg (i + 1)
        outer_loop : Ptr -> Ptr -> Ptr -> Integer -> Integer -> Ptr -> Integer -> IO Integer
        outer_loop bsp bspev bsock loop_length msg_size msg j = do
          inner_loop bsp bspev bsock msg_size msg 0
          if j == (loop_length - 1)
             then do 
               mfree msg
               return (j + 1)
             else outer_loop bsp bspev bsock loop_length msg_size msg (j + 1)
  
results : Integer -> Integer -> Integer -> IO ()
results j time msg_size = do
  ntime <- pure $ bitsToInt $ MkBits {n=64} !(Main.now)
  diff_time <- pure $ fromInteger {ty = Double} (ntime - time)
  rate <- pure $ (fromInteger {ty = Double} ((j*10000 + 1) * 1000)) / diff_time
  putStrLn ("Rate: " ++ show rate ++ " msgs per second.") 
  putStrLn ("Length: " ++ show msg_size )  
  putStrLn ("Msgs received: " ++ show (j * 10000) )  



main : IO()
main = do
  ((::) _ $ (::) msg_size_ $ (::) loop_length_  _) <- getArgs
  putStrLn ("Msg_size :" ++ msg_size_)
  putStrLn ("Loop length :" ++ loop_length_)
  loop_length <- pure $ cast {to=Integer} loop_length_
  msg_size <- pure $ cast {to=Integer} msg_size_
  bsp <- bsparrow_new 50000 4000 2 2 1 "9003"
  bspev <- scalloc 1 72
  bsparrow_wait bsp bspev 0
  event <- pure $ bitsToInt $ MkBits {n=32} !(bsparrow_event_get_event bspev)
  if event == 16 
     then do 
       bsock <- bsparrow_event_get_bsock bspev
       bsparrow_socket_assign_id bsock 1
       time <- pure $ bitsToInt $ MkBits {n=64} !(Main.now)
       actual_loop_length <- msg_receive_loop bsp bspev bsock loop_length msg_size

       -- Send last uncknowledge msg 
       ar <- pure $ newAsciiArray 100 
       ar2 <- pure $ fillArray ar $ intVectToBits {n=8} (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 92 :: Nil)
       ar3 <- pure $ pushString 21 "Got them all, thanks!" ar2
       (ptr, l) <- pure $ give_memory ar3
       bsparrow_send bsp bsock ptr $ toIntNat l
       results actual_loop_length time msg_size

       bsparrow_destroy bsp
       mfree bspev
       return ()
     else do
       return ()
  return ()




