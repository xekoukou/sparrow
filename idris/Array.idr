module Array

import CFFI.Memory
import CFFI.Types

import Data.Vect
import Data.Bits
import Debug.Error
import Debug.Trace

%include C "Array.h"
%link C "Array.o"


%default total

new_CData : Int -> Int -> IO CData
new_CData x y = foreign FFI_C "array_alloc" (Int -> Int -> IO CData) x y

realloc_CData : Int -> CData -> IO ()
realloc_CData x y = foreign FFI_C "array_realloc" (Int -> CData -> IO ()) x y

claim_memory : Ptr -> Int -> IO CData
claim_memory x y = foreign FFI_C "array_manage" (Ptr -> Int -> IO CData) x y

return_memory : CData -> IO Ptr
return_memory x = foreign FFI_C "return_memory" (CData -> IO Ptr) x

return_size : CData -> IO Int
return_size x = foreign FFI_C "return_size" (CData -> IO Int) x


-- TODO Remove ArrayT, this is to mean the granularity with which we look into memory. (so replace it with Nat). and have data types be implemented on top of Array like AsciiArray.

||| The data type that is contained in the Array.
|||
||| 
public export
data ArrayT : Type where
  ABits8  : ArrayT
  ABits16 : ArrayT
  ABits32 : ArrayT
  ABits64 : ArrayT

public export
mapT : ArrayT -> Type
mapT ABits8 = Bits8
mapT ABits16 = Bits16
mapT ABits32 = Bits32
mapT ABits64 = Bits64

export
sizeof : ArrayT -> Int
sizeof ABits8 = 8
sizeof ABits16 = 16
sizeof ABits32 = 32
sizeof ABits64 = 64



export
data Array : Nat -> ArrayT ->  Type where
  NewArray : (n: Nat) -> (t:ArrayT) -> CData -> (s: Nat) -> (os: Nat) -> {auto p: LTE n $ mult os s} -> {auto p2: (os = S w) } -> Array n t -- n indicates the amount of data that are insize the Array, The other Int indicates its memory size

export
newArray : (t:ArrayT) -> (s: Nat) -> {auto p: (s = S w)} -> Array 0 t
newArray t s {p=p}= unsafePerformIO (do
                               cdata <- new_CData (toIntNat s) $ sizeof t
                               return $ NewArray Z t cdata 1 s {p2=p}
                               )

-- Unsafe, to be used only when s >= n
array_poke : %static {t: ArrayT} -> Nat -> CData -> mapT t -> IO ()
array_poke {t=ABits8} k x d = foreign FFI_C "array_poke8" (Int -> Bits8 -> CData -> IO ()) (toIntNat k) d x
array_poke {t=ABits16} k x d = foreign FFI_C "array_poke16" (Int -> Bits16 -> CData -> IO ()) (toIntNat k) d x
array_poke {t=ABits32} k x d = foreign FFI_C "array_poke32" (Int -> Bits32 -> CData -> IO ()) (toIntNat k) d x
array_poke {t=ABits64} k x d = foreign FFI_C "array_poke64" (Int -> Bits64 -> CData -> IO ()) (toIntNat k) d x

array_peek : %static {t: ArrayT} -> Nat -> CData -> IO (mapT t)
array_peek {t=ABits8} k x = foreign FFI_C "array_peek8" (Int -> CData -> IO Bits8) (toIntNat k) x
array_peek {t=ABits16} k x = foreign FFI_C "array_peek16" (Int -> CData -> IO Bits16) (toIntNat k) x
array_peek {t=ABits32} k x = foreign FFI_C "array_peek32" (Int -> CData -> IO Bits32) (toIntNat k) x
array_peek {t=ABits64} k x = foreign FFI_C "array_peek64" (Int -> CData -> IO Bits64) (toIntNat k) x

lteAddLeft : (n : Nat) -> LTE n (plus m n)
lteAddLeft Z = LTEZero
lteAddLeft {m=m} (S k) = replace (plusSuccRightSucc m k) $ LTESucc (lteAddLeft k)

lemma : (s : Nat) -> (os : Nat) -> (p : (os = S w)) -> (p1 : LTE k (mult os s)) -> LTE (S k) (mult os (S s))
lemma s Z p p1 = absurd p
lemma s (S m) p p1 =  lteTransitive (LTESucc p1) inlemma1 where
  inlemma2 : (r:Nat) -> LTE (S (mult (S r) s)) (plus (S r) $ mult (S r) s)
  inlemma2 r = LTESucc $ lteAddLeft $ plus s $ mult r s

  inlemma1 : LTE (S (mult (S m) s)) (mult (S m) (S s))
  inlemma1 = replace (sym $ multRightSuccPlus (S m) s) $ inlemma2 m

export
push : mapT t -> Array k t -> Array (S k) t
push y (NewArray k t x s os {p=p} {p2=p2}) = case (isLTE (S k) $ mult os s) of
                                 Yes pr => unsafePerformIO (do
                                                          array_poke {t=t} k x y
                                                          return $ NewArray (S k) t x s os {p2=p2}
                                                          )
                                 No pr => unsafePerformIO (do
                                                         realloc_CData (toIntNat $ mult (S s) os) x
                                                         array_poke {t=t} k x y
                                                         return $ NewArray (S k) t x (S s) os {p=lemma s os p2 p} {p2=p2}
                                                         )
export
value_at : Array n t -> (k: Nat) -> {auto nz: n = (S m)} -> {p:LTE k m} -> mapT t
value_at (NewArray n t x s os) k = unsafePerformIO (do
        array_peek {t=t} k x
        )


mult1 : (s: Nat) -> LTE s (mult s (S Z))
mult1 Z = LTEZero
mult1 (S k) = LTESucc $ mult1 k

export
enclose_memory : (t:ArrayT) -> Ptr -> (s: Nat) -> {auto p: (s = S w)} -> Array s t
enclose_memory t ptr s {p=p}= unsafePerformIO (do
                               cdata <- claim_memory ptr (toIntNat s)
                               return $ NewArray s t cdata 1 s {p=(mult1 s)} {p2=p}
                               )



export
give_memory : Array s t -> (Ptr, Nat)
give_memory (NewArray s t x k os) = unsafePerformIO (do
            m <- return_memory x
            return (m, k * os)
            )

export
fillArray : Array n t -> Vect m (mapT t) -> Array (n+m) t
fillArray x [] {t=t} {n=n} = replace {P=\x => Array x t} (sym $ plusZeroRightNeutral n) x
fillArray x (y :: ys) {t=t} {n=n} {m=S k} = replace {P=\x => Array x t} (plusSuccRightSucc n k) (fillArray (push y x) ys)


intVectToBits : {n: Nat} -> Vect k Integer -> Vect k (machineTy $ nextBytes n)
intVectToBits [] = []
intVectToBits (x :: xs) {n=n} = case (intToBits {n=n} x) of
                                MkBits b => b :: intVectToBits xs



stringToVect : (s: String) -> Vect (length $ unpack s) Bits8
stringToVect s = replace {P = (\x => Vect x Bits8)} (mapPreservesLength turnToBits8 (unpack s)) $
                                    fromList $ map turnToBits8 (unpack s)                          where
  turnToBits8 : Char -> Bits8
  turnToBits8 x = case (intToBits {n=8} $ cast $ ord x) of
                       MkBits b => b


public export
data AsciiArray : Nat -> Type where
  NewAsciiArray : Array n ABits8 -> AsciiArray n

export
newAsciiArray : (s:Nat) -> {auto p: (s = S w)} -> AsciiArray 0
newAsciiArray n = NewAsciiArray $ newArray ABits8 n

export
pushString : (s :String) -> AsciiArray k -> AsciiArray (k + (length $ unpack s))
pushString s (NewAsciiArray ar) {k=k} = NewAsciiArray $ fillArray ar $ stringToVect s 

export
stringToArray : (s :String) -> AsciiArray (length $ unpack s)
stringToArray s = let ar = newAsciiArray (S $ length $ unpack s)  in
                      replace {P = (\x => AsciiArray x)}  (plusZeroLeftNeutral (length $ unpack s)) $
                                   pushString s ar

