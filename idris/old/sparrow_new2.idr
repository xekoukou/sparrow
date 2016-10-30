module Main

import Data.HVect
import Data.Vect

%default total

mutual
  data SFun : Vect k Type -> Type where
    MkSFun : {v1 : Vect k1 Type} -> {v2 : Vect k2 Type} -> {v3 : Vect k3 Type} -> {nv2 : Vect l1 ( y: Nat ** x : Vect y Type ** SFun x ) } -> (HVect v1 -> HVect v2 -> HVect v3 -> (HVect v3 , HVect (map Main.map_lamb nv2 ))) -> SFun v2

  data LSFun : SFun a -> Type where
    MkLSFun : (x : SFun a) -> LSFun x

  map_lamb : (j: Nat ** o : Vect j Type ** SFun o) -> Type
  map_lamb (l ** x ** y) = ( (Nat, HVect x) , LSFun y )

fon : HVect [Int, String] -> HVect [Nat] -> HVect [Nat] -> (HVect [Nat], HVect [])
fon x y z = ?fun_rhs

fun1 : HVect [Int, String] -> HVect [Nat] -> HVect [Nat] -> (HVect [Nat], HVect [((Nat, HVect [Nat] ) , LSFun (MkSFun Main.fon {nv2 = []}) )] )
fun1 x y z = ( z , [((Z, y ), MkLSFun (MkSFun Main.fon) ) ] )

fun2 : HVect [Int, String] -> HVect [Nat] -> HVect [Nat] -> (HVect [Nat], HVect [((Nat, HVect [Nat] ) , LSFun (MkSFun Main.fun1 {nv2 = [ (1 ** [Nat] ** (MkSFun Main.fon {nv2 = []}) ) ]}) )] )
fun2 x y z = ?dd




decompose : (a -> b -> c -> (c,d)) -> List Type
decompose f {a=a} {b=b} {c=c} {d=d} = [d]

