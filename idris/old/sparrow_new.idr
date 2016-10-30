module Main

import Data.Vect
import Data.HVect
import Data.Fin

%default total

-- TODO Make a local copy of HVect and Vect
--
--genT : Vect l Type -> Type -> Type
--genT [] a = a
--genT (x :: xs) a = x -> genT xs a
--
--callF : {a : Type } -> genT v a -> HVect v -> a
--callF f [] = f
--callF f (x :: z) = callF (f x) z
--
--dcallF : {h: HVect v} -> {f: (genT v Type)} -> {g : (genT v Type)} -> (callF f h -> callF g h ) -> callF f h -> callF g h
--dcallF d x = d x
--
--
--map : {hh : Vect m (HVect v)} -> {f: (genT v Type)} -> {g : (genT v Type)} -> (callF f r -> callF g r) -> HVect (map (\x => callF f x) hh ) -> HVect (map (\x => callF g x) hh )
--map d [] {hh = []} = []
--map d (y :: ys) {hh = h :: hs} = dcallF d y :: map d ys
--


--foo : List a -> List a
--foo [] = []
--foo (x :: xs) = x :: foo xs
--
--list1 : List String
--list1 = ["hello"]
--
--list2 : List Nat
--list2 = [3]
--
--result : List Nat
--result = dcallF {h = [Nat]} foo list2
--
--result2 : HVect [List String, List Nat]
--result2 = map foo {hh = [[String] , [Nat]]} {f = List} {g = List} [list1, list2]
--



--mutual
-- 
--  data SFun : Vect _ Type -> Vect _ Type -> Type where
--    MkSFun : (vl : Vect _ Type) -> (vk : Vect _ Type) -> {a : Vect _ (_ , _)} -> HVect (map (\(x,y) => SFun x y) a ) -> (HVect vl -> HVect vk -> Lin s) -> SFun vl vk
--
--  data Lin : SFun _ _ -> Type where
--    MkLin : (m : SFun vl vk) -> HVect vl -> HVect vk -> Lin m





