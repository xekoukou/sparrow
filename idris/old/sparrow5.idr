module Main


import Syntax.PreorderReasoning
import Data.Fin
import Data.Vect
import Data.HVect
import Debug.Error

 %default total

elemSmallerThanBound : (n : Fin m) -> LTE (finToNat n) m
elemSmallerThanBound FZ = LTEZero
elemSmallerThanBound (FS x) = LTESucc (elemSmallerThanBound x)


--certain nat to fin
cnatToFin : (k: Nat) -> (n : Nat) -> {auto prf : LTE (S k) n} -> Fin n
cnatToFin Z Z {prf=prf} = void $ succNotLTEzero prf
cnatToFin Z (S k) = FZ
cnatToFin (S k) Z {prf=prf} = void $ succNotLTEzero prf
cnatToFin (S k) (S j) {prf=LTESucc prf} = FS $ cnatToFin k j

natToFinToNat : (k: Nat) -> (n : Nat) -> {auto prf : LTE (S k) n} -> (finToNat $ cnatToFin k n {prf = prf}) = k
natToFinToNat Z Z {prf=prf} = void $ succNotLTEzero prf
natToFinToNat Z (S k) {prf=prf} = Refl
natToFinToNat (S k) Z {prf=prf} = void $ succNotLTEzero prf
natToFinToNat (S k) (S j) {prf=LTESucc prf} = eqSucc (finToNat $ cnatToFin k j) k $ natToFinToNat k j {prf=prf}


plusminus : (m: Nat) -> (n : Nat) -> {auto prf : LTE n m} -> (m - n) + n = m 
plusminus Z Z = Refl
plusminus Z (S k) {prf = prf}= void $ succNotLTEzero prf
plusminus (S k) Z = rewrite ((S (plus k Z) = S k) <== plusZeroRightNeutral) in
                    Refl
plusminus (S k) (S j) {prf = LTESucc prf} = let prf2 =  eqSucc ((k - j) + j) k (plusminus k j {prf = prf}) in
                                            let prf3 = sym $ plusSuccRightSucc (k - j) j in
                                                trans prf3 prf2
                               

lemma2 : (r,c : Nat) -> (prf : LTE r c) -> minus (S c) r = S $ minus c r
lemma2 Z c prf = rewrite ((minus c Z = c) <== minusZeroRight) in
                 Refl
lemma2 (S k) Z prf = void $ succNotLTEzero prf
lemma2 (S k) (S j) (LTESucc prf) = lemma2 k j prf

symLemma2 : (r,c : Nat) -> (prf : LTE r c) -> S $ minus c r = minus (S c) r
symLemma2 r c prf = sym $ lemma2 r c prf


complement : (x : Fin (S k)) -> Fin (S k)
complement FZ {k = l} = cnatToFin l (S l) {prf = lteRefl {n = (S l)}}
complement (FS FZ) {k = Z} impossible
complement (FS (FS _)) {k = Z} impossible
complement (FS y) {k = (S k)} = weaken $ complement y

FCWeakenCommute : (x : Fin (S k)) -> FS (weaken x) = weaken (FS x)
FCWeakenCommute FZ = Refl
FCWeakenCommute (FS x) = Refl

FSComplWeakenCommute : (x : Fin (S k)) -> complement $ weaken x = FS (complement x)
FSComplWeakenCommute FZ = Refl
FSComplWeakenCommute (FS FZ) {k = Z} impossible
FSComplWeakenCommute (FS (FS _)) {k = Z} impossible
FSComplWeakenCommute (FS x) {k = (S k)} = rewrite ((complement $ weaken x = FS (complement x)) <== FSComplWeakenCommute ) in
                                          Refl

FSComplComplCommute : (x : Fin (S k)) -> complement $ complement (FS x) = FS (complement $ complement x)
FSComplComplCommute x = rewrite ((complement $ weaken $ complement x = FS (complement $ complement x)) <== FSComplWeakenCommute) in
                                Refl

complComplId : (x : Fin (S k)) -> complement $ complement x = x
complComplId FZ {k = Z} = Refl
complComplId FZ {k = (S Z)} = Refl
complComplId FZ {k = (S (S k))} = rewrite ((complement $ complement FZ = FZ {k = k}) <== complComplId) in
                                  Refl
complComplId (FS FZ) {k = Z} impossible
complComplId (FS (FS _)) {k = Z} impossible
complComplId (FS x) {k = (S k)} = rewrite ((complement $ complement $ FS x = FS $ complement $ complement x ) <== FSComplComplCommute ) ==> (FS (complement (complement x)) = FS x) in
                                  rewrite ((complement $ complement x = x ) <== complComplId) ==> (FS x = FS x) in
                                  Refl


finToNatWeakenNeutral : (x : Fin (S k)) -> finToNat $ weaken x = finToNat x
finToNatWeakenNeutral FZ = Refl
finToNatWeakenNeutral (FS FZ) {k = Z} impossible
finToNatWeakenNeutral (FS (FS _)) {k = Z} impossible
finToNatWeakenNeutral (FS x) {k = (S k)} = cong $ finToNatWeakenNeutral x

------------------------------------------------------------



data Node : String -> Type where
  MkNode : (s : String) -> Node s

genT : Vect n Type -> Type
genT [] = Type
genT (x :: xs) = x -> genT xs


belongs : ((s : String ** Node s), Nat) -> Vect n ((e : String ** Node e), Nat) -> Bool
belongs x [] = False
belongs ((s ** MkNode s), l) (((j ** MkNode j), m) :: xs) = case (s == j) of
                                                                 False => belongs ((s ** MkNode s), l) xs
                                                                 True => case (l == m) of
                                                                              True => True
                                                                              False => belongs ((s ** MkNode s), l) xs


data InSet : ((s : String ** Node s), Nat) -> Vect n ((s : String ** Node s), Nat) -> Type where
  Belongs : (k : ((s : String ** Node s), Nat)) -> (m : Vect n ((s : String ** Node s), Nat)) -> {prf : belongs k m = True} -> InSet k m

mutual
  data NGraph : Nat -> Type where
    NGNil : NGraph Z
    CNGEdge : (g : NGraph m) -> (no : Node so) -> (tc : Vect _ Type) -> (fc : genT tc) -> (tr : Vect _  (Fin m)) -> {e : Vect _ ((s : String ** Node s) , Nat)} -> (co :( (x: HVect (getAllDep g tr)) -> applyH g tr dT x -> List (r: ((s : String ** Node s), Nat) ** InSet r e) )) -> NGraph (S m)


-- Path dependence of dependent types.

-- We can check the the dependent variables are in the path of the communications we have taken by adding one new value after one correct communication and by omitting those that are in a circle. We can thus iteratively compute the allowed dependencies.

--When do we release a variable from the memory? We maintain a tree. In each if statement, we move to the next tree branch that contains the dependencies. We release the values that we do not need based on that tree.
--
--
-- ------> We release a variable when the function subgraph has finished its computation.
