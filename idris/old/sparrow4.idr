module Main

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


-- TODO Add local depependent variables which determine the type of the data. (Those local dependencies need to be transmitted with the data or not (Probably they are not needed , if you send two messages, the first sending the dependent variables).

mutual 
  data NGraph : Nat -> Type where
    NGNil : NGraph Z
    CNGEdge : (g : NGraph m) -> (tr : Vect tn  (Fin m)) -> 
              (dT : genFT g tr) -> (no : Node so) -> {e : Vect _ ((s : String ** Node s) , Nat)} -> (c :( (x: HVect (getAllDep g tr)) -> applyH g tr dT x -> List (r: ((s : String ** Node s), Nat) ** InSet r e) )) -> NGraph (S m)

  getAllDep : (g : NGraph m) -> (tr : Vect tn  (Fin m)) -> Vect tn Type
  getAllDep g tr = map (getDep g) tr 

  genFT : (g : NGraph m) -> (tr : Vect tn  (Fin m)) -> Type
  genFT g tr = genT $ getAllDep g tr

  getDep : NGraph m -> Fin m -> Type
  getDep (CNGEdge g tr dT no c) FZ = (x : HVect (getAllDep g tr) ** (applyH g tr dT x) )
  getDep (CNGEdge g tr dT no c) (FS x) = getDep g x

  applyH : (g : NGraph m) -> (tr : Vect tn  (Fin m)) -> genFT g tr -> HVect $ getAllDep g tr -> Type
  applyH g [] f [] = f
  applyH g (t :: ts) f (y :: ys) = applyH g ts (f y) ys

traverseToIndex : (n : Fin (S k)) -> NGraph (S k) -> NGraph (finToNat n)
traverseToIndex n g {k = k} = replace {P = (\x => NGraph $ finToNat x)} ((complement $ complement n = n) <== complComplId ) $ 
                              traverseCompl (complement n) g                                                                      where
  traverseCompl : (c : Fin (S l)) -> NGraph (S l) -> NGraph (finToNat $ complement c)
  traverseCompl FZ (CNGEdge x tr dT no c) {l = Z} = x
  traverseCompl FZ (CNGEdge x tr dT no c) {l = (S k)} = replace {P = (\x => NGraph (S x)) }  (sym $ natToFinToNat k (S k) {prf = lteRefl {n = (S k)}}) x
  traverseCompl (FS FZ) _ {l = Z} impossible
  traverseCompl (FS (FS _)) _ {l = Z} impossible
  traverseCompl (FS y) (CNGEdge x tr dT no c) {l = (S k)} = replace {P = (\x => NGraph x)} (sym $ finToNatWeakenNeutral $ complement y) $ traverseCompl y x



--All Nats must direct to existing CNGEdges.
nextEdgesExist : Nat -> NGraph m -> Bool
nextEdgesExist k NGNil = True
nextEdgesExist k (CNGEdge g tr dT no c {e=e}) = foldr (\x, r => r && (x < k) && (x > 0)) True (map snd e)


-- The next edge must either have as origin the end node of the prev edge or the same endpoints.
correctEndPoints : NGraph lm -> NGraph m -> Bool
correctEndPoints NGNil y = True
correctEndPoints _ _ {m = Z} = True
correctEndPoints (CNGEdge g tr dT no c {e=e}) y {m= (S k)} = (foldr (\ ((s ** ne) , x ) , r => case (isLTE (S x) (S k)) of 
                                                                          Yes prf => r && (checkOne no ne ( traverseToIndex (cnatToFin x (S k)) y ) )
                                                                          No _    => False                                              ) True e) && (correctEndPoints g y) where
  checkOne : (no : Node so) -> (ne : Node se) ->  NGraph _ -> Bool
  checkOne no ne NGNil = True
  checkOne no {so=so} ne {se=se} (CNGEdge y xs z nno {so=nso} f {e=e} ) = case (se == nso) of
                                                                        True => True
                                                                        False => case (so == nso) of
                                                                                      False => False
                                                                                      True => foldr (\(nse ** _) ,r => r && (nse == se) ) True (map fst e)




-- Dependent types should only dependent on data that are received by the node. TODO Also they should depend only on previous data, not future. When there are circles, future data can not depend on the data of the circle except on the part that it is certain to have
-- been traversed.
correctDependence : NGraph m -> Bool
correctDependence NGNil = True
correctDependence (CNGEdge g tr dT no {so=so} c) = (foldr(\x, r => r && (checkOne g x) ) True tr) && (correctDependence g) where
  checkOne : NGraph m -> Fin m -> Bool
  checkOne _ FZ {m=Z} impossible
  checkOne _ (FS _) {m=Z} impossible
  checkOne g x {m=(S k)} with (traverseToIndex x g)
    checkOne g FZ {m=(S k)} | NGNil = error "Report Bug : Because of correctEndPoints, all xs' of tr cannot be FZ."        --TODO This should never happen. We need to prove it.
    checkOne g (FS x) {m=(S k)} | (CNGEdge _ _ _ _ _ {e=e}) = foldr (\(nse ** _) ,r => r && (nse == so) ) True (map fst e)
    
                     


data ValidNGraph : NGraph m -> Type where
  MkValidNGraph : (g : NGraph m) -> {auto prf1 : (nextEdgesExist m g = True)} -> {auto prf2 : (correctEndPoints g g = True) } -> ValidNGraph g


generateLocalGraph : NGraph m -> (r : Nat ** NGraph r)
generateLocalGraph NGNil = (Z ** NGNil)
generateLocalGraph (CNGEdge g tr dT no c) = ?generateLocalGraph_rhs_2




