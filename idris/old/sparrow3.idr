module Main

import Data.Fin
import Data.Vect
import Data.HVect

 %default total


hasT : t -> Type
hasT x = t


belongs : Nat -> Vect n Nat -> Bool
belongs k [] = False
belongs k (x :: xs) = case (k == x) of
                           True => True
                           False => belongs k xs


data InSet : Nat -> Vect n Nat -> Type where
  Belongs : (k : Nat) -> (m : Vect n Nat) -> {prf : belongs k m = True} -> InSet k m
  

data Node : String -> Type where
  MkNode : (a : String) -> Node a

mutual 
  data NGraph : Nat -> Type where
    NGNil : NGraph Z
    CNGEdge : (g : NGraph m) -> {tr : Vect tn (Fin m)} -> {p : genT (getAllTypes g tr)} -> Node o -> {o : Vect on Nat} -> 
                                {c : (dT -> List ((e : String ** Node e), r: Nat ** InSet r o) ) } -> Vect r ((e : String ** Node e) , Nat) -> NGraph (S m)

--  getType : NGraph m -> Fin m -> Type
--  getType (CNGEdge g x z w) FZ = hasT w
--  getType (CNGEdge g x z w) (FS y) = getType g y
--
--  getValue : (r : NGraph m) -> (i : Fin m) -> getType r i
--  getValue (CNGEdge g x z w) FZ = w
--  getValue (CNGEdge g x z w) (FS y) = getValue g y
--
--  getAllTypes : NGraph m -> Vect tn (Fin m) -> Vect tn Type
--  getAllTypes x [] = []
--  getAllTypes x (y :: xs) = getType x y :: getAllTypes x xs
--  
--  getAllValues : (l : NGraph m) -> (m : Vect tn (Fin m)) -> HVect (getAllTypes l m)
--  getAllValues x [] = []
--  getAllValues x (y :: xs) = getValue x y :: getAllValues x xs

  genT : Vect tn Type -> Type
  genT [] = Type
  genT (x :: xs) = x -> genT xs
  
  applyH : {v : Vect k Type} -> genT v -> HVect v -> Type
  applyH f [] = f
  applyH f (x :: y) = applyH (f x) y
 


