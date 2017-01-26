{-# OPTIONS --exact-split #-}

module Common where


open import Data.Empty public hiding (⊥-elim)
open import Relation.Binary.PropositionalEquality public using (_≡_ ; refl)
open import Relation.Nullary public
open import Size public
open import Function public
open import Level public renaming (suc to lsuc ; _⊔_ to _l⊔_ ; zero to lzero) 
open import Data.Nat public
open import Data.Vec


-- A proof irrelevant eliminator

module _ where

  ⊥-elim : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
  ⊥-elim ()


module _ where


-- A vector that contains elements of possibly different types.
  
  infixr 5 _∷_
  
  data HVec {u} : ∀{n} -> Vec (Set u) n -> Set u where
    []  : HVec []
    _∷_ : ∀{n} {A : Set u} {vt : Vec (Set u) n} (x : A) (xs : HVec vt) -> HVec (A ∷ vt)
  

-- Used in LinLogic.

  genT : ∀{u} {n : ℕ} -> Vec (Set u) n -> Set (lsuc u)
  genT {u} [] = Set u
  genT (x ∷ xs) =  x -> genT xs


-- A function that applies HVec to a genT function.

  applyH : ∀{u n} -> {vt : Vec (Set u) n} -> HVec vt -> genT vt -> Set u
  applyH [] y = y
  applyH (x ∷ xs) y = applyH xs (y x)
  