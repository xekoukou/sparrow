{-# OPTIONS --exact-split #-}

module Common where


open import Data.Empty public
open import Relation.Binary.PropositionalEquality public using (_≡_ ; refl)
open import Relation.Binary.HeterogeneousEquality public using (_≅_ ; refl ; ≅-to-≡)
open import Relation.Nullary public
open import Size public
open import Function public
open import Level public renaming (suc to lsuc ; _⊔_ to _l⊔_ ; zero to lzero) 
open import Data.Nat public
open import Data.Vec
open import Data.Product public


-- postulates

postulate IMPOSSIBLE : ∀{u} → {A : Set (u)} → A


J : {u u' : Level} {A : Set u} {x : A} (P : (y : A) → x ≡ y → Set u') →
     P x refl → (y : A) (x≡y : x ≡ y) → P y x≡y
J P p ._ refl = p


it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x


module _ where


-- A vector that contains elements of possibly different types.
  
  infixr 5 _∷_
  
  data HVec {u} : ∀{n} -> Vec (Set u) n -> Set (lsuc u) where
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
  

infixr 0 _asInst_

_asInst_ : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → ({{y : A}} → B y) → B x
x asInst f = f {{x}}


eqEq : ∀{u} → {A : Set u} → {x y : A} → (eqa : x ≡ y) → (eqb : x ≡ y) → eqa ≡ eqb
eqEq refl refl = refl
