{-# OPTIONS --exact-split #-}

module LinT where

open import Common
open import LinLogic
open import LinDepT
open import Size
open import Function
open import Data.Vec
open import Data.Sum
open import Level

-- Input
data LinTᵢ {u} : ∀{ll} → LinDepTᵢ {u} ll → Set (lsuc u) where
  ∅    : LinTᵢ ∅
  τ    :  ∀{n} → {dt : Vec (Set u) n} → {df : genT dt} → {hv : HVec dt}
          → applyH hv df → LinTᵢ $ τ {u} {n} {dt} {df} hv
  _∧_  : ∀{lll l rll r} → LinTᵢ {ll = lll} l → LinTᵢ {ll = rll} r → LinTᵢ (_∧_ l r)
  _←&    : ∀{lll l rll} → LinTᵢ {ll = lll} l → LinTᵢ (_←& {_} {_} {rll} l)
  &→_    : ∀{lll rll r} → LinTᵢ {ll = rll} r → LinTᵢ (&→_ {_} {lll} r)
  ∨    : ∀{lll l rll r} → LinTᵢ {ll = lll} l ⊎ LinTᵢ {ll = rll} r → LinTᵢ (_∨_ l r)


-- Output
data LinTₒ {i : Size} {u} : ∀{ll} → LinDepTₒ {i} {u} ll → Set (lsuc u) where
  ∅    : LinTₒ ∅
  τ    :  ∀{n} → {dt : Vec (Set u) n} → {df : genT dt} → {hv : HVec dt}
          → applyH hv df → LinTₒ $ τ {i} {u} {n} {dt} {df} hv
  _∧_  : ∀{lll l rll r} → LinTₒ {ll = lll} l → LinTₒ {ll = rll} r → LinTₒ (_∧_ l r)
  ∨    : ∀{lll l rll r} → LinTₒ {ll = lll} l ⊎ LinTₒ {ll = rll} r → LinTₒ (_∨_ l r)
  _←∂  : ∀{lll l rll} → LinTₒ {ll = lll} l → LinTₒ (∂ {l = lll} {r = rll} $ inj₁ l)
  ∂→_  : ∀{lll rll r} → LinTₒ {ll = rll} r → LinTₒ (∂ {l = lll} {r = rll} $ inj₂ r)
  -- IMPORTANT the & operator is only possible as a compile time operator. (in the output).
