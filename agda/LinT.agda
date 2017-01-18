{-# OPTIONS --exact-split #-}

module LinT where

open import LinDepT public
open import Size
open import Function
open import Data.Vec
open import Data.Sum
open import Level


mutual
  data LinT {i : Size} {u} : ∀{ll} → LinDepT {i} {u} ll → Set (suc u) where
    ∅    : LinT ∅
    τ    :  ∀{n} → {dt : Vec (Set u) n} → {df : genT dt} → {hv : HVec dt}
            → applyH hv df → LinT $ τ {i} {u} {n} {dt} {df} hv
    _∧_  : ∀{lll l rll r} → LinT {ll = lll} l → LinT {ll = rll} r → LinT (l ∧ r)
    ∨    : ∀{lll l rll r} → LinT {ll = lll} l ⊎ LinT {ll = rll} r → LinT (l ∨ r)
    _←∨  : ∀{lll l rll} → LinT {ll = lll} l → LinT {ll = _∨_ lll rll} (l ←∨)
    ∨→_  : ∀{lll rll r} → LinT {ll = rll} r → LinT {ll = _∨_ lll rll} (∨→ r)
    _←∂  : ∀{lll l rll} → LinT {ll = lll} l → LinT (∂ {l = lll} {r = rll} $ inj₁ l)
    ∂→_  : ∀{lll rll r} → LinT {ll = rll} r → LinT (∂ {l = lll} {r = rll} $ inj₂ r)

