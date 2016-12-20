{-# OPTIONS --exact-split #-}

module LinFun where

open import LinT public
open import Size
open import Level
open import Function
open import Data.Bool
open import Relation.Binary.PropositionalEquality

module _ where

  open SetLLMp
  
  mutual
    data LFun {i : Size} {u} : {rll : LinLogic i {u}} → {ll : LinLogic i {u}} → Set (suc u) where
     I   : ∀{rll} → LFun {rll = rll} {ll = rll}
     _⊂_ : ∀{pll ll ell rll} → {ind : IndexLL pll ll} → (elf : LFun {i} {u} {ell} {pll})
           → {{prf : usesInput elf ≡ true}} → LFun {i} {u} {rll} {(replLL ll ind ell)}
           → LFun {i} {u} {rll} {ll}
     --DO we need to set ltr as an instance varriable?
     tr  : ∀{ll orll rll} → {{ltr : LLTr orll ll}} → LFun {i} {u} {rll} {orll} → LFun {i} {u} {rll} {ll}
     com : ∀{ll frll rll} → {prfi : onlyNilOrNoNilFinite ll ≡ true}
           → {prfo : onlyNilOrNoNilFinite frll ≡ true}
           → (df : (ldt : LinDepT ll) → LinT ldt → LinDepT frll) → LFun {i} {u} {rll} {frll}
           → LFun {rll = rll} {ll = ll}
     call : ∀{∞ll ∞rll} → ∞LFun {i} {u} {∞rll} {∞ll} → LFun {i = i} {rll = call ∞rll} {ll = call ∞ll}
  
  
    record ∞LFun {i u} {∞rll ∞ll : ∞LinLogic i {u}} : Set (suc u) where
      coinductive
      field
        step : {j : Size< i} → LFun {j} {u} {step ∞rll} {step ∞ll}
  
    -- Maybe this should be changed to have as output an MSet.
    usesInput : ∀{i u rll ll} → LFun {i} {u} {rll} {ll} → Bool
    usesInput x = usesInput` x ∅ where
      usesInput` : ∀{i u rll ll} → LFun {i} {u} {rll} {ll} → MSetLL ll → Bool
      usesInput` I s = false
      usesInput` (_⊂_ {ell = ell} {ind = ind} elf lf) ∅ = usesInput` lf (¬∅ (∅-add ind ell))
      usesInput` (_⊂_ {ell = ell} {ind = ↓} elf lf) (¬∅ s) with (contruct $ add s ↓ ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {↓} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {_} {_} {.(_ LinLogic.∧ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∧ = {!!}
      usesInput` (_⊂_ {_} {_} {.(_ LinLogic.∧ _)} {_} {↓} elf lf) (¬∅ s) | ∧→ ns = {!!}
      usesInput` (_⊂_ {_} {_} {.(_ LinLogic.∧ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∧→ ns₁ = {!!}
      usesInput` (_⊂_ {_} {_} {.(_ LinLogic.∨ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∨ = {!!}
      usesInput` (_⊂_ {_} {_} {.(_ LinLogic.∨ _)} {_} {↓} elf lf) (¬∅ s) | ∨→ ns = {!!}
      usesInput` (_⊂_ {_} {_} {.(_ LinLogic.∨ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∨→ ns₁ = {!!}
      usesInput` (_⊂_ {_} {_} {.(_∂_ _ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∂ = {!!}
      usesInput` (_⊂_ {_} {_} {.(_∂_ _ _)} {_} {↓} elf lf) (¬∅ s) | ∂→ ns = {!!}
      usesInput` (_⊂_ {_} {_} {.(_∂_ _ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∂→ ns₁ = {!!}
      usesInput` (_⊂_ {ell = ell} {ind = ind ←∧} elf lf) (¬∅ s) with (contruct $ add s (ind ←∧) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∧} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∧} elf lf) (¬∅ s) | ns ←∧ = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∧} elf lf) (¬∅ s) | ∧→ ns = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∧} elf lf) (¬∅ s) | ns ←∧→ ns₁ = {!!}
      usesInput` (_⊂_ {ell = ell} {ind = ∧→ ind} elf lf) (¬∅ s) with (contruct $ add s (∧→ ind) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {∧→ ind} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {_} {_} {ell} {_} {∧→ ind} elf lf) (¬∅ s) | ns ←∧ = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {∧→ ind} elf lf) (¬∅ s) | ∧→ ns = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {∧→ ind} elf lf) (¬∅ s) | ns ←∧→ ns₁ = {!!}
      usesInput` (_⊂_ {ell = ell} {ind = ind ←∨} elf lf) (¬∅ s) with (contruct $ add s (ind ←∨) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∨} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∨} elf lf) (¬∅ s) | ns ←∨ = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∨} elf lf) (¬∅ s) | ∨→ ns = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∨} elf lf) (¬∅ s) | ns ←∨→ ns₁ = {!!}
      usesInput` (_⊂_ {ell = ell} {ind = ∨→ ind} elf lf) (¬∅ s) with (contruct $ add s (∨→ ind) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {∨→ ind} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {_} {_} {ell} {_} {∨→ ind} elf lf) (¬∅ s) | ns ←∨ = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {∨→ ind} elf lf) (¬∅ s) | ∨→ ns = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {∨→ ind} elf lf) (¬∅ s) | ns ←∨→ ns₁ = {!!}
      usesInput` (_⊂_ {ell = ell} {ind = ind ←∂} elf lf) (¬∅ s) with (contruct $ add s (ind ←∂) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∂} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∂} elf lf) (¬∅ s) | ns ←∂ = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∂} elf lf) (¬∅ s) | ∂→ ns = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∂} elf lf) (¬∅ s) | ns ←∂→ ns₁ = {!!}
      usesInput` (_⊂_ {ell = ell} {ind = ∂→ ind} elf lf) (¬∅ s) with (contruct $ add s (∂→ ind) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {∂→ ind} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {_} {_} {ell} {_} {∂→ ind} elf lf) (¬∅ s) | ns ←∂ = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {∂→ ind} elf lf) (¬∅ s) | ∂→ ns = {!!}
      usesInput` (_⊂_ {_} {_} {ell} {_} {∂→ ind} elf lf) (¬∅ s) | ns ←∂→ ns₁ = {!!}

--with (contruct $ add s ind ell)
--      ... | ns = {!!}
      usesInput` (tr lf₁) s = {!!}
      usesInput` (com df lf₁) s = {!!}
      usesInput` (call x) s = {!!}
  
  



