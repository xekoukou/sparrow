--{-# OPTIONS --exact-split #-}

module LinFun where

open import LinT public
open import Size
open import Level
open import Function
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit

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
     com : ∀{ll frll rll} → {prfi : onlyOneNilOrNoNilFinite ll ≡ true}
           → {prfo : onlyOneNilOrNoNilFinite frll ≡ true}
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
      usesInput` (_⊂_ {ell = ell} {ind = ↓} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns) 
      usesInput` (_⊂_ {ell = ell} {ind = ind ←∧} elf lf) (¬∅ s) with (contruct $ add s (ind ←∧) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∧} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {ell = ell} {ind = ind ←∧} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` (_⊂_ {ell = ell} {ind = ∧→ ind} elf lf) (¬∅ s) with (contruct $ add s (∧→ ind) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {∧→ ind} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {ell = ell} {ind = ∧→ ind} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` (_⊂_ {ell = ell} {ind = ind ←∨} elf lf) (¬∅ s) with (contruct $ add s (ind ←∨) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∨} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {ell = ell} {ind = ind ←∨} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` (_⊂_ {ell = ell} {ind = ∨→ ind} elf lf) (¬∅ s) with (contruct $ add s (∨→ ind) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {∨→ ind} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {ell = ell} {ind = ∨→ ind} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` (_⊂_ {ell = ell} {ind = ind ←∂} elf lf) (¬∅ s) with (contruct $ add s (ind ←∂) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {ind ←∂} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {ell = ell} {ind = ind ←∂} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` (_⊂_ {ell = ell} {ind = ∂→ ind} elf lf) (¬∅ s) with (contruct $ add s (∂→ ind) ell)
      usesInput` (_⊂_ {_} {_} {ell} {_} {∂→ ind} elf lf) (¬∅ s) | ↓ = true
      usesInput` (_⊂_ {ell = ell} {ind = ∂→ ind} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` (tr lf) ∅ = usesInput` lf ∅
      usesInput` (tr {{ltr = ltr}} lf) (¬∅ s) = usesInput` lf $ ¬∅ (SetLLMp.tran s ltr)
      usesInput` (com df lf) s = true
      usesInput` (call ∞lf) s = true
  
open ∞LFun public



module _ where

  data NextLFun : Set where
    I    : NextLFun
    call : NextLFun
    com  : NextLFun
  
  nextLFun : ∀{i u rll ll} → LFun {i} {u} {rll} {ll} → NextLFun
  nextLFun I = I
  nextLFun (lf ⊂ lf₁) = nextLFun lf
  nextLFun (tr lf) = nextLFun lf
  nextLFun (com df lf) = com 
  nextLFun (call x) = call

--cutT : ∀{i u rll ll} → {j : Size< i} → LFun {i} {u} {rll} {ll} → LinLogic j {u} × LinLogic j {u}
--cutT {i} {u} {rll} {.rll} {.i} I = (rll , rll)
--cutT {i} {u} {rll} {ll} (_⊂_ {ind = ind} x x₁) = let (crll , cll) = cutT x
--                                   in (crll , replLL ll ind cll)
--cutT {i} {u} {rll} {ll} (tr {orll = orll} x) = (rll , orll)
--cutT {i} {u} {rll} {ll} (com {frll = frll} df x) = (rll , frll)
--cutT {i} {u} {(call ∞rll)} {(call ∞ll)} (call x) = ({!step ∞rll!} , {!!} )
--  

-- cll is the linear logic that is introduced after the last Com.
-- The index points us to the last transformation of the LinLogic, the last place we received data.
-- We need to preserve the ∨(or) choices of the previous inputs.
  mutual
    data Spec :  ∀{i u ll rll s} →  LinState {ll = ll} s → LFun {i} {u} {rll} {ll} → Set where  

    data Input {i : Size} {u} : ∀{ll rll s} →  LinState {ll = ll} s → LFun {i} {u} {rll} {ll} → Set where
--        I    : ∀{ll rll s} → ⦃prf : (nextLFun lf ≡ I)⦄ → ⦃prf₁ : FilledSetLL {ll = ll} s⦄→ Input (¬∅ s)  
--      next : in → Input → Input
--      call : ∞input → Input → Input

    record ∞Input {i u ∞ll ∞rll} ( ∞ldt : ∞LinDepT ∞ll) ( ∞lf : ∞LFun {i} {u} {∞rll} {∞ll}) : Set where
      coinductive
      field
        step : {j : Size< i} → Input {i = j} {ll = step ∞ll} {rll = step ∞rll} ∅ (step ∞ldt) (step ∞lf)

