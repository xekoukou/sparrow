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

-- We send to the receiver both the values the type depends and the value of the type. This way, we achieve locality in terms of finding the type of the incoming value.
-- We need to point that the receiver and the sender are the same node.

module _ where

  open SetLLMp
  
  mutual
    data LFun {u} {k : Size} : ∀{i j} → {rll : LinLogic j {u}} → {ll : LinLogic i {u}} → Set (suc u) where
     I   : ∀{rll} → LFun {rll = rll} {ll = rll}
     _⊂_ : ∀{pll ll ell rll} → {ind : IndexLL pll ll} → (elf : LFun {rll = ell} {ll = pll})
           → {{prf : usesInput elf ≡ true}} → LFun {rll = rll} {ll = (replLL ll ind ell)}
           → LFun {rll = rll} {ll = ll}
     --DO we need to set ltr as an instance varriable?
     tr  : ∀{ll orll rll} → {{ltr : LLTr orll ll}} → LFun {rll = rll} {ll = orll} → LFun {rll = rll} {ll = ll}
     obs : ∀{∞ll rll} → LFun {rll = rll} {ll = step ∞ll} → LFun {rll = rll} {ll = call ∞ll}
     com : ∀{ll frll rll} → {prfi : onlyOneNilOrNoNilFinite ll ≡ true}
           → {prfo : onlyOneNilOrNoNilFinite frll ≡ true}
           → (df : (ldt : LinDepT ll) → LinT ldt → LinDepT frll) → LFun {rll = rll} {ll = frll}
           → LFun {rll = rll} {ll = ll}
     call : ∀{ll ∞rll} → ∞LFun {∞rll = ∞rll} {ll = ll} → LFun {rll = call ∞rll} {ll = ll}
  
  
    record ∞LFun {k i u} {∞rll : ∞LinLogic i {u}} {ll : LinLogic i {u}} : Set (suc u) where
      coinductive
      field
        step : {j : Size< k} → LFun {k = j} {rll = step ∞rll} {ll}

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
    com  : NextLFun
    call : NextLFun
  
  nextLFun : ∀{i u rll ll} → LFun {i} {u} {rll} {ll} → NextLFun
  nextLFun I = I
  nextLFun (lf ⊂ lf₁) = nextLFun lf
  nextLFun (tr lf) = nextLFun lf
  nextLFun (com df lf) = com 
  nextLFun (call x) = call

  notCall : NextLFun → Set
  notCall I = ⊤
  notCall com = ⊤
  notCall call = ⊥

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
    data Spec :  ∀{i u ll rll} → LinDepT ll → LFun {i} {u} {rll} {ll} → Set where  

    data Input {i : Size} {u} : ∀{rll ll} →  LinDepT ll → LFun {i} {u} {rll} {ll} → Set (suc u) where
      I    : ∀{rll ll ldt lf} → ⦃ prf : nextLFun {i} {u} {rll} {ll} lf ≡ I ⦄ → Input {rll = rll} ldt lf
      next : ∀{rll ll ldt lf} → LinT ldt → ⦃ prf : nextLFun {i} {u} {rll} {ll} lf ≡ com ⦄ → Input {i} {u} {rll} {ll} ldt lf
--      next : in → Input → Input
--      call : ∞input → Input → Input

    record ∞Input {i u ∞ll ∞rll} ( ∞ldt : ∞LinDepT ∞ll) ( ∞lf : ∞LFun {i} {u} {∞rll} {∞ll}) : Set (suc u) where
      coinductive
      field
        step : {j : Size< i} → Input {i = j} {rll = step ∞rll} {ll = step ∞ll} (step ∞ldt) (step ∞lf)

