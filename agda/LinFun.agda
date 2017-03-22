-- {-# OPTIONS --show-implicit #-}

module LinFun where

open import Common
open import LinLogic
open import LinDepT
open import LinT 
open import SetLL
open import SetLLRem
open import SetLLProp

open import Data.Bool
open import Data.Unit hiding (_≤_ ; _≤?_)

open import Data.Product
open import Data.Sum


private
  _c∪ₘₛ_ : ∀{i u} → {ll : LinLogic i {u}} → MSetLL ll → MSetLL ll → MSetLL ll
  _c∪ₘₛ_ ∅ ∅            = ∅
  _c∪ₘₛ_ ∅ (¬∅ s)       = ¬∅ $ contruct s
  _c∪ₘₛ_ (¬∅ fs) ∅      = ¬∅ $ contruct fs
  _c∪ₘₛ_ (¬∅ fs) (¬∅ s) = ¬∅ $ contruct $ fs ∪ₛ s
        
-- We send to the receiver both the values the type depends and the value of the type. This way, we achieve locality in terms of finding the type of the incoming value.
-- We need to point that the receiver and the sender are the same node.


mutual
  data LFun {u} : {i : Size} → {j : Size< ↑ i} → {rll : LinLogic j {u}} → {ll : LinLogic i {u}} → Set (lsuc u) where
   I   : {i : Size} → ∀{rll} → LFun {u} {i} {_} {rll} {rll}
   _⊂_ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{pll ll ell rll} → {ind : IndexLL {i} pll ll} → (elf : LFun {_} {i} {j} {ell} {pll})
         → {{prf : usesInputT elf}} → LFun {_} {j} {k} {rll} {(replLL ll ind ell)}
         → LFun {_} {i} {k} {rll} {ll}
   -- Do we need to set ltr as an instance variable?
   tr  : {i : Size} → {j : Size< ↑ i} → ∀{ll orll rll} → {{ltr : LLTr orll ll}} → LFun {_} {i} {j} {rll} {orll} → LFun {_} {i} {j} {rll} {ll}
   obs : {i : Size} → {j : Size< i} → {k : Size< ↑ j} → ∀{∞ll rll} → LFun {_} {j} {k} {rll} {(step ∞ll)} → LFun {_} {i} {k} {rll} {call ∞ll}
   com : {i : Size} → {j : Size< ↑ i} → ∀{rll ll} → {frll : LinLogic i}
         → ⦃ prfi : onlyOneNilOrNoNilFinite ll ≡ true ⦄ → ⦃ prfo : onlyOneNilOrNoNilFinite frll ≡ true ⦄
         → (df : (ldt : LinDepT ll) → LinT ldt → LinDepT frll) → LFun {rll = rll} {ll = frll}
         → LFun {_} {i} {j} {rll = rll} {ll = ll}
   -- prf guarantees that calls will always contain an input that is not a call. Thus when we remove calls based on previous input availability, only one per call will be removed.
   call : {i : Size} → {j : Size< ↑ i} → ∀{ll ∞rll prf} → ∞LFun {i} {_} {∞rll} {ll} {{prf}} → LFun {_} {i} {j} {call ∞rll} {ll}

-- We need to create an observe function, that will unfold all first calls. Then when call is unfolded, the remaining calls generate obs.↑
  record ∞LFun {i : Size} {u} {∞rll : ∞LinLogic i {u}} {ll : LinLogic i {u}} {{prf : notCall ll}} : Set (lsuc u) where
    coinductive
    field
      step : {j : Size< i} → Σ (LFun {_} {j} {j} {(step ∞rll)} {unfold ll}) (λ x → usesInputT x)



-- calls in LinLogic need to be excluded from this, thus we need to add-calls in SetLL.
  data usesInputT {i : Size} {j : Size< ↑ i } {u rll ll} (lf : LFun {u} {i} {j} {rll} {ll}) : Set where
    usesInputC : usesInputT` {i} {j} {u} {rll} {ll} lf ∅ → usesInputT {i} {j} {u} {rll} {ll} lf

  data usesInputT` : {i : Size} → {j : Size< ↑ i } → ∀{u rll ll} → LFun {u} {i} {j} {rll} {ll} → MSetLL ll → Set where
    usesInputC`⊂↓ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll ell ll elf prf lf ms}
                    → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {ll} {ll} {ell} {rll} {↓} elf {{prf}} lf) ms
    usesInputC`⊂←∧∅ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll lll llr ell ind elf prf lf}
                      → let ns = ∅-add (ind ←∧) ell in
                        let ll = LinLogic._∧_ lll llr in
                        usesInputT` {j} {k} {u} {rll} {replLL ll (ind ←∧) ell} lf (¬∅ ns)
                      → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∧_ lll llr} {ell} {rll} {ind ←∧} elf {{prf}} lf) ∅
    usesInputC`⊂←∧¬∅c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr ind s elf prf lf}
                     → {cTo↓ : (contruct $ add s (ind ←∧) ell) ≡ ↓} 
                     → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∧_ lll llr} {ell} {rll} {ind ←∧} elf {{prf}} lf) (¬∅ s)
    usesInputC`⊂←∧¬∅¬c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr s ind elf prf lf}
                      → let ns = contruct $ add s (ind ←∧) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∧_ lll llr in usesInputT` {j} {k} {u} {rll} {replLL ll (ind ←∧) ell} lf (¬∅ ns)
                      → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {ll} {ell} {rll} {ind ←∧} elf {{prf}} lf) (¬∅ s)
    usesInputC`⊂∧→∅ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll lll llr ell ind elf prf lf}
                      → let ns = ∅-add (∧→ ind) ell in
                        let ll = LinLogic._∧_ lll llr in
                        usesInputT` {j} {k} {u} {rll} {replLL ll (∧→ ind) ell} lf (¬∅ ns)
                      → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∧_ lll llr} {ell} {rll} {∧→ ind} elf {{prf}} lf) ∅
    usesInputC`⊂∧→¬∅c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr ind s elf prf lf}
                     → {cTo↓ : (contruct $ add s (∧→ ind) ell) ≡ ↓} 
                     → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∧_ lll llr} {ell} {rll} {∧→ ind} elf {{prf}} lf) (¬∅ s)
    usesInputC`⊂∧→¬∅¬c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr s ind elf prf lf}
                      → let ns = contruct $ add s (∧→ ind) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∧_ lll llr in usesInputT` {j} {k} {u} {rll} {replLL ll (∧→ ind) ell} lf (¬∅ ns)
                      → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {ll} {ell} {rll} {∧→ ind} elf {{prf}} lf) (¬∅ s)
    usesInputC`⊂←∨∅ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll lll llr ell ind elf prf lf}
                      → let ns = ∅-add (ind ←∨) ell in
                        let ll = LinLogic._∨_ lll llr in
                        usesInputT` {j} {k} {u} {rll} {replLL ll (ind ←∨) ell} lf (¬∅ ns)
                      → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∨_ lll llr} {ell} {rll} {ind ←∨} elf {{prf}} lf) ∅
    usesInputC`⊂←∨¬∅c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr ind s elf prf lf}
                     → {cTo↓ : (contruct $ add s (ind ←∨) ell) ≡ ↓} 
                     → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∨_ lll llr} {ell} {rll} {ind ←∨} elf {{prf}} lf) (¬∅ s)
    usesInputC`⊂←∨¬∅¬c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr s ind elf prf lf}
                      → let ns = contruct $ add s (ind ←∨) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∨_ lll llr in usesInputT` {j} {k} {u} {rll} {replLL ll (ind ←∨) ell} lf (¬∅ ns)
                      → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {ll} {ell} {rll} {ind ←∨} elf {{prf}} lf) (¬∅ s)
    usesInputC`⊂∨→∅ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll lll llr ell ind elf prf lf}
                      → let ns = ∅-add (∨→ ind) ell in
                        let ll = LinLogic._∨_ lll llr in
                        usesInputT` {j} {k} {u} {rll} {replLL ll (∨→ ind) ell} lf (¬∅ ns)
                      → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∨_ lll llr} {ell} {rll} {∨→ ind} elf {{prf}} lf) ∅
    usesInputC`⊂∨→¬∅c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr ind s elf prf lf}
                     → {cTo↓ : (contruct $ add s (∨→ ind) ell) ≡ ↓} 
                     → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∨_ lll llr} {ell} {rll} {∨→ ind} elf {{prf}} lf) (¬∅ s)
    usesInputC`⊂∨→¬∅¬c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr s ind elf prf lf}
                      → let ns = contruct $ add s (∨→ ind) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∨_ lll llr in usesInputT` {j} {k} {u} {rll} {replLL ll (∨→ ind) ell} lf (¬∅ ns)
                      → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {ll} {ell} {rll} {∨→ ind} elf {{prf}} lf) (¬∅ s)
    usesInputC`⊂←∂∅ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll lll llr ell ind elf prf lf}
                      → let ns = ∅-add (ind ←∂) ell in
                        let ll = LinLogic._∂_ lll llr in
                        usesInputT` {j} {k} {u} {rll} {replLL ll (ind ←∂) ell} lf (¬∅ ns)
                    → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∂_ lll llr} {ell} {rll} {ind ←∂} elf {{prf}} lf) ∅
    usesInputC`⊂←∂¬∅c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr ind s elf prf lf}
                     → {cTo↓ : (contruct $ add s (ind ←∂) ell) ≡ ↓} 
                     → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∂_ lll llr} {ell} {rll} {ind ←∂} elf {{prf}} lf) (¬∅ s)
    usesInputC`⊂←∂¬∅¬c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr s ind elf prf lf}
                      → let ns = contruct $ add s (ind ←∂) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∂_ lll llr in usesInputT` {j} {k} {u} {rll} {replLL ll (ind ←∂) ell} lf (¬∅ ns)
                      → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {ll} {ell} {rll} {ind ←∂} elf {{prf}} lf) (¬∅ s)
    usesInputC`⊂∂→∅ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll lll llr ell ind elf prf lf}
                      → let ns = ∅-add (∂→ ind) ell in
                        let ll = LinLogic._∂_ lll llr in
                        usesInputT` {j} {k} {u} {rll} {replLL ll (∂→ ind) ell} lf (¬∅ ns)
                    → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∂_ lll llr} {ell} {rll} {∂→ ind} elf {{prf}} lf) ∅
    usesInputC`⊂∂→¬∅c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr ind s elf prf lf}
                     → {cTo↓ : (contruct $ add s (∂→ ind) ell) ≡ ↓} 
                     → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {LinLogic._∂_ lll llr} {ell} {rll} {∂→ ind} elf {{prf}} lf) (¬∅ s)
    usesInputC`⊂∂→¬∅¬c : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell lll llr s ind elf prf lf}
                      → let ns = contruct $ add s (∂→ ind) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∂_ lll llr in usesInputT` {j} {k} {u} {rll} {replLL ll (∂→ ind) ell} lf (¬∅ ns)
                      → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {ll} {ell} {rll} {∂→ ind} elf {{prf}} lf) (¬∅ s)
    usesInputC`tr∅ : {i : Size} → {j : Size< ↑ i} → ∀{u ll rll orll ltr lf}
                     → usesInputT` lf ∅
                     → usesInputT` {_} {_} (tr {u} {i} {j}  {ll} {orll} {rll} {{ltr}} lf) ∅
    usesInputC`trs : {i : Size} → {j : Size< ↑ i} → ∀{u ll rll orll ltr lf s}
                     → usesInputT` lf $ ¬∅ (SetLL.tran s ltr)
                     → usesInputT` {_} {_} (tr {u} {i} {j}  {ll} {orll} {rll} {{ltr}} lf) (¬∅ s)
    usesInputC`com : {i : Size} → {j : Size< ↑ i} → ∀{u rll ll ms frll prfi prfo  df lf}
                     → usesInputT` (com {u} {i} {j} {rll} {ll} {frll}  ⦃ prfi = prfi ⦄ ⦃ prfo = prfo ⦄ df lf) ms
    usesInputC`callc : {i : Size} → {j : Size< ↑ i} → ∀{u ∞rll ll ms prf ∞lf}
                       → {cTo↓ : ((fillWithCalls ll) c∪ₘₛ ms ) ≡ ¬∅ ↓} 
                       → usesInputT` (call {u} {i} {j} {ll} {∞rll} {prf} ∞lf) ms 


open ∞LFun public

doesItUseAllInputs : {i : Size} → {j : Size< ↑ i } → ∀{u rll ll} → (lf : LFun {u} {i} {j} {rll} {ll}) → Dec (usesInputT lf)
doesItUseAllInputs {ll = ll} lf with (doesItUseAllInputs` lf ∅) where
  doesItUseAllInputs` : {i : Size} → {j : Size< ↑ i } → ∀{u rll ll} → (lf : LFun {u} {i} {j} {rll} {ll}) → (ms : MSetLL ll) → Dec (usesInputT` lf ms)
  doesItUseAllInputs` I ms = no (λ ())
  doesItUseAllInputs` (_⊂_ {ell = ell} {ind = ↓} elf lf) ms = yes usesInputC`⊂↓
  doesItUseAllInputs` plf@(_⊂_ {pll = pll} {ll = ll} {ell = ell} {ind = ind ←∧} elf lf) ∅ with (doesItUseAllInputs` lf (¬∅ (∅-add (ind ←∧) ell)))
  ... | yes p = yes (usesInputC`⊂←∧∅ p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂←∧∅ x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (ind ←∧)} elf lf) (¬∅ s) with (isEq (contruct $ add s (ind ←∧) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂←∧¬∅c {cTo↓ = cTo↓})
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (ind ←∧) ell))
  ... | yes p = yes (usesInputC`⊂←∧¬∅¬c {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂←∧¬∅c {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂←∧¬∅¬c x) = p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = ∧→ ind} elf lf) ∅ with (doesItUseAllInputs` lf (¬∅ (∅-add (∧→ ind) ell)))
  ... | yes p = yes (usesInputC`⊂∧→∅ p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂∧→∅ x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (∧→ ind)} elf lf) (¬∅ s) with (isEq (contruct $ add s (∧→ ind) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂∧→¬∅c {cTo↓ = cTo↓})
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (∧→ ind) ell))
  ... | yes p = yes (usesInputC`⊂∧→¬∅¬c {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂∧→¬∅c {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂∧→¬∅¬c x) = p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = ind ←∨} elf lf) ∅ with (doesItUseAllInputs` lf (¬∅ (∅-add (ind ←∨) ell)))
  ... | yes p = yes (usesInputC`⊂←∨∅ p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂←∨∅ x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (ind ←∨)} elf lf) (¬∅ s) with (isEq (contruct $ add s (ind ←∨) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂←∨¬∅c {cTo↓ = cTo↓}) 
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (ind ←∨) ell))
  ... | yes p = yes (usesInputC`⊂←∨¬∅¬c {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂←∨¬∅c {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂←∨¬∅¬c x) = p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = ∨→ ind} elf lf) ∅ with (doesItUseAllInputs` lf (¬∅ (∅-add (∨→ ind) ell)))
  ... | yes p = yes (usesInputC`⊂∨→∅ p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂∨→∅ x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (∨→ ind)} elf lf) (¬∅ s) with (isEq (contruct $ add s (∨→ ind) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂∨→¬∅c {cTo↓ = cTo↓})
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (∨→ ind) ell))
  ... | yes p = yes (usesInputC`⊂∨→¬∅¬c {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂∨→¬∅c {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂∨→¬∅¬c x) = p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = ind ←∂} elf lf) ∅ with (doesItUseAllInputs` lf (¬∅ (∅-add (ind ←∂) ell)))
  ... | yes p = yes (usesInputC`⊂←∂∅ p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂←∂∅ x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (ind ←∂)} elf lf) (¬∅ s) with (isEq (contruct $ add s (ind ←∂) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂←∂¬∅c {cTo↓ = cTo↓}) 
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (ind ←∂) ell))
  ... | yes p = yes (usesInputC`⊂←∂¬∅¬c {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂←∂¬∅c {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂←∂¬∅¬c x) = p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = ∂→ ind} elf lf) ∅ with (doesItUseAllInputs` lf (¬∅ (∅-add (∂→ ind) ell)))
  ... | yes p = yes (usesInputC`⊂∂→∅ p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂∂→∅ x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (∂→ ind)} elf lf) (¬∅ s) with (isEq (contruct $ add s (∂→ ind) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂∂→¬∅c {cTo↓ = cTo↓})
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (∂→ ind) ell))
  ... | yes p = yes (usesInputC`⊂∂→¬∅¬c {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂∂→¬∅c {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂∂→¬∅¬c x) = p x
  doesItUseAllInputs` plf@(tr lf) ∅ with (doesItUseAllInputs` lf ∅)
  ... | yes p = yes (usesInputC`tr∅ p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`tr∅ x) = ¬p x
  doesItUseAllInputs` plf@(tr {{ltr = ltr}} lf ) (¬∅ s) with (doesItUseAllInputs` lf $ ¬∅ (SetLL.tran s ltr))
  ... | yes p  = yes (usesInputC`trs p)
  ... | no ¬p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`trs x) = ¬p x
-- Since we should never reach at obs, we set it to ⊥ in hopes of catching any bugs.
  doesItUseAllInputs` (obs lf) ms = no (λ ())
  doesItUseAllInputs` (com df lf) ms = yes usesInputC`com
-- We add all the calls that are here and check if together with ms it contructs to ↓.
  doesItUseAllInputs` {ll = ll} plf@(call x) ms with (isEqM ((fillWithCalls ll) c∪ₘₛ ms) (¬∅ ↓) )
  ... | yes cTo↓ = yes (usesInputC`callc {cTo↓ = cTo↓})
  ... | no ¬cTo↓ = no hf where
    hf : usesInputT` plf ms → ⊥
    hf (usesInputC`callc {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
... | yes p = yes (usesInputC p)
... | no ¬p =  no hf where
    hf : usesInputT lf → ⊥
    hf (usesInputC x) = ¬p x




module _ where

  private
    -- The fact that we do fillAllLowerRem is important for the impossible to never be reached because delRem deletes everything we do not have memory of,
    -- thus it removes complete sets if one element is removed from it.
    pdelRem : ∀{pi} → {i : Size< ↑ pi} → ∀{u ll pll q} → {j : Size< ↑ i} → SetLLRem {pi} {i} pll ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic j)
              → SetLLRem {pi} {j} pll (replLL ll ind rll)
    pdelRem sr ind rll with (delRem sr ind rll)
    ... | ∅    = IMPOSSIBLE
    ... | ¬∅ x = x


  findUnusedorPrUI : {i : Size} → {j : Size< ↑ i } → ∀{u rll ll} → (lf : LFun {u} {i} {j} {rll} {ll}) → (usesInputT lf) ⊎ Σ (Size< ↑ i) (λ k → Σ (LinLogic k {u}) (λ ull → (SetLLRem ll ull)))
  findUnusedorPrUI {ll = ll} lf with (findUnusedorPrUI` {pll = ll} lf ∅ (fillAllLowerRem ll)) where
    findUnusedorPrUI` : {pi : Size} → {i : Size< ↑ pi} → {j : Size< ↑ i } → ∀{u rll pll ll} → (lf : LFun {u} {i} {j} {rll} {ll}) → (ms : MSetLL ll) → (sr : SetLLRem {pi} pll ll) → (usesInputT` lf ms) ⊎ Σ (Size< ↑ pi) (λ k → Σ (LinLogic k {u}) (λ ull → (SetLLRem pll ull)))
    findUnusedorPrUI` I ms sr = inj₂ (_ , _ , sr)
    findUnusedorPrUI` (_⊂_ {ell = ell} {ind = ↓} elf lf) ms sr = inj₁ usesInputC`⊂↓
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = ind ←∧} elf lf) ∅ sr with (findUnusedorPrUI` lf (¬∅ (∅-add (ind ←∧) ell)) (pdelRem sr (ind ←∧) ell))
    ... | (inj₁ p) = inj₁ (usesInputC`⊂←∧∅ p)
    ... | (inj₂ p) = inj₂ p
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = (ind ←∧)} elf lf) (¬∅ s) sr with (isEq (contruct $ add s (ind ←∧) ell) ↓)
    ... | yes cTo↓ = inj₁ (usesInputC`⊂←∧¬∅c {cTo↓ = cTo↓})
    ... | no ¬cTo↓ with (findUnusedorPrUI` lf (¬∅ $ contruct $ add s (ind ←∧) ell) (pdelRem sr (ind ←∧) ell) )
    ... | inj₁ p = inj₁ (usesInputC`⊂←∧¬∅¬c {¬cTo↓ = ¬cTo↓} p)
    ... | inj₂ p  = inj₂ p 
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = ∧→ ind} elf lf) ∅ sr with (findUnusedorPrUI` lf (¬∅ (∅-add (∧→ ind) ell)) (pdelRem sr (∧→ ind) ell))
    ... | inj₁ p = inj₁ (usesInputC`⊂∧→∅ p)
    ... | inj₂ p = inj₂ p 
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = (∧→ ind)} elf lf) (¬∅ s) sr with (isEq (contruct $ add s (∧→ ind) ell) ↓)
    ... | yes cTo↓ = inj₁ (usesInputC`⊂∧→¬∅c {cTo↓ = cTo↓})
    ... | no ¬cTo↓ with (findUnusedorPrUI` lf (¬∅ $ contruct $ add s (∧→ ind) ell) (pdelRem sr (∧→ ind) ell))
    ... | inj₁ p = inj₁ (usesInputC`⊂∧→¬∅¬c {¬cTo↓ = ¬cTo↓} p)
    ... | inj₂ p  = inj₂ p
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = ind ←∨} elf lf) ∅ sr with (findUnusedorPrUI` lf (¬∅ (∅-add (ind ←∨) ell)) (pdelRem sr (ind ←∨) ell))
    ... | inj₁ p = inj₁ (usesInputC`⊂←∨∅ p)
    ... | inj₂ p = inj₂ p
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = (ind ←∨)} elf lf) (¬∅ s) sr with (isEq (contruct $ add s (ind ←∨) ell) ↓)
    ... | yes cTo↓ = inj₁ (usesInputC`⊂←∨¬∅c {cTo↓ = cTo↓}) 
    ... | no ¬cTo↓ with (findUnusedorPrUI` lf (¬∅ $ contruct $ add s (ind ←∨) ell) (pdelRem sr (ind ←∨) ell))
    ... | inj₁ p = inj₁ (usesInputC`⊂←∨¬∅¬c {¬cTo↓ = ¬cTo↓} p)
    ... | inj₂ p  = inj₂ p
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = ∨→ ind} elf lf) ∅ sr with (findUnusedorPrUI` lf (¬∅ (∅-add (∨→ ind) ell)) (pdelRem sr (∨→ ind) ell))
    ... | inj₁ p = inj₁ (usesInputC`⊂∨→∅ p)
    ... | inj₂ p = inj₂ p
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = (∨→ ind)} elf lf) (¬∅ s) sr with (isEq (contruct $ add s (∨→ ind) ell) ↓)
    ... | yes cTo↓ = inj₁ (usesInputC`⊂∨→¬∅c {cTo↓ = cTo↓})
    ... | no ¬cTo↓ with (findUnusedorPrUI` lf (¬∅ $ contruct $ add s (∨→ ind) ell) (pdelRem sr (∨→ ind) ell))
    ... | inj₁ p = inj₁ (usesInputC`⊂∨→¬∅¬c {¬cTo↓ = ¬cTo↓} p)
    ... | inj₂ p  = inj₂ p 
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = ind ←∂} elf lf) ∅ sr with (findUnusedorPrUI` lf (¬∅ (∅-add (ind ←∂) ell)) (pdelRem sr (ind ←∂) ell))
    ... | inj₁ p = inj₁ (usesInputC`⊂←∂∅ p)
    ... | inj₂ p = inj₂ p
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = (ind ←∂)} elf lf) (¬∅ s) sr with (isEq (contruct $ add s (ind ←∂) ell) ↓)
    ... | yes cTo↓ = inj₁ (usesInputC`⊂←∂¬∅c {cTo↓ = cTo↓}) 
    ... | no ¬cTo↓ with (findUnusedorPrUI` lf (¬∅ $ contruct $ add s (ind ←∂) ell) (pdelRem sr (ind ←∂) ell))
    ... | inj₁ p = inj₁ (usesInputC`⊂←∂¬∅¬c {¬cTo↓ = ¬cTo↓} p)
    ... | inj₂ p  = inj₂ p
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = ∂→ ind} elf lf) ∅ sr with (findUnusedorPrUI` lf (¬∅ (∅-add (∂→ ind) ell)) (pdelRem sr (∂→ ind) ell))
    ... | inj₁ p = inj₁ (usesInputC`⊂∂→∅ p)
    ... | inj₂ p = inj₂ p
    findUnusedorPrUI` plf@(_⊂_ {ell = ell} {ind = (∂→ ind)} elf lf) (¬∅ s) sr with (isEq (contruct $ add s (∂→ ind) ell) ↓)
    ... | yes cTo↓ = inj₁ (usesInputC`⊂∂→¬∅c {cTo↓ = cTo↓})
    ... | no ¬cTo↓ with (findUnusedorPrUI` lf (¬∅ $ contruct $ add s (∂→ ind) ell) (pdelRem sr (∂→ ind) ell))
    ... | inj₁ p = inj₁ (usesInputC`⊂∂→¬∅¬c {¬cTo↓ = ¬cTo↓} p)
    ... | inj₂ p  = inj₂ p
    findUnusedorPrUI` plf@(tr {{ltr = ltr}} lf) ∅ sr with (findUnusedorPrUI` lf ∅ (tranRem sr ltr))
    ... | inj₁ p = inj₁ (usesInputC`tr∅ p)
    ... | inj₂ p = inj₂ p
    findUnusedorPrUI` plf@(tr {{ltr = ltr}} lf ) (¬∅ s) sr with (findUnusedorPrUI` lf (¬∅ (SetLL.tran s ltr)) (tranRem sr ltr))
    ... | inj₁ p  = inj₁ (usesInputC`trs p)
    ... | inj₂ p  = inj₂ p 
  -- Since we should never reach at obs, we set it to IMPOSSIBLE
    findUnusedorPrUI` (obs lf) ms sr = IMPOSSIBLE
    findUnusedorPrUI` (com df lf) ms sr = inj₁ usesInputC`com
  -- We add all the calls that are here and check if together with ms it contructs to ↓.
    findUnusedorPrUI` {ll = ll} plf@(call x) ms sr with (isEqM ((fillWithCalls ll) c∪ₘₛ ms) (¬∅ ↓) )
    ... | yes cTo↓ = inj₁ (usesInputC`callc {cTo↓ = cTo↓})
    ... | no ¬cTo↓ = inj₂ (_ , _ , sr)
  ... | inj₁ p = inj₁ (usesInputC p)
  ... | inj₂ p = inj₂ p 
  

notObs : ∀{i u ll} → {j : Size< ↑ i} → ∀{rll} → LFun {u} {i} {j} {rll} {ll} → Bool
notObs I = true
notObs (lf ⊂ lf₁) = (notObs lf) Data.Bool.∧ notObs lf₁
notObs (tr lf) = notObs lf
notObs (obs lf) = false
notObs (com df lf) = notObs lf
notObs (call x) = true


