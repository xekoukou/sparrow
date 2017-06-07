{-# OPTIONS --exact-split #-}

module LinFun where

open import Common
open import LinLogic
open import LinLogicProp
open import LinDepT
open import LinT 
open import SetLL
open import SetLLRem

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


module _ where

-- UsesInput tries to find that all inputs have been used. By definition, calls are not to be used unless observed.
-- Thus we need to add them in the set.
-- Since LinLogic calls can only be consumed by LinFun calls, we can add them when we reach the appropriate LinFun call.

  open import Data.List
  open import Data.Product


  findCalls : ∀{i u} → (ll : LinLogic i {u}) → List (Σ (LinLogic i {u}) (λ pll → IndexLL pll ll))
  findCalls ∅ = []
  findCalls (τ x) = []
  findCalls (li ∧ ri) = (Data.List.map (λ x → ((proj₁ x) , (proj₂ x) ←∧)) (findCalls li)) ++ (Data.List.map (λ x → ((proj₁ x) , ∧→ (proj₂ x) )) (findCalls ri))
  findCalls (li ∨ ri) = (Data.List.map (λ x → ((proj₁ x) , (proj₂ x) ←∨)) (findCalls li)) ++ (Data.List.map (λ x → ((proj₁ x) , ∨→ (proj₂ x) )) (findCalls ri))
  findCalls (li ∂ ri) = (Data.List.map (λ x → ((proj₁ x) , (proj₂ x) ←∂)) (findCalls li)) ++ (Data.List.map (λ x → ((proj₁ x) , ∂→ (proj₂ x) )) (findCalls ri))
  findCalls ll@(call x) = [(ll , ↓) ]


  fillWithCalls : ∀{i u} → (ll : LinLogic i {u}) → MSetLL ll
  fillWithCalls ll with (findCalls ll)
  fillWithCalls ll | [] = ∅
  fillWithCalls ll | x ∷ xs with (∅-add (proj₂ x) (proj₁ x))
  ... | r with (replLL ll (proj₂ x) (proj₁ x)) | (replLL-id ll (proj₂ x) (proj₁ x) refl) 
  fillWithCalls {i} {u} ll | x ∷ xs | r | .ll | refl = ¬∅ $ foldl hf r xs where
    hf : SetLL ll → Σ (LinLogic i {u}) (λ pll → IndexLL pll ll) → SetLL ll
    hf s ind with (add s (proj₂ x) (proj₁ x))
    ... | r with (replLL ll (proj₂ x) (proj₁ x)) | (replLL-id ll (proj₂ x) (proj₁ x) refl)
    hf s ind | r₁ | _ | refl = r₁






-- We send to the receiver both the values the type depends and the value of the type. This way, we achieve locality in terms of finding the type of the incoming value.
-- We need to point that the receiver and the sender are the same node.


mutual
  data LFun {i u} : (ll : LinLogic i {u}) → (rll : LinLogic i {u}) → Set (lsuc u) where
   I   : ∀{rll} → LFun {i} {u} rll rll
   _⊂_ : ∀{pll ll ell rll} → {ind : IndexLL {i} {u} pll ll} → (elf : LFun pll ell)
         → LFun (replLL ll ind ell) rll
         → LFun ll rll
   tr  : ∀{ll orll rll} → (ltr : LLTr orll ll) → LFun {i} {u} orll rll → LFun {i} {u} ll rll
   com : ∀{rll ll} → {frll : LinLogic i}
         → ⦃ prfi : onlyOneNilOrNoNilFinite ll ≡ true ⦄ → ⦃ prfo : onlyOneNilOrNoNilFinite frll ≡ true ⦄
         → (df : (ldt : LinDepT ll) → LinT ldt → LinDepT frll) → LFun frll rll
         → LFun {i} {u} ll rll
   --prf guarantees that calls will always contain an input that is not a call. Thus when we remove calls based on previous input availability, only one will be removed for a specific input.
   -- TODO ?? I think that prf is usefull but not for the previous argument. Without prf, we can have LFun that have no concrete inputs.
   call : ∀{ll ∞rll prf} → ∞LFun {i} {u} ll ∞rll {{prf}} → LFun {i} {u} ll (call ∞rll)

-- The comment is obsolete, remove : We need to create an observe function, that will unfold all first calls. Then when call is unfolded, the remaining calls generate obs.↑
  record ∞LFun {i u} (ll : LinLogic i {u}) (∞rll : ∞LinLogic i {u}) {{prf : notOnlyCall ll ≡ true}} : Set (lsuc u) where
    coinductive
    field
      step : {j : Size< i} → Σ (LFun {j} {u} (unfold ll) ((step ∞rll))) (λ x → usesInputT x) -- ??






-- UsesInput checks that the inputs will be used by the current LFun and not by the LFun of a call. This means that the search for the appropriate com is total, it takes a finite amount of time.

  data usesInputT {i u} {rll ll} (lf : LFun {i} {u} ll rll) : Set where
    usesInputC : usesInputT` {i} {u} {rll} {ll} lf ∅ → usesInputT {i} {u} {rll} {ll} lf

  data usesInputT` {i u} : ∀{rll ll} → LFun {i} {u} ll rll → MSetLL ll → Set where
    usesInputC`I  : ∀{ll ms} → usesInputT` {i} {u} {_} {ll} I ms 
    usesInputC`⊂↓ : ∀{rll ell ll elf lf ms}
                    → usesInputT` {i} {u} (_⊂_ {i} {u} {ll} {ll} {ell} {rll} {↓} elf lf) ms
    usesInputC`⊂←∧∅ : ∀{rll pll lll llr ell ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = ∅-add (ind ←∧) ell in
                        let ll = LinLogic._∧_ lll llr in
                        usesInputT` {i} {u} {rll} {replLL ll (ind ←∧) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∧_ lll llr} {ell} {rll} {ind ←∧} elf lf) ∅
    usesInputC`⊂←∧¬∅c : ∀{rll pll ell lll llr ind s elf lf}
                     →  usesInputT` {i} {u} {ell} {pll} elf ∅
                     → {cTo↓ : (contruct $ add s (ind ←∧) ell) ≡ ↓} 
                     → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∧_ lll llr} {ell} {rll} {ind ←∧} elf lf) (¬∅ s)
    usesInputC`⊂←∧¬∅¬c : ∀{rll pll ell lll llr s ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = contruct $ add s (ind ←∧) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∧_ lll llr in usesInputT` {i} {u} {rll} {replLL ll (ind ←∧) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind ←∧} elf lf) (¬∅ s)
    usesInputC`⊂∧→∅ :  ∀{rll pll lll llr ell ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = ∅-add (∧→ ind) ell in
                        let ll = LinLogic._∧_ lll llr in
                        usesInputT` {i} {u} {rll} {replLL ll (∧→ ind) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∧_ lll llr} {ell} {rll} {∧→ ind} elf lf) ∅
    usesInputC`⊂∧→¬∅c : ∀{rll pll ell lll llr ind s elf lf}
                     →  usesInputT` {i} {u} {ell} {pll} elf ∅
                     → {cTo↓ : (contruct $ add s (∧→ ind) ell) ≡ ↓} 
                     → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∧_ lll llr} {ell} {rll} {∧→ ind} elf lf) (¬∅ s)
    usesInputC`⊂∧→¬∅¬c : ∀{rll pll ell lll llr s ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = contruct $ add s (∧→ ind) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∧_ lll llr in usesInputT` {i} {u} {rll} {replLL ll (∧→ ind) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {∧→ ind} elf lf) (¬∅ s)
    usesInputC`⊂←∨∅ : ∀{rll pll lll llr ell ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = ∅-add (ind ←∨) ell in
                        let ll = LinLogic._∨_ lll llr in
                        usesInputT` {i} {u} {rll} {replLL ll (ind ←∨) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∨_ lll llr} {ell} {rll} {ind ←∨} elf lf) ∅
    usesInputC`⊂←∨¬∅c : ∀{rll pll ell lll llr ind s elf lf}
                     →  usesInputT` {i} {u} {ell} {pll} elf ∅
                     → {cTo↓ : (contruct $ add s (ind ←∨) ell) ≡ ↓} 
                     → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∨_ lll llr} {ell} {rll} {ind ←∨} elf lf) (¬∅ s)
    usesInputC`⊂←∨¬∅¬c : ∀{rll pll ell lll llr s ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = contruct $ add s (ind ←∨) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∨_ lll llr in usesInputT` {i} {u} {rll} {replLL ll (ind ←∨) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind ←∨} elf lf) (¬∅ s)
    usesInputC`⊂∨→∅ : ∀{rll pll lll llr ell ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = ∅-add (∨→ ind) ell in
                        let ll = LinLogic._∨_ lll llr in
                        usesInputT` {i} {u} {rll} {replLL ll (∨→ ind) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∨_ lll llr} {ell} {rll} {∨→ ind} elf lf) ∅
    usesInputC`⊂∨→¬∅c : ∀{rll pll ell lll llr ind s elf lf}
                     →  usesInputT` {i} {u} {ell} {pll} elf ∅
                     → {cTo↓ : (contruct $ add s (∨→ ind) ell) ≡ ↓} 
                     → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∨_ lll llr} {ell} {rll} {∨→ ind} elf lf) (¬∅ s)
    usesInputC`⊂∨→¬∅¬c : ∀{rll pll ell lll llr s ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = contruct $ add s (∨→ ind) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∨_ lll llr in usesInputT` {i} {u} {rll} {replLL ll (∨→ ind) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {∨→ ind} elf lf) (¬∅ s)
    usesInputC`⊂←∂∅ : ∀{rll pll lll llr ell ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = ∅-add (ind ←∂) ell in
                        let ll = LinLogic._∂_ lll llr in
                        usesInputT` {i} {u} {rll} {replLL ll (ind ←∂) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∂_ lll llr} {ell} {rll} {ind ←∂} elf lf) ∅
    usesInputC`⊂←∂¬∅c : ∀{rll pll ell lll llr ind s elf lf}
                     →  usesInputT` {i} {u} {ell} {pll} elf ∅
                     → {cTo↓ : (contruct $ add s (ind ←∂) ell) ≡ ↓} 
                     → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∂_ lll llr} {ell} {rll} {ind ←∂} elf lf) (¬∅ s)
    usesInputC`⊂←∂¬∅¬c : ∀{rll pll ell lll llr s ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = contruct $ add s (ind ←∂) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∂_ lll llr in usesInputT` {i} {u} {rll} {replLL ll (ind ←∂) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind ←∂} elf lf) (¬∅ s)
    usesInputC`⊂∂→∅ : ∀{rll pll lll llr ell ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = ∅-add (∂→ ind) ell in
                        let ll = LinLogic._∂_ lll llr in
                        usesInputT` {i} {u} {rll} {replLL ll (∂→ ind) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∂_ lll llr} {ell} {rll} {∂→ ind} elf lf) ∅
    usesInputC`⊂∂→¬∅c : ∀{rll pll ell lll llr ind s elf lf}
                     →  usesInputT` {i} {u} {ell} {pll} elf ∅
                     → {cTo↓ : (contruct $ add s (∂→ ind) ell) ≡ ↓} 
                     → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {LinLogic._∂_ lll llr} {ell} {rll} {∂→ ind} elf lf) (¬∅ s)
    usesInputC`⊂∂→¬∅¬c : ∀{rll pll ell lll llr s ind elf lf}
                      →  usesInputT` {i} {u} {ell} {pll} elf ∅
                      → let ns = contruct $ add s (∂→ ind) ell in {¬cTo↓ : ¬ (ns ≡ ↓)}
                      → let ll = LinLogic._∂_ lll llr in usesInputT` {i} {u} {rll} {replLL ll (∂→ ind) ell} lf (¬∅ ns)
                      → usesInputT` {i} {u} (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {∂→ ind} elf lf) (¬∅ s)
    usesInputC`tr∅ : ∀{ll rll orll ltr lf}
                     → usesInputT` lf ∅
                     → usesInputT` {_} {_} (tr {i} {u} {ll} {orll} {rll} ltr lf) ∅
    usesInputC`trs : ∀{ll rll orll ltr lf s}
                     → usesInputT` lf $ ¬∅ (SetLL.tran s ltr)
                     → usesInputT` {_} {_} (tr {i} {u} {ll} {orll} {rll} ltr lf) (¬∅ s)
    usesInputC`com : ∀{rll ll ms frll prfi prfo  df lf}
                     → usesInputT` (com {i} {u} {rll} {ll} {frll}  ⦃ prfi = prfi ⦄ ⦃ prfo = prfo ⦄ df lf) ms
    usesInputC`callc : ∀{∞rll ll ms prf ∞lf}
                       → {cTo↓ : ((fillWithCalls ll) c∪ₘₛ ms ) ≡ ¬∅ ↓} 
                       → usesInputT` (call {i} {u} {ll} {∞rll} {prf} ∞lf) ms 


open ∞LFun public

doesItUseAllInputs : {i : Size} → {j : Size< ↑ i } → ∀{u rll ll} → (lf : LFun {i} {u} ll rll) → Dec (usesInputT lf)
doesItUseAllInputs {ll = ll} lf with (doesItUseAllInputs` lf ∅) where
  doesItUseAllInputs` : {i : Size} → {j : Size< ↑ i } → ∀{u rll ll} → (lf : LFun {i} {u} ll rll) → (ms : MSetLL ll) → Dec (usesInputT` lf ms)
  doesItUseAllInputs` I ms = yes usesInputC`I
  doesItUseAllInputs` (_⊂_ {ell = ell} {ind = ↓} elf lf) ms = yes usesInputC`⊂↓
  doesItUseAllInputs` plf@(_⊂_ {pll = pll} {ll = ll} {ell = ell} {ind = ind ←∧} elf lf) ∅ with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂←∧∅ y x) = ¬y y
  ... | yes y with (doesItUseAllInputs` lf (¬∅ (∅-add (ind ←∧) ell)))
  ... | yes p = yes (usesInputC`⊂←∧∅ y p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂←∧∅ y x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (ind ←∧)} elf lf) (¬∅ s) with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂←∧¬∅c y) = ¬y y
    hf (usesInputC`⊂←∧¬∅¬c y y₁) = ¬y y
  ... | yes y with (isEq (contruct $ add s (ind ←∧) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂←∧¬∅c y {cTo↓ = cTo↓})
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (ind ←∧) ell))
  ... | yes p = yes (usesInputC`⊂←∧¬∅¬c y {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂←∧¬∅c y {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂←∧¬∅¬c y x) = p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = ∧→ ind} elf lf) ∅ with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂∧→∅ y y₁) = ¬y y
  ... | yes y with (doesItUseAllInputs` lf (¬∅ (∅-add (∧→ ind) ell)))
  ... | yes p = yes (usesInputC`⊂∧→∅ y p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂∧→∅ y x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (∧→ ind)} elf lf) (¬∅ s) with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂∧→¬∅c y) = ¬y y
    hf (usesInputC`⊂∧→¬∅¬c y y₁) = ¬y y
  ... | yes y with (isEq (contruct $ add s (∧→ ind) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂∧→¬∅c y {cTo↓ = cTo↓})
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (∧→ ind) ell))
  ... | yes p = yes (usesInputC`⊂∧→¬∅¬c y {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂∧→¬∅c y {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂∧→¬∅¬c y x) = p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = ind ←∨} elf lf) ∅ with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂←∨∅ y y₁) = ¬y y
  ... | yes y with (doesItUseAllInputs` lf (¬∅ (∅-add (ind ←∨) ell)))
  ... | yes p = yes (usesInputC`⊂←∨∅ y p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂←∨∅ y x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (ind ←∨)} elf lf) (¬∅ s) with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂←∨¬∅c y) = ¬y y
    hf (usesInputC`⊂←∨¬∅¬c y y₁) = ¬y y
  ... | yes y with (isEq (contruct $ add s (ind ←∨) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂←∨¬∅c y {cTo↓ = cTo↓}) 
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (ind ←∨) ell))
  ... | yes p = yes (usesInputC`⊂←∨¬∅¬c y {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂←∨¬∅c y {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂←∨¬∅¬c y x) = p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = ∨→ ind} elf lf) ∅ with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂∨→∅ y y₁) = ¬y y
  ... | yes y with (doesItUseAllInputs` lf (¬∅ (∅-add (∨→ ind) ell)))
  ... | yes p = yes (usesInputC`⊂∨→∅ y p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂∨→∅ y x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (∨→ ind)} elf lf) (¬∅ s) with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂∨→¬∅c y) = ¬y y
    hf (usesInputC`⊂∨→¬∅¬c y y₁) = ¬y y
  ... | yes y with (isEq (contruct $ add s (∨→ ind) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂∨→¬∅c y {cTo↓ = cTo↓})
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (∨→ ind) ell))
  ... | yes p = yes (usesInputC`⊂∨→¬∅¬c y {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂∨→¬∅c y {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂∨→¬∅¬c y x) = p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = ind ←∂} elf lf) ∅ with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂←∂∅ y y₁) = ¬y y
  ... | yes y with (doesItUseAllInputs` lf (¬∅ (∅-add (ind ←∂) ell)))
  ... | yes p = yes (usesInputC`⊂←∂∅ y p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂←∂∅ y x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (ind ←∂)} elf lf) (¬∅ s) with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂←∂¬∅c y) = ¬y y
    hf (usesInputC`⊂←∂¬∅¬c y y₁) = ¬y y
  ... | yes y with (isEq (contruct $ add s (ind ←∂) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂←∂¬∅c y {cTo↓ = cTo↓}) 
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (ind ←∂) ell))
  ... | yes p = yes (usesInputC`⊂←∂¬∅¬c y {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂←∂¬∅c y {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂←∂¬∅¬c y x) = p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = ∂→ ind} elf lf) ∅ with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂∂→∅ y y₁) = ¬y y
  ... | yes y with (doesItUseAllInputs` lf (¬∅ (∅-add (∂→ ind) ell)))
  ... | yes p = yes (usesInputC`⊂∂→∅ y p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`⊂∂→∅ y x) = ¬p x
  doesItUseAllInputs` plf@(_⊂_ {ell = ell} {ind = (∂→ ind)} elf lf) (¬∅ s) with (doesItUseAllInputs` elf ∅)
  ... | no ¬y = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂∂→¬∅c y) = ¬y y
    hf (usesInputC`⊂∂→¬∅¬c y y₁) = ¬y y
  ... | yes y with (isEq (contruct $ add s (∂→ ind) ell) ↓)
  ... | yes cTo↓ = yes (usesInputC`⊂∂→¬∅c y {cTo↓ = cTo↓})
  ... | no ¬cTo↓ with (doesItUseAllInputs` lf (¬∅ $ contruct $ add s (∂→ ind) ell))
  ... | yes p = yes (usesInputC`⊂∂→¬∅¬c y {¬cTo↓ = ¬cTo↓} p)
  ... | no p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`⊂∂→¬∅c y {cTo↓ = cTo↓}) = ¬cTo↓ cTo↓
    hf (usesInputC`⊂∂→¬∅¬c y x) = p x
  doesItUseAllInputs` plf@(tr ltr lf) ∅ with (doesItUseAllInputs` lf ∅)
  ... | yes p = yes (usesInputC`tr∅ p)
  ... | no ¬p = no hf where
    hf : usesInputT` plf ∅ → ⊥
    hf (usesInputC`tr∅ x) = ¬p x
  doesItUseAllInputs` plf@(tr ltr lf ) (¬∅ s) with (doesItUseAllInputs` lf $ ¬∅ (SetLL.tran s ltr))
  ... | yes p  = yes (usesInputC`trs p)
  ... | no ¬p  = no hf where
    hf : usesInputT` plf (¬∅ s) → ⊥
    hf (usesInputC`trs x) = ¬p x
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



