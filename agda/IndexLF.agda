
module IndexLF where

open import Common
open import LinLogic
--open import LinDepT
--open import LinT 
--open import SetLL
--open import SetLLProp
--open import SetLLRem
open import LinFun

open import Data.Product


data IndexLFC {i u} : ∀{ll rll} → LFun {i} {u} ll rll → Set where
  ↓    : ∀{ll rll} → {lf : LFun {i} {u} ll rll} → IndexLFC lf
  _←⊂_ : ∀{rll pll ell ll ind elf lf}
         → IndexLFC elf
         → IndexLFC (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  _⊂→_ : ∀{rll pll ell ll ind elf lf}
         → IndexLFC lf
         → IndexLFC (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  tr   : ∀{ll orll rll} → {ltr : LLTr orll ll} → {lf : LFun {i} {u} orll rll}
         → IndexLFC lf → IndexLFC (tr ltr lf) 
  com  : ∀{rll ll frll prfi prfo df lf}
         → IndexLFC lf
         → IndexLFC (com {i} {u} {rll} {ll} {frll} {{prfi}} {{prfo}} df lf)



data SetLFC {i u oll orll} (olf : LFun {i} {u} oll orll) : ∀{ll rll} → LFun {i} {u} ll rll → Set (lsuc u) where
  ↓    : ∀{ll rll} → {lf : LFun {i} {u} ll rll} → IndexLFC olf → SetLFC olf lf
  _←⊂_ : ∀{rll pll ell ll ind elf lf}
         → SetLFC olf elf
         → SetLFC olf (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  _⊂→_ : ∀{rll pll ell ll ind elf lf}
         → SetLFC olf lf
         → SetLFC olf (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  _←⊂→_ : ∀{rll pll ell ll ind elf lf}
         → SetLFC olf elf
         → SetLFC olf lf
         → SetLFC olf (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  tr   : ∀{ll orll rll} → {ltr : LLTr orll ll} → {lf : LFun {i} {u} orll rll}
         → SetLFC olf lf
         → SetLFC olf (tr ltr lf) 
  com  : ∀{rll ll frll prfi prfo df lf}
         → SetLFC olf lf
         → SetLFC olf (com {i} {u} {rll} {ll} {frll} {{prfi}} {{prfo}} df lf)

data MSetLFC {i u oll orll} (olf : LFun {i} {u} oll orll) : ∀{ll rll} → LFun {i} {u} ll rll → Set (lsuc u) where
  ∅   : ∀{ll rll} → {lf : LFun {i} {u} ll rll}            → MSetLFC olf lf
  ¬∅  : ∀{ll rll} → {lf : LFun {i} {u} ll rll} → SetLFC olf lf → MSetLFC olf lf


data SetLFCRem {i u oll orll} (olf : LFun {i} {u} oll orll) : LinLogic i {u} → Set (lsuc u) where
  ↓c    : ∀{∞ll} → IndexLFC {i} olf                     → SetLFCRem olf (call ∞ll)
  _←∧   : ∀{rs ls} → SetLFCRem olf ls                   → SetLFCRem olf (ls ∧ rs)
  ∧→_   : ∀{rs ls} → SetLFCRem olf rs                   → SetLFCRem olf (ls ∧ rs)
  _←∧→_ : ∀{rs ls} → SetLFCRem olf ls → SetLFCRem olf rs → SetLFCRem olf (ls ∧ rs)
  _←∨   : ∀{rs ls} → SetLFCRem olf ls                   → SetLFCRem olf (ls ∨ rs)
  ∨→_   : ∀{rs ls} → SetLFCRem olf rs                   → SetLFCRem olf (ls ∨ rs)
  _←∨→_ : ∀{rs ls} → SetLFCRem olf ls → SetLFCRem olf rs → SetLFCRem olf (ls ∨ rs)
  _←∂   : ∀{rs ls} → SetLFCRem olf ls                   → SetLFCRem olf (ls ∂ rs)
  ∂→_   : ∀{rs ls} → SetLFCRem olf rs                   → SetLFCRem olf (ls ∂ rs)
  _←∂→_ : ∀{rs ls} → SetLFCRem olf ls → SetLFCRem olf rs → SetLFCRem olf (ls ∂ rs)

data MSetLFCRem {i u oll orll} (olf : LFun {i} {u} oll orll) : LinLogic i {u} → Set (lsuc u) where
  ∅   : ∀{ll}            → MSetLFCRem olf ll
  ¬∅  : ∀{ll} → SetLFCRem olf ll → MSetLFCRem olf ll


truncSetLFCRem : ∀{i} → ∀{u ll oll orll q} → {olf : LFun {i} {u} oll orll} → MSetLFCRem {i} {u} olf ll → (ind : IndexLL {i} {u} q ll) → MSetLFCRem {i} olf q
truncSetLFCRem ∅ ind = ∅
truncSetLFCRem (¬∅ x) ↓ = ¬∅ x
truncSetLFCRem (¬∅ (x ←∧)) (ind ←∧) = truncSetLFCRem (¬∅ x) ind
truncSetLFCRem (¬∅ (∧→ x)) (ind ←∧) = ∅
truncSetLFCRem (¬∅ (x ←∧→ x₁)) (ind ←∧) = truncSetLFCRem (¬∅ x) ind
truncSetLFCRem (¬∅ (x ←∧)) (∧→ ind) = ∅
truncSetLFCRem (¬∅ (∧→ x)) (∧→ ind) =  truncSetLFCRem (¬∅ x) ind
truncSetLFCRem (¬∅ (x ←∧→ x₁)) (∧→ ind) =  truncSetLFCRem (¬∅ x₁) ind
truncSetLFCRem (¬∅ (x ←∨)) (ind ←∨) = truncSetLFCRem (¬∅ x) ind
truncSetLFCRem (¬∅ (∨→ x)) (ind ←∨) = ∅
truncSetLFCRem (¬∅ (x ←∨→ x₁)) (ind ←∨) = truncSetLFCRem (¬∅ x) ind
truncSetLFCRem (¬∅ (x ←∨)) (∨→ ind) = ∅
truncSetLFCRem (¬∅ (∨→ x)) (∨→ ind) =  truncSetLFCRem (¬∅ x) ind
truncSetLFCRem (¬∅ (x ←∨→ x₁)) (∨→ ind) =  truncSetLFCRem (¬∅ x₁) ind
truncSetLFCRem (¬∅ (x ←∂)) (ind ←∂) = truncSetLFCRem (¬∅ x) ind
truncSetLFCRem (¬∅ (∂→ x)) (ind ←∂) = ∅
truncSetLFCRem (¬∅ (x ←∂→ x₁)) (ind ←∂) = truncSetLFCRem (¬∅ x) ind
truncSetLFCRem (¬∅ (x ←∂)) (∂→ ind) = ∅
truncSetLFCRem (¬∅ (∂→ x)) (∂→ ind) =  truncSetLFCRem (¬∅ x) ind
truncSetLFCRem (¬∅ (x ←∂→ x₁)) (∂→ ind) =  truncSetLFCRem (¬∅ x₁) ind

delLFCRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → SetLFCRem {i} olf ll → (ind : IndexLL {i} {u} pll ll) → (rll : LinLogic i)
      → MSetLFCRem {i} olf (replLL ll ind rll)
delLFCRem s ↓ rll = ∅
delLFCRem (s ←∧) (ind ←∧) rll with (delLFCRem s ind rll)
delLFCRem (s ←∧) (ind ←∧) rll | ∅ = ∅
delLFCRem (s ←∧) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧)
delLFCRem (∧→ s) (ind ←∧) rll = ¬∅ (∧→ (s))
delLFCRem (s ←∧→ s₁) (ind ←∧) rll with (delLFCRem s ind rll)
delLFCRem (s ←∧→ s₁) (ind ←∧) rll | ∅ = ¬∅ (∧→ (s₁))
delLFCRem (s ←∧→ s₁) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧→ (s₁))
delLFCRem (s ←∧) (∧→ ind) rll = ¬∅ ((s) ←∧)
delLFCRem (∧→ s) (∧→ ind) rll with (delLFCRem s ind rll)
delLFCRem (∧→ s) (∧→ ind) rll | ∅ = ∅
delLFCRem (∧→ s) (∧→ ind) rll | ¬∅ x = ¬∅ (∧→ x)
delLFCRem (s ←∧→ s₁) (∧→ ind) rll with (delLFCRem s₁ ind rll)
delLFCRem (s ←∧→ s₁) (∧→ ind) rll | ∅ = ¬∅ ((s) ←∧)
delLFCRem (s ←∧→ s₁) (∧→ ind) rll | ¬∅ x = ¬∅ ((s) ←∧→ x)
delLFCRem (s ←∨) (ind ←∨) rll with (delLFCRem s ind rll)
delLFCRem (s ←∨) (ind ←∨) rll | ∅ = ∅
delLFCRem (s ←∨) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨)
delLFCRem (∨→ s) (ind ←∨) rll = ¬∅ (∨→ (s))
delLFCRem (s ←∨→ s₁) (ind ←∨) rll with (delLFCRem s ind rll)
delLFCRem (s ←∨→ s₁) (ind ←∨) rll | ∅ = ¬∅ (∨→ (s₁))
delLFCRem (s ←∨→ s₁) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨→ (s₁))
delLFCRem (s ←∨) (∨→ ind) rll = ¬∅ ((s) ←∨)
delLFCRem (∨→ s) (∨→ ind) rll with (delLFCRem s ind rll)
delLFCRem (∨→ s) (∨→ ind) rll | ∅ = ∅
delLFCRem (∨→ s) (∨→ ind) rll | ¬∅ x = ¬∅ (∨→ x)
delLFCRem (s ←∨→ s₁) (∨→ ind) rll with (delLFCRem s₁ ind rll)
delLFCRem (s ←∨→ s₁) (∨→ ind) rll | ∅ = ¬∅ ((s) ←∨)
delLFCRem (s ←∨→ s₁) (∨→ ind) rll | ¬∅ x = ¬∅ ((s) ←∨→ x)
delLFCRem (s ←∂) (ind ←∂) rll with (delLFCRem s ind rll)
delLFCRem (s ←∂) (ind ←∂) rll | ∅ = ∅
delLFCRem (s ←∂) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂)
delLFCRem (∂→ s) (ind ←∂) rll = ¬∅ (∂→ (s))
delLFCRem (s ←∂→ s₁) (ind ←∂) rll with (delLFCRem s ind rll)
delLFCRem (s ←∂→ s₁) (ind ←∂) rll | ∅ = ¬∅ (∂→ (s₁))
delLFCRem (s ←∂→ s₁) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂→ (s₁))
delLFCRem (s ←∂) (∂→ ind) rll = ¬∅ ((s) ←∂)
delLFCRem (∂→ s) (∂→ ind) rll with (delLFCRem s ind rll)
delLFCRem (∂→ s) (∂→ ind) rll | ∅ = ∅
delLFCRem (∂→ s) (∂→ ind) rll | ¬∅ x = ¬∅ (∂→ x)
delLFCRem (s ←∂→ s₁) (∂→ ind) rll with (delLFCRem s₁ ind rll)
delLFCRem (s ←∂→ s₁) (∂→ ind) rll | ∅ = ¬∅ ((s) ←∂)
delLFCRem (s ←∂→ s₁) (∂→ ind) rll | ¬∅ x = ¬∅ ((s) ←∂→ x)

mdelLFCRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → MSetLFCRem {i} olf ll → (ind : IndexLL {i} {u} pll ll) → (rll : LinLogic i)
             → MSetLFCRem {i} olf (replLL ll ind rll)
mdelLFCRem ∅ ind rll = ∅
mdelLFCRem (¬∅ x) ind rll = delLFCRem x ind rll



mreplaceLFCRem :  ∀{i u oll orll ll pll rll} → {olf : LFun {i} {u} oll orll} → (ind : IndexLL {i} {u} pll ll) → MSetLFCRem {i} olf rll → MSetLFCRem olf ll → MSetLFCRem olf (replLL ll ind rll)
mreplaceLFCRem ind ∅ ∅ = ∅
mreplaceLFCRem ind ∅ (¬∅ x) = {!!}
mreplaceLFCRem ind (¬∅ x) ms = {!!}


findCallGraph : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → (lf : LFun {i} {u} ll rll) → MSetLFCRem olf ll → MSetLFC olf olf → MSetLFCRem olf rll × MSetLFC olf olf
findCallGraph I msr ms = msr , ms
findCallGraph (_⊂_ {ind = ind} lf lf₁) msr ms = let emsr , ems = findCallGraph lf (truncSetLFCRem msr ind) ms
                                                in {!!} 
findCallGraph (tr ltr lf) msr ms = {!!}
findCallGraph (com df lf) msr ms = {!!}
findCallGraph (call x) msr ms = {!!}
