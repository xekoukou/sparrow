
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
  ↓c    : ∀{ll ∞rll prf ∞lf} → IndexLFC (call {i} {u} {ll} {∞rll} {prf} ∞lf)
  _←⊂ : ∀{rll pll ell ll ind elf lf}
         → IndexLFC elf
         → IndexLFC (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  ⊂→_ : ∀{rll pll ell ll ind elf lf}
         → IndexLFC lf
         → IndexLFC (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  tr   : ∀{ll orll rll} → {ltr : LLTr orll ll} → {lf : LFun {i} {u} orll rll}
         → IndexLFC lf → IndexLFC (tr ltr lf) 
  com  : ∀{rll ll frll prfi prfo df lf}
         → IndexLFC lf
         → IndexLFC (com {i} {u} {rll} {ll} {frll} {{prfi}} {{prfo}} df lf)



data SetLFC {i u oll orll} (olf : LFun {i} {u} oll orll) : ∀{ll rll} → LFun {i} {u} ll rll → Set (lsuc u) where
  ↓c    : ∀{ll ∞rll prf ∞lf} → IndexLFC olf → SetLFC olf (call {i} {u} {ll} {∞rll} {prf} ∞lf)
  _←⊂ : ∀{rll pll ell ll ind elf lf}
         → SetLFC olf elf
         → SetLFC olf (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  ⊂→_ : ∀{rll pll ell ll ind elf lf}
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

∅-addLFC : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → {lf : LFun {i} {u} ll rll} → IndexLFC olf → IndexLFC lf → SetLFC olf lf 
∅-addLFC oic ↓c = ↓c oic
∅-addLFC oic (ic ←⊂) = (∅-addLFC oic ic) ←⊂
∅-addLFC oic (⊂→ ic) = ⊂→ (∅-addLFC oic ic)
∅-addLFC oic (tr ic) = tr (∅-addLFC oic ic)
∅-addLFC oic (com ic) = com (∅-addLFC oic ic)

addLFC : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → {lf : LFun {i} {u} ll rll} → SetLFC olf lf → IndexLFC olf → IndexLFC lf → SetLFC olf lf 
addLFC (↓c x) oic ↓c = ↓c oic -- replace
addLFC (s ←⊂) oic (ic ←⊂) = (addLFC s oic ic) ←⊂
addLFC (⊂→ s) oic (ic ←⊂) = (∅-addLFC oic ic) ←⊂→ s
addLFC (s ←⊂→ s₁) oic (ic ←⊂) =  (addLFC s oic ic) ←⊂→ s₁
addLFC (s ←⊂) oic (⊂→ ic) = s ←⊂→ (∅-addLFC oic ic)
addLFC (⊂→ s) oic (⊂→ ic) = ⊂→ (addLFC s oic ic)
addLFC (s ←⊂→ s₁) oic (⊂→ ic) = s ←⊂→ (addLFC s₁ oic ic)
addLFC (tr s) oic (tr ic) = tr (addLFC s oic ic)
addLFC (com s) oic (com ic) = com (addLFC s oic ic)


maddLFC : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → {lf : LFun {i} {u} ll rll} → MSetLFC olf lf → IndexLFC olf → IndexLFC lf → MSetLFC olf lf
maddLFC ∅ oic ic = ¬∅ (∅-addLFC oic ic)
maddLFC (¬∅ x) oic ic = ¬∅ (addLFC x oic ic)

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

∅-addLFCRem : ∀{i u ll ∞rll oll orll} → {olf : LFun {i} {u} oll orll} → (ind : IndexLL {i} {u} (call ∞rll) ll) → IndexLFC olf
        → SetLFCRem olf ll
∅-addLFCRem ↓ m = ↓c m
∅-addLFCRem (ind ←∧) m = (∅-addLFCRem ind m) ←∧
∅-addLFCRem (∧→ ind) m = ∧→ (∅-addLFCRem ind m)
∅-addLFCRem (ind ←∨) m = (∅-addLFCRem ind m) ←∨
∅-addLFCRem (∨→ ind) m = ∨→ (∅-addLFCRem ind m)
∅-addLFCRem (ind ←∂) m = (∅-addLFCRem ind m) ←∂
∅-addLFCRem (∂→ ind) m = ∂→ (∅-addLFCRem ind m)

addLFCRem : ∀{i u ll ∞rll oll orll} → {olf : LFun {i} {u} oll orll} → SetLFCRem olf ll → (ind : IndexLL {i} {u} (call ∞rll) ll) → IndexLFC olf
        → SetLFCRem olf ll
addLFCRem (↓c rm) ind m               = ↓c m
addLFCRem (s ←∧) (ind ←∧) m     = (addLFCRem s ind m) ←∧
addLFCRem (s ←∧) (∧→ ind) m     = s ←∧→ (∅-addLFCRem ind m)
addLFCRem (∧→ s) (ind ←∧) m     = (∅-addLFCRem ind m) ←∧→ s
addLFCRem (∧→ s) (∧→ ind) m     = ∧→ addLFCRem s ind m
addLFCRem (s ←∧→ s₁) (ind ←∧) m = (addLFCRem s ind m) ←∧→ s₁
addLFCRem (s ←∧→ s₁) (∧→ ind) m = s ←∧→ (addLFCRem s₁ ind m)
addLFCRem (s ←∨) (ind ←∨) m     = (addLFCRem s ind m) ←∨
addLFCRem (s ←∨) (∨→ ind) m     = s ←∨→ (∅-addLFCRem ind m)
addLFCRem (∨→ s) (ind ←∨) m     = (∅-addLFCRem ind m) ←∨→ s
addLFCRem (∨→ s) (∨→ ind) m     = ∨→ addLFCRem s ind m
addLFCRem (s ←∨→ s₁) (ind ←∨) m = (addLFCRem s ind m) ←∨→ s₁
addLFCRem (s ←∨→ s₁) (∨→ ind) m = s ←∨→ (addLFCRem s₁ ind m)
addLFCRem (s ←∂) (ind ←∂) m     = (addLFCRem s ind m) ←∂
addLFCRem (s ←∂) (∂→ ind) m     = s ←∂→ (∅-addLFCRem ind m)
addLFCRem (∂→ s) (ind ←∂) m     = (∅-addLFCRem ind m) ←∂→ s
addLFCRem (∂→ s) (∂→ ind) m     = ∂→ addLFCRem s ind m
addLFCRem (s ←∂→ s₁) (ind ←∂) m = (addLFCRem s ind m) ←∂→ s₁
addLFCRem (s ←∂→ s₁) (∂→ ind) m = s ←∂→ (addLFCRem s₁ ind m)

madd : ∀{i u ll ∞rll oll orll} → {olf : LFun {i} {u} oll orll} → MSetLFCRem olf ll → (ind : IndexLL {i} {u} (call ∞rll) ll) → IndexLFC olf
      → MSetLFCRem olf ll
madd ∅ ind m = ¬∅ (∅-addLFCRem ind m)
madd (¬∅ x) ind m = ¬∅ (addLFCRem x ind m)


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

tranLFCRem : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → SetLFCRem {i} olf ll → (tr : LLTr {i} {u} rll ll)
       → SetLFCRem olf rll
tranLFCRem s I                           = s
tranLFCRem (s ←∂) (∂c ltr)                = tranLFCRem (∂→ s) ltr
tranLFCRem (∂→ s) (∂c ltr)                = tranLFCRem (s ←∂) ltr
tranLFCRem (s ←∂→ s₁) (∂c ltr)            = tranLFCRem (s₁ ←∂→ s) ltr
tranLFCRem (s ←∨) (∨c ltr)                = tranLFCRem (∨→ s) ltr
tranLFCRem (∨→ s) (∨c ltr)                = tranLFCRem (s ←∨) ltr
tranLFCRem (s ←∨→ s₁) (∨c ltr)            = tranLFCRem (s₁ ←∨→ s) ltr
tranLFCRem (s ←∧) (∧c ltr)                = tranLFCRem (∧→ s) ltr
tranLFCRem (∧→ s) (∧c ltr)                = tranLFCRem (s ←∧) ltr
tranLFCRem (s ←∧→ s₁) (∧c ltr)            = tranLFCRem (s₁ ←∧→ s) ltr
tranLFCRem ((s ←∧) ←∧) (∧∧d ltr)          = tranLFCRem (s ←∧) ltr
tranLFCRem ((∧→ s) ←∧) (∧∧d ltr)          = tranLFCRem (∧→ (s ←∧)) ltr
tranLFCRem ((s ←∧→ s₁) ←∧) (∧∧d ltr)      = tranLFCRem (s ←∧→ (s₁ ←∧)) ltr
tranLFCRem (∧→ s) (∧∧d ltr)               = tranLFCRem (∧→ (∧→ s)) ltr
tranLFCRem ((s ←∧) ←∧→ s₁) (∧∧d ltr)      = tranLFCRem (s ←∧→ (∧→ s₁)) ltr
tranLFCRem ((∧→ s) ←∧→ s₁) (∧∧d ltr)      = tranLFCRem (∧→ (s ←∧→ s₁)) ltr
tranLFCRem ((s ←∧→ s₁) ←∧→ s₂) (∧∧d ltr)  = tranLFCRem (s ←∧→ (s₁ ←∧→ s₂)) ltr
tranLFCRem (s ←∧) (¬∧∧d ltr)              = tranLFCRem ((s ←∧) ←∧) ltr
tranLFCRem (∧→ (s ←∧)) (¬∧∧d ltr)         = tranLFCRem ((∧→ s) ←∧) ltr
tranLFCRem (∧→ (∧→ s)) (¬∧∧d ltr)         = tranLFCRem (∧→ s) ltr
tranLFCRem (∧→ (s ←∧→ s₁)) (¬∧∧d ltr)     = tranLFCRem ((∧→ s) ←∧→ s₁) ltr
tranLFCRem (s ←∧→ (s₁ ←∧)) (¬∧∧d ltr)     = tranLFCRem ((s ←∧→ s₁) ←∧) ltr
tranLFCRem (s ←∧→ (∧→ s₁)) (¬∧∧d ltr)     = tranLFCRem ((s ←∧) ←∧→ s₁) ltr
tranLFCRem (s ←∧→ (s₁ ←∧→ s₂)) (¬∧∧d ltr) = tranLFCRem ((s ←∧→ s₁) ←∧→ s₂) ltr
tranLFCRem ((s ←∨) ←∨) (∨∨d ltr)          = tranLFCRem (s ←∨) ltr
tranLFCRem ((∨→ s) ←∨) (∨∨d ltr)          = tranLFCRem (∨→ (s ←∨)) ltr
tranLFCRem ((s ←∨→ s₁) ←∨) (∨∨d ltr)      = tranLFCRem (s ←∨→ (s₁ ←∨)) ltr
tranLFCRem (∨→ s) (∨∨d ltr)               = tranLFCRem (∨→ (∨→ s)) ltr
tranLFCRem ((s ←∨) ←∨→ s₁) (∨∨d ltr)      = tranLFCRem (s ←∨→ (∨→ s₁)) ltr
tranLFCRem ((∨→ s) ←∨→ s₁) (∨∨d ltr)      = tranLFCRem (∨→ (s ←∨→ s₁)) ltr
tranLFCRem ((s ←∨→ s₁) ←∨→ s₂) (∨∨d ltr)  = tranLFCRem (s ←∨→ (s₁ ←∨→ s₂)) ltr
tranLFCRem (s ←∨) (¬∨∨d ltr)              = tranLFCRem ((s ←∨) ←∨) ltr
tranLFCRem (∨→ (s ←∨)) (¬∨∨d ltr)         = tranLFCRem ((∨→ s) ←∨) ltr
tranLFCRem (∨→ (∨→ s)) (¬∨∨d ltr)         = tranLFCRem (∨→ s) ltr
tranLFCRem (∨→ (s ←∨→ s₁)) (¬∨∨d ltr)     = tranLFCRem ((∨→ s) ←∨→ s₁) ltr
tranLFCRem (s ←∨→ (s₁ ←∨)) (¬∨∨d ltr)     = tranLFCRem ((s ←∨→ s₁) ←∨) ltr
tranLFCRem (s ←∨→ (∨→ s₁)) (¬∨∨d ltr)     = tranLFCRem ((s ←∨) ←∨→ s₁) ltr
tranLFCRem (s ←∨→ (s₁ ←∨→ s₂)) (¬∨∨d ltr) = tranLFCRem ((s ←∨→ s₁) ←∨→ s₂) ltr
tranLFCRem ((s ←∂) ←∂) (∂∂d ltr)          = tranLFCRem (s ←∂) ltr
tranLFCRem ((∂→ s) ←∂) (∂∂d ltr)          = tranLFCRem (∂→ (s ←∂)) ltr
tranLFCRem ((s ←∂→ s₁) ←∂) (∂∂d ltr)      = tranLFCRem (s ←∂→ (s₁ ←∂)) ltr
tranLFCRem (∂→ s) (∂∂d ltr)               = tranLFCRem (∂→ (∂→ s)) ltr
tranLFCRem ((s ←∂) ←∂→ s₁) (∂∂d ltr)      = tranLFCRem (s ←∂→ (∂→ s₁)) ltr
tranLFCRem ((∂→ s) ←∂→ s₁) (∂∂d ltr)      = tranLFCRem (∂→ (s ←∂→ s₁)) ltr
tranLFCRem ((s ←∂→ s₁) ←∂→ s₂) (∂∂d ltr)  = tranLFCRem (s ←∂→ (s₁ ←∂→ s₂)) ltr
tranLFCRem (s ←∂) (¬∂∂d ltr)              = tranLFCRem ((s ←∂) ←∂) ltr
tranLFCRem (∂→ (s ←∂)) (¬∂∂d ltr)         = tranLFCRem ((∂→ s) ←∂) ltr
tranLFCRem (∂→ (∂→ s)) (¬∂∂d ltr)         = tranLFCRem (∂→ s) ltr
tranLFCRem (∂→ (s ←∂→ s₁)) (¬∂∂d ltr)     = tranLFCRem ((∂→ s) ←∂→ s₁) ltr
tranLFCRem (s ←∂→ (s₁ ←∂)) (¬∂∂d ltr)     = tranLFCRem ((s ←∂→ s₁) ←∂) ltr
tranLFCRem (s ←∂→ (∂→ s₁)) (¬∂∂d ltr)     = tranLFCRem ((s ←∂) ←∂→ s₁) ltr
tranLFCRem (s ←∂→ (s₁ ←∂→ s₂)) (¬∂∂d ltr) = tranLFCRem ((s ←∂→ s₁) ←∂→ s₂) ltr


extendLFCRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → IndexLL {i} {u} pll ll → SetLFCRem {i} olf pll → SetLFCRem olf ll
extendLFCRem ↓ sr = sr
extendLFCRem (ind ←∧) sr = (extendLFCRem ind sr) ←∧
extendLFCRem (∧→ ind) sr = ∧→ (extendLFCRem ind sr)
extendLFCRem (ind ←∨) sr = (extendLFCRem ind sr) ←∨
extendLFCRem (∨→ ind) sr = ∨→ (extendLFCRem ind sr)
extendLFCRem (ind ←∂) sr = (extendLFCRem ind sr) ←∂
extendLFCRem (∂→ ind) sr = ∂→ (extendLFCRem ind sr)

replaceLFCRem : ∀{i u oll orll ll pll rll} → {olf : LFun {i} {u} oll orll} → (ind : IndexLL {i} {u} pll ll) → SetLFCRem {i} olf rll → SetLFCRem olf ll → SetLFCRem olf (replLL ll ind rll)
replaceLFCRem ↓ esr sr = esr
replaceLFCRem {rll = rll} (ind ←∧) esr (sr ←∧) = replaceLFCRem ind esr sr ←∧
replaceLFCRem {rll = rll} (ind ←∧) esr (∧→ sr) = (extendLFCRem (updateIndex rll ind) esr) ←∧→ sr
replaceLFCRem {rll = rll} (ind ←∧) esr (sr ←∧→ sr₁) = (replaceLFCRem ind esr sr) ←∧→ sr₁
replaceLFCRem {rll = rll} (∧→ ind) esr (sr ←∧) = sr ←∧→ (extendLFCRem (updateIndex rll ind) esr)
replaceLFCRem {rll = rll} (∧→ ind) esr (∧→ sr) = ∧→ replaceLFCRem ind esr sr
replaceLFCRem {rll = rll} (∧→ ind) esr (sr ←∧→ sr₁) = sr ←∧→ replaceLFCRem ind esr sr₁
replaceLFCRem {rll = rll} (ind ←∨) esr (sr ←∨) = replaceLFCRem ind esr sr ←∨
replaceLFCRem {rll = rll} (ind ←∨) esr (∨→ sr) = (extendLFCRem (updateIndex rll ind) esr) ←∨→ sr
replaceLFCRem {rll = rll} (ind ←∨) esr (sr ←∨→ sr₁) = (replaceLFCRem ind esr sr) ←∨→ sr₁
replaceLFCRem {rll = rll} (∨→ ind) esr (sr ←∨) = sr ←∨→ (extendLFCRem (updateIndex rll ind) esr)
replaceLFCRem {rll = rll} (∨→ ind) esr (∨→ sr) = ∨→ replaceLFCRem ind esr sr
replaceLFCRem {rll = rll} (∨→ ind) esr (sr ←∨→ sr₁) = sr ←∨→ replaceLFCRem ind esr sr₁
replaceLFCRem {rll = rll} (ind ←∂) esr (sr ←∂) = replaceLFCRem ind esr sr ←∂
replaceLFCRem {rll = rll} (ind ←∂) esr (∂→ sr) = (extendLFCRem (updateIndex rll ind) esr) ←∂→ sr
replaceLFCRem {rll = rll} (ind ←∂) esr (sr ←∂→ sr₁) = (replaceLFCRem ind esr sr) ←∂→ sr₁
replaceLFCRem {rll = rll} (∂→ ind) esr (sr ←∂) = sr ←∂→ (extendLFCRem (updateIndex rll ind) esr)
replaceLFCRem {rll = rll} (∂→ ind) esr (∂→ sr) = ∂→ replaceLFCRem ind esr sr
replaceLFCRem {rll = rll} (∂→ ind) esr (sr ←∂→ sr₁) = sr ←∂→ replaceLFCRem ind esr sr₁


mreplaceLFCRem :  ∀{i u oll orll ll pll rll} → {olf : LFun {i} {u} oll orll} → (ind : IndexLL {i} {u} pll ll) → MSetLFCRem {i} olf rll → MSetLFCRem olf ll → MSetLFCRem olf (replLL ll ind rll)
mreplaceLFCRem ind ∅ ∅ = ∅
mreplaceLFCRem {rll = rll} ind ∅ (¬∅ x) = delLFCRem x ind rll
mreplaceLFCRem {rll = rll} ind (¬∅ x) ∅ = ¬∅ (extendLFCRem (updateIndex rll ind) x)
mreplaceLFCRem ind (¬∅ x) (¬∅ x₁) = ¬∅ (replaceLFCRem ind x x₁)

findCallGraph : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → (lf : LFun {i} {u} ll rll) → (IndexLFC lf → IndexLFC olf) → MSetLFCRem olf ll → MSetLFC olf olf → MSetLFCRem olf rll × MSetLFC olf olf
findCallGraph I if msr ms = msr , ms
findCallGraph (_⊂_ {ind = ind} lf lf₁) if msr ms = let emsr , ems = findCallGraph lf (λ x → if (x ←⊂)) (truncSetLFCRem msr ind) ms
                                                in findCallGraph lf₁ (λ x → if (⊂→ x)) (mreplaceLFCRem ind emsr msr) ems 
findCallGraph (tr ltr lf) if ∅ ms = ∅ , ms
findCallGraph (tr ltr lf) if (¬∅ x) ms = findCallGraph lf (λ x → if (tr x)) (¬∅ $ tranLFCRem x ltr) ms
findCallGraph (com df lf) if ∅ ms = findCallGraph lf (λ x → if (com x)) ∅ ms
findCallGraph (com df lf) if (¬∅ x) ms = IMPOSSIBLE
findCallGraph {ll = ll} {rll = call .∞rll} {olf = olf} (call {∞rll = ∞rll} x) if msr ms = ¬∅ (∅-addLFCRem ↓ (if ↓c)) , hf (if ↓c) msr ms where
  hf : ∀{ll} → IndexLFC olf → MSetLFCRem olf ll → MSetLFC olf olf → MSetLFC olf olf
  hf oic ∅ ms = ms
  hf oic (¬∅ (↓c x₁)) ms₁ = maddLFC ms₁ oic x₁ 
  hf oic (¬∅ (x₁ ←∧)) ms₁ = hf oic (¬∅ x₁) ms₁
  hf oic (¬∅ (∧→ x₁)) ms₁ = hf oic (¬∅ x₁) ms₁
  hf oic (¬∅ (x₁ ←∧→ x₂)) ms₁ = hf oic (¬∅ x₁) ms₁
  hf oic (¬∅ (x₁ ←∨)) ms₁ = hf oic (¬∅ x₁) ms₁
  hf oic (¬∅ (∨→ x₁)) ms₁ = hf oic (¬∅ x₁) ms₁
  hf oic (¬∅ (x₁ ←∨→ x₂)) ms₁ = hf oic (¬∅ x₁) ms₁
  hf oic (¬∅ (x₁ ←∂)) ms₁ = hf oic (¬∅ x₁) ms₁
  hf oic (¬∅ (∂→ x₁)) ms₁ = hf oic (¬∅ x₁) ms₁
  hf oic (¬∅ (x₁ ←∂→ x₂)) ms₁ = hf oic (¬∅ x₁) ms₁
