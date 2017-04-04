
module IndexLF where

open import Common
open import IndexLLProp
open import LinLogic
open import LinFun

open import Data.Product
open import Data.Unit



data IndexLF {i u} : ∀{ll rll} → LFun {i} {u} ll rll → Set where
  ↓    : ∀{ll rll} → {lf : LFun ll rll} → IndexLF lf
  _←⊂ : ∀{rll pll ell ll ind elf lf}
         → IndexLF elf
         → IndexLF (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  ⊂→_ : ∀{rll pll ell ll ind elf lf}
         → IndexLF lf
         → IndexLF (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  tr   : ∀{ll orll rll} → {ltr : LLTr orll ll} → {lf : LFun {i} {u} orll rll}
         → IndexLF lf → IndexLF (tr ltr lf) 
  com  : ∀{rll ll frll prfi prfo df lf}
         → IndexLF lf
         → IndexLF (com {i} {u} {rll} {ll} {frll} {{prfi}} {{prfo}} df lf)


lastCom : ∀{i u ll rll} → {lf : LFun {i} {u} ll rll} → IndexLF lf → Set
lastCom {lf      = I} ↓ = ⊥
lastCom {lf      = lf ⊂ lf₁} ↓ = ⊥
lastCom {lf      = tr ltr lf} ↓ = ⊥
lastCom {lf      = com df lf} ↓ = ⊤
lastCom {lf      = call x} ↓ = ⊥
lastCom (ic ←⊂)  = lastCom ic
lastCom (⊂→ ic)  = lastCom ic
lastCom (tr ic)  = lastCom ic
lastCom (com ic) = lastCom ic

lastCall : ∀{i u ll rll} → {lf : LFun {i} {u} ll rll} → IndexLF lf → Set
lastCall {lf      = I} ↓ = ⊥
lastCall {lf      = lf ⊂ lf₁} ↓ = ⊥
lastCall {lf      = tr ltr lf} ↓ = ⊥
lastCall {lf      = com df lf} ↓ = ⊥
lastCall {lf      = call x} ↓ = ⊤ 
lastCall (ic ←⊂)  = lastCall ic
lastCall (⊂→ ic)  = lastCall ic
lastCall (tr ic)  = lastCall ic
lastCall (com ic) = lastCall ic

-- To be removed since we will probably not need it anymore.  
--module _ {u : Level} where
--
--  open import SetLL
--  open import Data.Maybe
--  open import Category.Monad
--  open RawMonad {f = lsuc u} (monad)
--  open import Relation.Binary.PropositionalEquality 
--
--  private
--    hf : ∀{i u ll pll ell} → (ind : IndexLL {i} {u} pll ll) → (s : SetLL (replLL ll ind ell)) → (elf : LFun pll ell) → Maybe $ Σ (SetLL ll) (λ x → just x ≡ setRevNoComs ind s elf)
--    hf ind s elf with (setRevNoComs ind s elf)
--    hf ind s elf | just x = just (x , refl)
--    hf ind s elf | nothing = nothing
--
--    hf2 : ∀ {i u ll rll} → (s : SetLL rll) → (ltr : LLTr {i} {u} rll ll) → Σ (SetLL ll) (λ rs → rs ≡ tran s (revTr ltr))
--    hf2 s ltr with (tran s (revTr ltr))
--    ... | r = r , refl
--    
--  indLFtoLFCo : ∀{i ll rll} → {lf : LFun {i} {u} ll rll} → IndexLF lf → Maybe $ Σ (LinLogic i {u}) ( λ  cll → Σ (LinLogic i {u}) (λ frll → Σ (SetLL ll) (λ s → IndexLFCo {i = i} {u = u} cll frll s lf)))
--  indLFtoLFCo {lf = I} ↓ = nothing
--  indLFtoLFCo {lf = lf ⊂ lf₁} ↓ = nothing
--  indLFtoLFCo {lf = tr ltr lf} ↓ = nothing
--  indLFtoLFCo {lf = com {ll = cll} {frll = frll} df lf} ↓ = just (cll , frll , ↓ , ↓)
--  indLFtoLFCo {lf = call x} ↓ = nothing
--  indLFtoLFCo (_←⊂ {ind = ind} ic) = (indLFtoLFCo ic) >>= (λ {(cll , frll , s , x) → just (cll , frll , extend ind s , (x ←⊂))}) 
--  indLFtoLFCo (⊂→_ {ind = ind} {elf = elf} ic) with (indLFtoLFCo ic)
--  indLFtoLFCo (⊂→_ {_} {_} {_} {_} {ind} {elf} ic) | nothing = nothing
--  indLFtoLFCo (⊂→_ {_} {_} {_} {_} {ind} {elf} ic) | just (cll , frll , s , x) with (hf ind s elf)
--  indLFtoLFCo (⊂→_ {_} {_} {_} {_} {ind} {elf} ic) | just (cll , frll , s , x) | (just (rs , prf)) = just (cll , frll , rs , (⊂→_ x {prf = prf}))
--  indLFtoLFCo (⊂→_ {_} {_} {_} {_} {ind} {elf} ic) | just (cll , frll , s , x) | nothing = nothing
--  indLFtoLFCo (tr {ltr = ltr} ic) with (indLFtoLFCo ic)
--  ... | nothing = nothing
--  ... | just (cll , frll , s , x) with (hf2 s ltr)
--  indLFtoLFCo (tr {_} {_} {_} {ltr} ic) | just (cll , frll , s , x) | ( rs , prf) = just (cll , frll , rs , (tr x {prf = prf}))
--  indLFtoLFCo (com ic) = nothing 



data SetLF {i u oll orll} (olf : LFun {i} {u} oll orll) : ∀{ll rll} → LFun {i} {u} ll rll → Set (lsuc u) where
  ↓    : ∀{ll rll} → {lf : LFun ll rll} → IndexLF olf → SetLF olf lf
  _←⊂ : ∀{rll pll ell ll ind elf lf}
         → SetLF olf elf
         → SetLF olf (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  ⊂→_ : ∀{rll pll ell ll ind elf lf}
         → SetLF olf lf
         → SetLF olf (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  _←⊂→_ : ∀{rll pll ell ll ind elf lf}
         → SetLF olf elf
         → SetLF olf lf
         → SetLF olf (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  tr   : ∀{ll orll rll} → {ltr : LLTr orll ll} → {lf : LFun {i} {u} orll rll}
         → SetLF olf lf
         → SetLF olf (tr ltr lf) 
  com  : ∀{rll ll frll prfi prfo df lf}
         → SetLF olf lf
         → SetLF olf (com {i} {u} {rll} {ll} {frll} {{prfi}} {{prfo}} df lf)

data MSetLF {i u oll orll} (olf : LFun {i} {u} oll orll) : ∀{ll rll} → LFun {i} {u} ll rll → Set (lsuc u) where
  ∅   : ∀{ll rll} → {lf : LFun {i} {u} ll rll}            → MSetLF olf lf
  ¬∅  : ∀{ll rll} → {lf : LFun {i} {u} ll rll} → SetLF olf lf → MSetLF olf lf

∅-addLF : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → {lf : LFun {i} {u} ll rll} → IndexLF olf → IndexLF lf → SetLF olf lf 
∅-addLF oic ↓ = ↓ oic
∅-addLF oic (ic ←⊂) = (∅-addLF oic ic) ←⊂
∅-addLF oic (⊂→ ic) = ⊂→ (∅-addLF oic ic)
∅-addLF oic (tr ic) = tr (∅-addLF oic ic)
∅-addLF oic (com ic) = com (∅-addLF oic ic)

addLF : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → {lf : LFun {i} {u} ll rll} → SetLF olf lf → IndexLF olf → IndexLF lf → SetLF olf lf 
addLF (↓ x) oic ↓            = ↓ oic -- We replace the previous info
addLF (s ←⊂) oic ↓           = ↓ oic -- We replace the previous info
addLF (⊂→ s) oic ↓           = ↓ oic -- We replace the previous info
addLF (s ←⊂→ s₁) oic ↓       = ↓ oic -- We replace the previous info
addLF (tr s) oic ↓           = ↓ oic -- We replace the previous info
addLF (com s) oic ↓          = ↓ oic -- We replace the previous info
addLF (↓ x) oic (com ic)     =  com (∅-addLF oic ic) -- We replace the previous info
addLF (↓ x) oic (ic ←⊂)      = (∅-addLF oic ic) ←⊂ -- We replace the previous info
addLF (s ←⊂) oic (ic ←⊂)     = (addLF s oic ic) ←⊂
addLF (⊂→ s) oic (ic ←⊂)     = (∅-addLF oic ic) ←⊂→ s
addLF (s ←⊂→ s₁) oic (ic ←⊂) =  (addLF s oic ic) ←⊂→ s₁
addLF (↓ x) oic (⊂→ ic)      = ⊂→ (∅-addLF oic ic) -- We replace the previous info
addLF (s ←⊂) oic (⊂→ ic)     = s ←⊂→ (∅-addLF oic ic)
addLF (⊂→ s) oic (⊂→ ic)     = ⊂→ (addLF s oic ic)
addLF (s ←⊂→ s₁) oic (⊂→ ic) = s ←⊂→ (addLF s₁ oic ic)
addLF (↓ x) oic (tr ic)      = tr (∅-addLF oic ic) -- We replace the previous info
addLF (tr s) oic (tr ic)     = tr (addLF s oic ic)
addLF (com s) oic (com ic)   = com (addLF s oic ic)


maddLF : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → {lf : LFun {i} {u} ll rll} → MSetLF olf lf → IndexLF olf → IndexLF lf → MSetLF olf lf
maddLF ∅ oic ic = ¬∅ (∅-addLF oic ic)
maddLF (¬∅ x) oic ic = ¬∅ (addLF x oic ic)

data SetLFRem {i u oll orll} (olf : LFun {i} {u} oll orll) : LinLogic i {u} → Set (lsuc u) where
  ↓    : ∀{ll} → IndexLF {i} olf                     → SetLFRem olf ll
  _←∧   : ∀{rs ls} → SetLFRem olf ls                   → SetLFRem olf (ls ∧ rs)
  ∧→_   : ∀{rs ls} → SetLFRem olf rs                   → SetLFRem olf (ls ∧ rs)
  _←∧→_ : ∀{rs ls} → SetLFRem olf ls → SetLFRem olf rs → SetLFRem olf (ls ∧ rs)
  _←∨   : ∀{rs ls} → SetLFRem olf ls                   → SetLFRem olf (ls ∨ rs)
  ∨→_   : ∀{rs ls} → SetLFRem olf rs                   → SetLFRem olf (ls ∨ rs)
  _←∨→_ : ∀{rs ls} → SetLFRem olf ls → SetLFRem olf rs → SetLFRem olf (ls ∨ rs)
  _←∂   : ∀{rs ls} → SetLFRem olf ls                   → SetLFRem olf (ls ∂ rs)
  ∂→_   : ∀{rs ls} → SetLFRem olf rs                   → SetLFRem olf (ls ∂ rs)
  _←∂→_ : ∀{rs ls} → SetLFRem olf ls → SetLFRem olf rs → SetLFRem olf (ls ∂ rs)

data MSetLFRem {i u oll orll} (olf : LFun {i} {u} oll orll) : LinLogic i {u} → Set (lsuc u) where
  ∅   : ∀{ll}            → MSetLFRem olf ll
  ¬∅  : ∀{ll} → SetLFRem olf ll → MSetLFRem olf ll

∅-addLFRem : ∀{i u ll pll oll orll} → {olf : LFun {i} {u} oll orll} → (ind : IndexLL {i} {u} pll ll) → IndexLF olf
        → SetLFRem olf ll
∅-addLFRem ↓ m = ↓ m
∅-addLFRem (ind ←∧) m = (∅-addLFRem ind m) ←∧
∅-addLFRem (∧→ ind) m = ∧→ (∅-addLFRem ind m)
∅-addLFRem (ind ←∨) m = (∅-addLFRem ind m) ←∨
∅-addLFRem (∨→ ind) m = ∨→ (∅-addLFRem ind m)
∅-addLFRem (ind ←∂) m = (∅-addLFRem ind m) ←∂
∅-addLFRem (∂→ ind) m = ∂→ (∅-addLFRem ind m)

addLFRem : ∀{i u ll pll oll orll} → {olf : LFun {i} {u} oll orll} → SetLFRem olf ll → (ind : IndexLL {i} {u} pll ll) → IndexLF olf
        → SetLFRem olf ll
addLFRem (↓ rm) ind m          = ↓ m
addLFRem (x ←∧) ↓ m            = ↓ m
addLFRem (∧→ x) ↓ m            = ↓ m --TODO Here we lose the information that is at lower levels.
addLFRem (x ←∧→ x₁) ↓ m        = ↓ m
addLFRem (x ←∨) ↓ m            = ↓ m
addLFRem (∨→ x) ↓ m            = ↓ m
addLFRem (x ←∨→ x₁) ↓ m        = ↓ m
addLFRem (x ←∂) ↓ m            = ↓ m
addLFRem (∂→ x) ↓ m            = ↓ m
addLFRem (x ←∂→ x₁) ↓ m        = ↓ m
addLFRem (s ←∧) (ind ←∧) m     = (addLFRem s ind m) ←∧
addLFRem (s ←∧) (∧→ ind) m     = s ←∧→ (∅-addLFRem ind m)
addLFRem (∧→ s) (ind ←∧) m     = (∅-addLFRem ind m) ←∧→ s
addLFRem (∧→ s) (∧→ ind) m     = ∧→ addLFRem s ind m
addLFRem (s ←∧→ s₁) (ind ←∧) m = (addLFRem s ind m) ←∧→ s₁
addLFRem (s ←∧→ s₁) (∧→ ind) m = s ←∧→ (addLFRem s₁ ind m)
addLFRem (s ←∨) (ind ←∨) m     = (addLFRem s ind m) ←∨
addLFRem (s ←∨) (∨→ ind) m     = s ←∨→ (∅-addLFRem ind m)
addLFRem (∨→ s) (ind ←∨) m     = (∅-addLFRem ind m) ←∨→ s
addLFRem (∨→ s) (∨→ ind) m     = ∨→ addLFRem s ind m
addLFRem (s ←∨→ s₁) (ind ←∨) m = (addLFRem s ind m) ←∨→ s₁
addLFRem (s ←∨→ s₁) (∨→ ind) m = s ←∨→ (addLFRem s₁ ind m)
addLFRem (s ←∂) (ind ←∂) m     = (addLFRem s ind m) ←∂
addLFRem (s ←∂) (∂→ ind) m     = s ←∂→ (∅-addLFRem ind m)
addLFRem (∂→ s) (ind ←∂) m     = (∅-addLFRem ind m) ←∂→ s
addLFRem (∂→ s) (∂→ ind) m     = ∂→ addLFRem s ind m
addLFRem (s ←∂→ s₁) (ind ←∂) m = (addLFRem s ind m) ←∂→ s₁
addLFRem (s ←∂→ s₁) (∂→ ind) m = s ←∂→ (addLFRem s₁ ind m)

maddLFRem : ∀{i u ll pll oll orll} → {olf : LFun {i} {u} oll orll} → MSetLFRem olf ll → (ind : IndexLL {i} {u} pll ll) → IndexLF olf
      → MSetLFRem olf ll
maddLFRem ∅ ind m = ¬∅ (∅-addLFRem ind m)
maddLFRem (¬∅ x) ind m = ¬∅ (addLFRem x ind m)


truncSetLFRem : ∀{i} → ∀{u ll oll orll q} → {olf : LFun {i} {u} oll orll} → MSetLFRem {i} {u} olf ll → (ind : IndexLL {i} {u} q ll) → MSetLFRem {i} olf q
truncSetLFRem ∅ ind = ∅
truncSetLFRem (¬∅ x) ↓ = ¬∅ x
truncSetLFRem (¬∅ (↓ x)) (ind ←∧) = ∅
truncSetLFRem (¬∅ (x ←∧)) (ind ←∧) = truncSetLFRem (¬∅ x) ind
truncSetLFRem (¬∅ (∧→ x)) (ind ←∧) = ∅
truncSetLFRem (¬∅ (x ←∧→ x₁)) (ind ←∧) = truncSetLFRem (¬∅ x) ind
truncSetLFRem (¬∅ (↓ x)) (∧→ ind) = ∅
truncSetLFRem (¬∅ (x ←∧)) (∧→ ind) = ∅
truncSetLFRem (¬∅ (∧→ x)) (∧→ ind) =  truncSetLFRem (¬∅ x) ind
truncSetLFRem (¬∅ (x ←∧→ x₁)) (∧→ ind) =  truncSetLFRem (¬∅ x₁) ind
truncSetLFRem (¬∅ (↓ x)) (ind ←∨) = ∅
truncSetLFRem (¬∅ (x ←∨)) (ind ←∨) = truncSetLFRem (¬∅ x) ind
truncSetLFRem (¬∅ (∨→ x)) (ind ←∨) = ∅
truncSetLFRem (¬∅ (x ←∨→ x₁)) (ind ←∨) = truncSetLFRem (¬∅ x) ind
truncSetLFRem (¬∅ (↓ x)) (∨→ ind) = ∅
truncSetLFRem (¬∅ (x ←∨)) (∨→ ind) = ∅
truncSetLFRem (¬∅ (∨→ x)) (∨→ ind) =  truncSetLFRem (¬∅ x) ind
truncSetLFRem (¬∅ (x ←∨→ x₁)) (∨→ ind) =  truncSetLFRem (¬∅ x₁) ind
truncSetLFRem (¬∅ (↓ x)) (ind ←∂) = ∅
truncSetLFRem (¬∅ (x ←∂)) (ind ←∂) = truncSetLFRem (¬∅ x) ind
truncSetLFRem (¬∅ (∂→ x)) (ind ←∂) = ∅
truncSetLFRem (¬∅ (x ←∂→ x₁)) (ind ←∂) = truncSetLFRem (¬∅ x) ind
truncSetLFRem (¬∅ (↓ x)) (∂→ ind) = ∅
truncSetLFRem (¬∅ (x ←∂)) (∂→ ind) = ∅
truncSetLFRem (¬∅ (∂→ x)) (∂→ ind) =  truncSetLFRem (¬∅ x) ind
truncSetLFRem (¬∅ (x ←∂→ x₁)) (∂→ ind) =  truncSetLFRem (¬∅ x₁) ind

delLFRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → SetLFRem {i} olf ll → (ind : IndexLL {i} {u} pll ll) → (rll : LinLogic i)
      → MSetLFRem {i} olf (replLL ll ind rll)
delLFRem s ↓ rll = ∅
delLFRem (↓ x) (ind ←∧) rll = ∅ -- We loose Information.
delLFRem (s ←∧) (ind ←∧) rll with (delLFRem s ind rll)
delLFRem (s ←∧) (ind ←∧) rll | ∅ = ∅
delLFRem (s ←∧) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧)
delLFRem (∧→ s) (ind ←∧) rll = ¬∅ (∧→ (s))
delLFRem (s ←∧→ s₁) (ind ←∧) rll with (delLFRem s ind rll)
delLFRem (s ←∧→ s₁) (ind ←∧) rll | ∅ = ¬∅ (∧→ (s₁))
delLFRem (s ←∧→ s₁) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧→ (s₁))
delLFRem (↓ x) (∧→ ind) rll = ∅ --
delLFRem (s ←∧) (∧→ ind) rll = ¬∅ ((s) ←∧)
delLFRem (∧→ s) (∧→ ind) rll with (delLFRem s ind rll)
delLFRem (∧→ s) (∧→ ind) rll | ∅ = ∅
delLFRem (∧→ s) (∧→ ind) rll | ¬∅ x = ¬∅ (∧→ x)
delLFRem (s ←∧→ s₁) (∧→ ind) rll with (delLFRem s₁ ind rll)
delLFRem (s ←∧→ s₁) (∧→ ind) rll | ∅ = ¬∅ ((s) ←∧)
delLFRem (s ←∧→ s₁) (∧→ ind) rll | ¬∅ x = ¬∅ ((s) ←∧→ x)
delLFRem (↓ x) (ind ←∨) rll = ∅
delLFRem (s ←∨) (ind ←∨) rll with (delLFRem s ind rll)
delLFRem (s ←∨) (ind ←∨) rll | ∅ = ∅
delLFRem (s ←∨) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨)
delLFRem (∨→ s) (ind ←∨) rll = ¬∅ (∨→ (s))
delLFRem (s ←∨→ s₁) (ind ←∨) rll with (delLFRem s ind rll)
delLFRem (s ←∨→ s₁) (ind ←∨) rll | ∅ = ¬∅ (∨→ (s₁))
delLFRem (s ←∨→ s₁) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨→ (s₁))
delLFRem (↓ x) (∨→ ind) rll = ∅
delLFRem (s ←∨) (∨→ ind) rll = ¬∅ ((s) ←∨)
delLFRem (∨→ s) (∨→ ind) rll with (delLFRem s ind rll)
delLFRem (∨→ s) (∨→ ind) rll | ∅ = ∅
delLFRem (∨→ s) (∨→ ind) rll | ¬∅ x = ¬∅ (∨→ x)
delLFRem (s ←∨→ s₁) (∨→ ind) rll with (delLFRem s₁ ind rll)
delLFRem (s ←∨→ s₁) (∨→ ind) rll | ∅ = ¬∅ ((s) ←∨)
delLFRem (s ←∨→ s₁) (∨→ ind) rll | ¬∅ x = ¬∅ ((s) ←∨→ x)
delLFRem (↓ x) (ind ←∂) rll = ∅
delLFRem (s ←∂) (ind ←∂) rll with (delLFRem s ind rll)
delLFRem (s ←∂) (ind ←∂) rll | ∅ = ∅
delLFRem (s ←∂) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂)
delLFRem (∂→ s) (ind ←∂) rll = ¬∅ (∂→ (s))
delLFRem (s ←∂→ s₁) (ind ←∂) rll with (delLFRem s ind rll)
delLFRem (s ←∂→ s₁) (ind ←∂) rll | ∅ = ¬∅ (∂→ (s₁))
delLFRem (s ←∂→ s₁) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂→ (s₁))
delLFRem (↓ x) (∂→ ind) rll = ∅
delLFRem (s ←∂) (∂→ ind) rll = ¬∅ ((s) ←∂)
delLFRem (∂→ s) (∂→ ind) rll with (delLFRem s ind rll)
delLFRem (∂→ s) (∂→ ind) rll | ∅ = ∅
delLFRem (∂→ s) (∂→ ind) rll | ¬∅ x = ¬∅ (∂→ x)
delLFRem (s ←∂→ s₁) (∂→ ind) rll with (delLFRem s₁ ind rll)
delLFRem (s ←∂→ s₁) (∂→ ind) rll | ∅ = ¬∅ ((s) ←∂)
delLFRem (s ←∂→ s₁) (∂→ ind) rll | ¬∅ x = ¬∅ ((s) ←∂→ x)

mdelLFRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → MSetLFRem {i} olf ll → (ind : IndexLL {i} {u} pll ll) → (rll : LinLogic i)
             → MSetLFRem {i} olf (replLL ll ind rll)
mdelLFRem ∅ ind rll = ∅
mdelLFRem (¬∅ x) ind rll = delLFRem x ind rll

tranLFRem : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → SetLFRem {i} olf ll → (tr : LLTr {i} {u} rll ll)
       → SetLFRem olf rll
tranLFRem s I                           = s
tranLFRem (s ←∂) (∂c ltr)                = tranLFRem (∂→ s) ltr
tranLFRem (↓ x) (∂c ltr)                = ↓ x
tranLFRem (∂→ s) (∂c ltr)                = tranLFRem (s ←∂) ltr
tranLFRem (s ←∂→ s₁) (∂c ltr)            = tranLFRem (s₁ ←∂→ s) ltr
tranLFRem (s ←∨) (∨c ltr)                = tranLFRem (∨→ s) ltr
tranLFRem (↓ x) (∨c ltr)                = ↓ x
tranLFRem (∨→ s) (∨c ltr)                = tranLFRem (s ←∨) ltr
tranLFRem (s ←∨→ s₁) (∨c ltr)            = tranLFRem (s₁ ←∨→ s) ltr
tranLFRem (s ←∧) (∧c ltr)                = tranLFRem (∧→ s) ltr
tranLFRem (↓ x) (∧c ltr)                = ↓ x
tranLFRem (∧→ s) (∧c ltr)                = tranLFRem (s ←∧) ltr
tranLFRem (s ←∧→ s₁) (∧c ltr)            = tranLFRem (s₁ ←∧→ s) ltr
tranLFRem ((s ←∧) ←∧) (∧∧d ltr)          = tranLFRem (s ←∧) ltr
tranLFRem (↓ x) (∧∧d ltr)          = ↓ x
tranLFRem ((↓ x) ←∧) (∧∧d ltr)          = tranLFRem ((↓ x) ←∧→ ((↓ x) ←∧)) ltr
tranLFRem ((∧→ s) ←∧) (∧∧d ltr)          = tranLFRem (∧→ (s ←∧)) ltr
tranLFRem ((s ←∧→ s₁) ←∧) (∧∧d ltr)      = tranLFRem (s ←∧→ (s₁ ←∧)) ltr
tranLFRem (∧→ s) (∧∧d ltr)               = tranLFRem (∧→ (∧→ s)) ltr
tranLFRem ((↓ x) ←∧→ s₁) (∧∧d ltr)      = tranLFRem ((↓ x) ←∧→ ((↓ x) ←∧→ s₁)) ltr
tranLFRem ((s ←∧) ←∧→ s₁) (∧∧d ltr)      = tranLFRem (s ←∧→ (∧→ s₁)) ltr
tranLFRem ((∧→ s) ←∧→ s₁) (∧∧d ltr)      = tranLFRem (∧→ (s ←∧→ s₁)) ltr
tranLFRem ((s ←∧→ s₁) ←∧→ s₂) (∧∧d ltr)  = tranLFRem (s ←∧→ (s₁ ←∧→ s₂)) ltr
tranLFRem (s ←∧) (¬∧∧d ltr)              = tranLFRem ((s ←∧) ←∧) ltr
tranLFRem (↓ x) (¬∧∧d ltr)              = ↓ x
tranLFRem (∧→ (↓ x)) (¬∧∧d ltr)         = tranLFRem ((∧→ (↓ x)) ←∧→ (↓ x)) ltr
tranLFRem (∧→ (s ←∧)) (¬∧∧d ltr)         = tranLFRem ((∧→ s) ←∧) ltr
tranLFRem (∧→ (∧→ s)) (¬∧∧d ltr)         = tranLFRem (∧→ s) ltr
tranLFRem (∧→ (s ←∧→ s₁)) (¬∧∧d ltr)     = tranLFRem ((∧→ s) ←∧→ s₁) ltr
tranLFRem (s ←∧→ (↓ x)) (¬∧∧d ltr)     = tranLFRem ((s ←∧→ (↓ x)) ←∧→ (↓ x)) ltr
tranLFRem (s ←∧→ (s₁ ←∧)) (¬∧∧d ltr)     = tranLFRem ((s ←∧→ s₁) ←∧) ltr
tranLFRem (s ←∧→ (∧→ s₁)) (¬∧∧d ltr)     = tranLFRem ((s ←∧) ←∧→ s₁) ltr
tranLFRem (s ←∧→ (s₁ ←∧→ s₂)) (¬∧∧d ltr) = tranLFRem ((s ←∧→ s₁) ←∧→ s₂) ltr
tranLFRem ((s ←∨) ←∨) (∨∨d ltr)          = tranLFRem (s ←∨) ltr
tranLFRem (↓ x) (∨∨d ltr)          = ↓ x
tranLFRem ((↓ x) ←∨) (∨∨d ltr)          = tranLFRem ((↓ x) ←∨→ ((↓ x) ←∨)) ltr
tranLFRem ((∨→ s) ←∨) (∨∨d ltr)          = tranLFRem (∨→ (s ←∨)) ltr
tranLFRem ((s ←∨→ s₁) ←∨) (∨∨d ltr)      = tranLFRem (s ←∨→ (s₁ ←∨)) ltr
tranLFRem (∨→ s) (∨∨d ltr)               = tranLFRem (∨→ (∨→ s)) ltr
tranLFRem ((↓ x) ←∨→ s₁) (∨∨d ltr)      = tranLFRem ((↓ x) ←∨→ ((↓ x) ←∨→ s₁)) ltr
tranLFRem ((s ←∨) ←∨→ s₁) (∨∨d ltr)      = tranLFRem (s ←∨→ (∨→ s₁)) ltr
tranLFRem ((∨→ s) ←∨→ s₁) (∨∨d ltr)      = tranLFRem (∨→ (s ←∨→ s₁)) ltr
tranLFRem ((s ←∨→ s₁) ←∨→ s₂) (∨∨d ltr)  = tranLFRem (s ←∨→ (s₁ ←∨→ s₂)) ltr
tranLFRem (s ←∨) (¬∨∨d ltr)              = tranLFRem ((s ←∨) ←∨) ltr
tranLFRem (↓ x) (¬∨∨d ltr)              = ↓ x
tranLFRem (∨→ (↓ x)) (¬∨∨d ltr)         = tranLFRem ((∨→ (↓ x)) ←∨→ (↓ x)) ltr
tranLFRem (∨→ (s ←∨)) (¬∨∨d ltr)         = tranLFRem ((∨→ s) ←∨) ltr
tranLFRem (∨→ (∨→ s)) (¬∨∨d ltr)         = tranLFRem (∨→ s) ltr
tranLFRem (∨→ (s ←∨→ s₁)) (¬∨∨d ltr)     = tranLFRem ((∨→ s) ←∨→ s₁) ltr
tranLFRem (s ←∨→ (↓ x)) (¬∨∨d ltr)     = tranLFRem ((s ←∨→ (↓ x)) ←∨→ (↓ x)) ltr
tranLFRem (s ←∨→ (s₁ ←∨)) (¬∨∨d ltr)     = tranLFRem ((s ←∨→ s₁) ←∨) ltr
tranLFRem (s ←∨→ (∨→ s₁)) (¬∨∨d ltr)     = tranLFRem ((s ←∨) ←∨→ s₁) ltr
tranLFRem (s ←∨→ (s₁ ←∨→ s₂)) (¬∨∨d ltr) = tranLFRem ((s ←∨→ s₁) ←∨→ s₂) ltr
tranLFRem ((s ←∂) ←∂) (∂∂d ltr)          = tranLFRem (s ←∂) ltr
tranLFRem (↓ x) (∂∂d ltr)          = ↓ x
tranLFRem ((↓ x) ←∂) (∂∂d ltr)          = tranLFRem ((↓ x) ←∂→ ((↓ x) ←∂)) ltr
tranLFRem ((∂→ s) ←∂) (∂∂d ltr)          = tranLFRem (∂→ (s ←∂)) ltr
tranLFRem ((s ←∂→ s₁) ←∂) (∂∂d ltr)      = tranLFRem (s ←∂→ (s₁ ←∂)) ltr
tranLFRem (∂→ s) (∂∂d ltr)               = tranLFRem (∂→ (∂→ s)) ltr
tranLFRem ((↓ x) ←∂→ s₁) (∂∂d ltr)      = tranLFRem ((↓ x) ←∂→ ((↓ x) ←∂→ s₁)) ltr
tranLFRem ((s ←∂) ←∂→ s₁) (∂∂d ltr)      = tranLFRem (s ←∂→ (∂→ s₁)) ltr
tranLFRem ((∂→ s) ←∂→ s₁) (∂∂d ltr)      = tranLFRem (∂→ (s ←∂→ s₁)) ltr
tranLFRem ((s ←∂→ s₁) ←∂→ s₂) (∂∂d ltr)  = tranLFRem (s ←∂→ (s₁ ←∂→ s₂)) ltr
tranLFRem (s ←∂) (¬∂∂d ltr)              = tranLFRem ((s ←∂) ←∂) ltr
tranLFRem (∂→ (s ←∂)) (¬∂∂d ltr)         = tranLFRem ((∂→ s) ←∂) ltr
tranLFRem (↓ x) (¬∂∂d ltr)         = ↓ x
tranLFRem (∂→ (↓ x)) (¬∂∂d ltr)         = tranLFRem ((∂→ (↓ x)) ←∂→ (↓ x)) ltr
tranLFRem (∂→ (∂→ s)) (¬∂∂d ltr)         = tranLFRem (∂→ s) ltr
tranLFRem (∂→ (s ←∂→ s₁)) (¬∂∂d ltr)     = tranLFRem ((∂→ s) ←∂→ s₁) ltr
tranLFRem (s ←∂→ (↓ x)) (¬∂∂d ltr)     = tranLFRem ((s ←∂→ (↓ x)) ←∂→ (↓ x)) ltr
tranLFRem (s ←∂→ (s₁ ←∂)) (¬∂∂d ltr)     = tranLFRem ((s ←∂→ s₁) ←∂) ltr
tranLFRem (s ←∂→ (∂→ s₁)) (¬∂∂d ltr)     = tranLFRem ((s ←∂) ←∂→ s₁) ltr
tranLFRem (s ←∂→ (s₁ ←∂→ s₂)) (¬∂∂d ltr) = tranLFRem ((s ←∂→ s₁) ←∂→ s₂) ltr


extendLFRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → IndexLL {i} {u} pll ll → SetLFRem {i} olf pll → SetLFRem olf ll
extendLFRem ↓ sr = sr
extendLFRem (ind ←∧) sr = (extendLFRem ind sr) ←∧
extendLFRem (∧→ ind) sr = ∧→ (extendLFRem ind sr)
extendLFRem (ind ←∨) sr = (extendLFRem ind sr) ←∨
extendLFRem (∨→ ind) sr = ∨→ (extendLFRem ind sr)
extendLFRem (ind ←∂) sr = (extendLFRem ind sr) ←∂
extendLFRem (∂→ ind) sr = ∂→ (extendLFRem ind sr)

replaceLFRem : ∀{i u oll orll ll pll rll} → {olf : LFun {i} {u} oll orll} → (ind : IndexLL {i} {u} pll ll) → SetLFRem {i} olf rll → SetLFRem olf ll → SetLFRem olf (replLL ll ind rll)
replaceLFRem ↓ esr sr = esr
replaceLFRem {rll = rll} (ind ←∧) esr (↓ x) = (extendLFRem (updInd rll ind) esr) ←∧
replaceLFRem {rll = rll} (ind ←∧) esr (sr ←∧) = replaceLFRem ind esr sr ←∧
replaceLFRem {rll = rll} (ind ←∧) esr (∧→ sr) = (extendLFRem (updInd rll ind) esr) ←∧→ sr
replaceLFRem {rll = rll} (ind ←∧) esr (sr ←∧→ sr₁) = (replaceLFRem ind esr sr) ←∧→ sr₁
replaceLFRem {rll = rll} (∧→ ind) esr (↓ x) = ∧→ (extendLFRem (updInd rll ind) esr)
replaceLFRem {rll = rll} (∧→ ind) esr (sr ←∧) = sr ←∧→ (extendLFRem (updInd rll ind) esr)
replaceLFRem {rll = rll} (∧→ ind) esr (∧→ sr) = ∧→ replaceLFRem ind esr sr
replaceLFRem {rll = rll} (∧→ ind) esr (sr ←∧→ sr₁) = sr ←∧→ replaceLFRem ind esr sr₁
replaceLFRem {rll = rll} (ind ←∨) esr (↓ x) = (extendLFRem (updInd rll ind) esr) ←∨
replaceLFRem {rll = rll} (ind ←∨) esr (sr ←∨) = replaceLFRem ind esr sr ←∨
replaceLFRem {rll = rll} (ind ←∨) esr (∨→ sr) = (extendLFRem (updInd rll ind) esr) ←∨→ sr
replaceLFRem {rll = rll} (ind ←∨) esr (sr ←∨→ sr₁) = (replaceLFRem ind esr sr) ←∨→ sr₁
replaceLFRem {rll = rll} (∨→ ind) esr (↓ x) = ∨→ (extendLFRem (updInd rll ind) esr)
replaceLFRem {rll = rll} (∨→ ind) esr (sr ←∨) = sr ←∨→ (extendLFRem (updInd rll ind) esr)
replaceLFRem {rll = rll} (∨→ ind) esr (∨→ sr) = ∨→ replaceLFRem ind esr sr
replaceLFRem {rll = rll} (∨→ ind) esr (sr ←∨→ sr₁) = sr ←∨→ replaceLFRem ind esr sr₁
replaceLFRem {rll = rll} (ind ←∂) esr (↓ x) = (extendLFRem (updInd rll ind) esr) ←∂
replaceLFRem {rll = rll} (ind ←∂) esr (sr ←∂) = replaceLFRem ind esr sr ←∂
replaceLFRem {rll = rll} (ind ←∂) esr (∂→ sr) = (extendLFRem (updInd rll ind) esr) ←∂→ sr
replaceLFRem {rll = rll} (ind ←∂) esr (sr ←∂→ sr₁) = (replaceLFRem ind esr sr) ←∂→ sr₁
replaceLFRem {rll = rll} (∂→ ind) esr (↓ x) = ∂→ (extendLFRem (updInd rll ind) esr)
replaceLFRem {rll = rll} (∂→ ind) esr (sr ←∂) = sr ←∂→ (extendLFRem (updInd rll ind) esr)
replaceLFRem {rll = rll} (∂→ ind) esr (∂→ sr) = ∂→ replaceLFRem ind esr sr
replaceLFRem {rll = rll} (∂→ ind) esr (sr ←∂→ sr₁) = sr ←∂→ replaceLFRem ind esr sr₁


mreplaceLFRem :  ∀{i u oll orll ll pll rll} → {olf : LFun {i} {u} oll orll} → (ind : IndexLL {i} {u} pll ll) → MSetLFRem {i} olf rll → MSetLFRem olf ll → MSetLFRem olf (replLL ll ind rll)
mreplaceLFRem ind ∅ ∅ = ∅
mreplaceLFRem {rll = rll} ind ∅ (¬∅ x) = delLFRem x ind rll
mreplaceLFRem {rll = rll} ind (¬∅ x) ∅ = ¬∅ (extendLFRem (updInd rll ind) x)
mreplaceLFRem ind (¬∅ x) (¬∅ x₁) = ¬∅ (replaceLFRem ind x x₁)



-- Move this function to LinFunCut

findCallGraph : ∀{i u oll orll} → (olf : LFun {i} {u} oll orll) → MSetLF olf olf
findCallGraph olf = proj₂ $ findCallGraph` olf (λ x → x) ∅ ∅ where
  findCallGraph` : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → (lf : LFun {i} {u} ll rll) → (IndexLF lf → IndexLF olf) → MSetLFRem olf ll → MSetLF olf olf → MSetLFRem olf rll × MSetLF olf olf
  findCallGraph` I if msr ms = msr , ms
  findCallGraph` (_⊂_ {ind = ind} lf lf₁) if msr ms = let emsr , ems = findCallGraph` lf (λ x → if (x ←⊂)) (truncSetLFRem msr ind) ms
                                                  in findCallGraph` lf₁ (λ x → if (⊂→ x)) (mreplaceLFRem ind emsr msr) ems 
  findCallGraph` (tr ltr lf) if ∅ ms = ∅ , ms
  findCallGraph` (tr ltr lf) if (¬∅ x) ms = findCallGraph` lf (λ x → if (tr x)) (¬∅ $ tranLFRem x ltr) ms
  findCallGraph` (com df lf) if ∅ ms = findCallGraph` lf (λ x → if (com x)) ∅ ms
  findCallGraph` (com df lf) if (¬∅ x) ms = IMPOSSIBLE
  findCallGraph` {ll = ll} {rll = call .∞rll} {olf = olf} (call {∞rll = ∞rll} x) if msr ms = ¬∅ (∅-addLFRem ↓ (if ↓)) , hf (if ↓) msr ms where
    hf : ∀{ll} → IndexLF olf → MSetLFRem olf ll → MSetLF olf olf → MSetLF olf olf
    hf oic ∅ ms = ms
    hf oic (¬∅ (↓ x₁)) ms₁ = maddLF ms₁ oic x₁ 
    hf oic (¬∅ (x₁ ←∧)) ms₁ = hf oic (¬∅ x₁) ms₁
    hf oic (¬∅ (∧→ x₁)) ms₁ = hf oic (¬∅ x₁) ms₁
    hf oic (¬∅ (x₁ ←∧→ x₂)) ms₁ = hf oic (¬∅ x₁) ms₁
    hf oic (¬∅ (x₁ ←∨)) ms₁ = hf oic (¬∅ x₁) ms₁
    hf oic (¬∅ (∨→ x₁)) ms₁ = hf oic (¬∅ x₁) ms₁
    hf oic (¬∅ (x₁ ←∨→ x₂)) ms₁ = hf oic (¬∅ x₁) ms₁
    hf oic (¬∅ (x₁ ←∂)) ms₁ = hf oic (¬∅ x₁) ms₁
    hf oic (¬∅ (∂→ x₁)) ms₁ = hf oic (¬∅ x₁) ms₁
    hf oic (¬∅ (x₁ ←∂→ x₂)) ms₁ = hf oic (¬∅ x₁) ms₁


