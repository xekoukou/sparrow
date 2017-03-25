
module SetLLRem where

open import Common hiding (_≤_)
open import SetLL
open import LinLogic
import Data.List
open import Data.Vec
open import Data.Product



-- A SetLL that remembers the position of its elements under transformations.
data SetLLRem {pi : Size} {i : Size< ↑ pi} {u} (pll : LinLogic pi {u}) : LinLogic i {u} → Set (lsuc u) where
  ↓∅    : ∀{rll} → IndexLL {pi} rll pll         → SetLLRem pll ∅
  ↓τ    : ∀{rll} → ∀{n} {dt : Vec (Set u) n} → {gT : genT dt } →
           IndexLL {pi} rll pll                 → SetLLRem pll (τ gT)
  ↓c    : ∀{∞ll rll} → IndexLL {pi} rll pll     → SetLLRem pll (call ∞ll)
  _←∧   : ∀{rs ls} → SetLLRem pll ls            → SetLLRem pll (ls ∧ rs)
  ∧→_   : ∀{rs ls} → SetLLRem pll rs            → SetLLRem pll (ls ∧ rs)
  _←∧→_ : ∀{rs ls} → SetLLRem pll ls → SetLLRem pll rs → SetLLRem pll (ls ∧ rs)
  _←∨   : ∀{rs ls} → SetLLRem pll ls            → SetLLRem pll (ls ∨ rs)
  ∨→_   : ∀{rs ls} → SetLLRem pll rs            → SetLLRem pll (ls ∨ rs)
  _←∨→_ : ∀{rs ls} → SetLLRem pll ls → SetLLRem pll rs → SetLLRem pll (ls ∨ rs)
  _←∂   : ∀{rs ls} → SetLLRem pll ls            → SetLLRem pll (ls ∂ rs)
  ∂→_   : ∀{rs ls} → SetLLRem pll rs            → SetLLRem pll (ls ∂ rs)
  _←∂→_ : ∀{rs ls} → SetLLRem pll ls → SetLLRem pll rs → SetLLRem pll (ls ∂ rs)
  


-- A possibly empty set of nodes in a Linear Logic tree. 
data MSetLLRem {pi : Size} {i : Size< ↑ pi} {u} (pll : LinLogic pi {u}) : LinLogic i {u} → Set (lsuc u) where
  ∅   : ∀{ll}            → MSetLLRem pll ll
  ¬∅  : ∀{ll} → SetLLRem pll ll → MSetLLRem pll ll

reConSet : {pi : Size} → {i : Size< ↑ pi} → ∀{u} → {pll : LinLogic pi {u}} → {ll : LinLogic i {u}} → SetLLRem {pi} {i} pll ll → MSetLL pll
reConSet {pi} {i} {u} {pll} sr = reConSet` sr ∅ where
  reConSet` : {ll : LinLogic i {u}} → SetLLRem {pi} {i} pll ll → MSetLL pll → MSetLL pll
  reConSet` (↓∅ {rll = rll} x) s with (madd {q = rll} s x rll)
  ... | r with (replLL pll x rll) | (replLL-id pll x rll refl)
  reConSet` (↓∅ {rll} x) s | r | m | refl = r
  reConSet` (↓τ {rll = rll} x) s with (madd {q = rll} s x rll)
  ... | r with (replLL pll x rll) | (replLL-id pll x rll refl)
  reConSet` (↓τ {rll} x) s | r | m | refl = r
  reConSet` (↓c {rll = rll} x) s with (madd {q = rll} s x rll)
  ... | r with (replLL pll x rll) | (replLL-id pll x rll refl)
  reConSet` (↓c {rll} x) s | r | m | refl = r
  reConSet` (sr ←∧) s = reConSet` sr s
  reConSet` (∧→ sr) s = reConSet` sr s
  reConSet` (sr ←∧→ sr₁) s = (reConSet` sr s) ∪ₘₛ (reConSet` sr₁ s)
  reConSet` (sr ←∨) s = reConSet` sr s
  reConSet` (∨→ sr) s = reConSet` sr s
  reConSet` (sr ←∨→ sr₁) s = (reConSet` sr s) ∪ₘₛ (reConSet` sr₁ s)
  reConSet` (sr ←∂) s = reConSet` sr s
  reConSet` (∂→ sr) s = reConSet` sr s
  reConSet` (sr ←∂→ sr₁) s =  (reConSet` sr s) ∪ₘₛ (reConSet` sr₁ s)

-- TODO We shouldn't need this. When issue agda #2409 is resolved, remove this.
drsize : ∀{pi u pll} → {i : Size< ↑ pi} → ∀{ll} {j : Size< ↑ i} → SetLLRem {pi} {i} {u} pll ll → SetLLRem {pi} {j} pll ll
drsize (↓∅ mm)          = (↓∅ mm)
drsize (↓τ mm)          = (↓τ mm)
drsize (↓c mm)          = (↓c mm)
drsize (x ←∧)     = (drsize x) ←∧
drsize (∧→ x)     = ∧→ (drsize x)
drsize (x ←∧→ x₁) = (drsize x ←∧→ drsize x₁)
drsize (x ←∨)     = (drsize x) ←∨
drsize (∨→ x)     = ∨→ (drsize x)
drsize (x ←∨→ x₁) = (drsize x ←∨→ drsize x₁)
drsize (x ←∂)     = (drsize x) ←∂
drsize (∂→ x)     = ∂→ (drsize x)
drsize (x ←∂→ x₁) = (drsize x ←∂→ drsize x₁)

-- It is required to fill all the lower levels with the indexes that we are to truck.
-- This is used to fill the initial memory of SetLLRem

fillAllLowerRem : ∀{i u} → ∀ ll → SetLLRem {i} {_} {u} ll ll
fillAllLowerRem ll = fillAllLowerRem` ll (λ x → x) where
  fillAllLowerRem` : ∀{pi} → {i : Size< ↑ pi} → ∀{u pll} → ∀ ll → (∀{rll} → IndexLL rll ll → IndexLL rll pll) → SetLLRem {pi} {i} {u} pll ll
  fillAllLowerRem` ∅ f = ↓∅ (f ↓)
  fillAllLowerRem` (τ x) f = ↓τ (f ↓)
  fillAllLowerRem` (ll₁ ∧ ll₂) f = (fillAllLowerRem` ll₁ (λ x → f (x ←∧)) ) ←∧→ (fillAllLowerRem` ll₂ (λ x → f (∧→ x)) )
  fillAllLowerRem` (ll₁ ∨ ll₂) f = (fillAllLowerRem` ll₁ (λ x → f (x ←∨))) ←∨→ (fillAllLowerRem` ll₂ (λ x → f (∨→ x)))
  fillAllLowerRem` (ll₁ ∂ ll₂) f = (fillAllLowerRem` ll₁ (λ x → f (x ←∂))) ←∂→ (fillAllLowerRem` ll₂ (λ x → f (∂→ x)))
  fillAllLowerRem` (call x) f =  ↓c (f ↓)



delRem : ∀{pi} → {i : Size< ↑ pi} → ∀{u ll pll q} → {j : Size< ↑ i} → SetLLRem {pi} {i} pll ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic j)
      → MSetLLRem {pi} {j} pll (replLL ll ind rll)
delRem s ↓ rll = ∅
delRem (s ←∧) (ind ←∧) rll with (delRem s ind rll)
delRem (s ←∧) (ind ←∧) rll | ∅ = ∅
delRem (s ←∧) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧)
delRem (∧→ s) (ind ←∧) rll = ¬∅ (∧→ (drsize s))
delRem (s ←∧→ s₁) (ind ←∧) rll with (delRem s ind rll)
delRem (s ←∧→ s₁) (ind ←∧) rll | ∅ = ¬∅ (∧→ (drsize s₁))
delRem (s ←∧→ s₁) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧→ (drsize s₁))
delRem (s ←∧) (∧→ ind) rll = ¬∅ ((drsize s) ←∧)
delRem (∧→ s) (∧→ ind) rll with (delRem s ind rll)
delRem (∧→ s) (∧→ ind) rll | ∅ = ∅
delRem (∧→ s) (∧→ ind) rll | ¬∅ x = ¬∅ (∧→ x)
delRem (s ←∧→ s₁) (∧→ ind) rll with (delRem s₁ ind rll)
delRem (s ←∧→ s₁) (∧→ ind) rll | ∅ = ¬∅ ((drsize s) ←∧)
delRem (s ←∧→ s₁) (∧→ ind) rll | ¬∅ x = ¬∅ ((drsize s) ←∧→ x)
delRem (s ←∨) (ind ←∨) rll with (delRem s ind rll)
delRem (s ←∨) (ind ←∨) rll | ∅ = ∅
delRem (s ←∨) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨)
delRem (∨→ s) (ind ←∨) rll = ¬∅ (∨→ (drsize s))
delRem (s ←∨→ s₁) (ind ←∨) rll with (delRem s ind rll)
delRem (s ←∨→ s₁) (ind ←∨) rll | ∅ = ¬∅ (∨→ (drsize s₁))
delRem (s ←∨→ s₁) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨→ (drsize s₁))
delRem (s ←∨) (∨→ ind) rll = ¬∅ ((drsize s) ←∨)
delRem (∨→ s) (∨→ ind) rll with (delRem s ind rll)
delRem (∨→ s) (∨→ ind) rll | ∅ = ∅
delRem (∨→ s) (∨→ ind) rll | ¬∅ x = ¬∅ (∨→ x)
delRem (s ←∨→ s₁) (∨→ ind) rll with (delRem s₁ ind rll)
delRem (s ←∨→ s₁) (∨→ ind) rll | ∅ = ¬∅ ((drsize s) ←∨)
delRem (s ←∨→ s₁) (∨→ ind) rll | ¬∅ x = ¬∅ ((drsize s) ←∨→ x)
delRem (s ←∂) (ind ←∂) rll with (delRem s ind rll)
delRem (s ←∂) (ind ←∂) rll | ∅ = ∅
delRem (s ←∂) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂)
delRem (∂→ s) (ind ←∂) rll = ¬∅ (∂→ (drsize s))
delRem (s ←∂→ s₁) (ind ←∂) rll with (delRem s ind rll)
delRem (s ←∂→ s₁) (ind ←∂) rll | ∅ = ¬∅ (∂→ (drsize s₁))
delRem (s ←∂→ s₁) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂→ (drsize s₁))
delRem (s ←∂) (∂→ ind) rll = ¬∅ ((drsize s) ←∂)
delRem (∂→ s) (∂→ ind) rll with (delRem s ind rll)
delRem (∂→ s) (∂→ ind) rll | ∅ = ∅
delRem (∂→ s) (∂→ ind) rll | ¬∅ x = ¬∅ (∂→ x)
delRem (s ←∂→ s₁) (∂→ ind) rll with (delRem s₁ ind rll)
delRem (s ←∂→ s₁) (∂→ ind) rll | ∅ = ¬∅ ((drsize s) ←∂)
delRem (s ←∂→ s₁) (∂→ ind) rll | ¬∅ x = ¬∅ ((drsize s) ←∂→ x)

mdelRem : ∀{pi} → {i : Size< ↑ pi} → ∀{u ll pll q} → {j : Size< ↑ i} → MSetLLRem {pi} {i} pll ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic j)
      → MSetLLRem {pi} {j} pll (replLL ll ind rll)
mdelRem ∅ ind rll = ∅
mdelRem (¬∅ x) ind rll = delRem x ind rll




-- If we tranform the linear logic tree, we need to tranform the SetLLRem as well.
tranRem : ∀{pi} → {i : Size< ↑ pi} → ∀{u pll ll rll} → SetLLRem {pi} pll ll → (tr : LLTr {i} {u} rll ll)
       → SetLLRem pll rll
tranRem s I                           = s
tranRem (s ←∂) (∂c tr)                = tranRem (∂→ s) tr
tranRem (∂→ s) (∂c tr)                = tranRem (s ←∂) tr
tranRem (s ←∂→ s₁) (∂c tr)            = tranRem (s₁ ←∂→ s) tr
tranRem (s ←∨) (∨c tr)                = tranRem (∨→ s) tr
tranRem (∨→ s) (∨c tr)                = tranRem (s ←∨) tr
tranRem (s ←∨→ s₁) (∨c tr)            = tranRem (s₁ ←∨→ s) tr
tranRem (s ←∧) (∧c tr)                = tranRem (∧→ s) tr
tranRem (∧→ s) (∧c tr)                = tranRem (s ←∧) tr
tranRem (s ←∧→ s₁) (∧c tr)            = tranRem (s₁ ←∧→ s) tr
-- tranRem (↓ mm) (∧∂d tr)                    = (↓ mm)
-- tranRem ((↓ mm) ←∧) (∧∂d tr)               = tranRem (((↓ mm) ←∧) ←∂→ ((↓ mm) ←∧)) tr
-- tranRem ((s ←∂) ←∧) (∧∂d tr)          = tranRem ((s ←∧) ←∂) tr
-- tranRem ((∂→ s) ←∧) (∧∂d tr)          = tranRem (∂→ (s ←∧)) tr
-- tranRem ((s ←∂→ s₁) ←∧) (∧∂d tr)      = tranRem ((s ←∧) ←∂→ (s₁ ←∧)) tr
-- tranRem (∧→ s) (∧∂d tr)               = tranRem ((∧→ s) ←∂→ (∧→ s)) tr
-- tranRem ((↓ mm) ←∧→ s₁) (∧∂d tr)           = tranRem (((↓ mm) ←∧→ s₁) ←∂→ ((↓ mm) ←∧→ s₁)) tr
-- tranRem ((s ←∂) ←∧→ s₁) (∧∂d tr)      = tranRem ((s ←∧→ s₁) ←∂) tr
-- tranRem ((∂→ s) ←∧→ s₁) (∧∂d tr)      = tranRem (∂→ (s ←∧→ s₁)) tr
-- tranRem ((s ←∂→ s₁) ←∧→ s₂) (∧∂d tr)  = tranRem ((s ←∧→ s₂) ←∂→ (s₁ ←∧→ s₂)) tr
-- tranRem (↓ mm) (∧∨d tr)                    = (↓ mm)
-- tranRem ((↓ mm) ←∧) (∧∨d tr)               = tranRem (((↓ mm) ←∧) ←∨→ ((↓ mm) ←∧)) tr
-- tranRem ((s ←∨) ←∧) (∧∨d tr)          = tranRem ((s ←∧) ←∨) tr
-- tranRem ((∨→ s) ←∧) (∧∨d tr)          = tranRem (∨→ (s ←∧)) tr
-- tranRem ((s ←∨→ s₁) ←∧) (∧∨d tr)      = tranRem ((s ←∧) ←∨→ (s₁ ←∧)) tr
-- tranRem (∧→ s) (∧∨d tr)               = tranRem ((∧→ s) ←∨→ (∧→ s)) tr
-- tranRem ((↓ mm) ←∧→ s₁) (∧∨d tr)           = tranRem (((↓ mm) ←∧→ s₁) ←∨→ ((↓ mm) ←∧→ s₁)) tr
-- tranRem ((s ←∨) ←∧→ s₁) (∧∨d tr)      = tranRem ((s ←∧→ s₁) ←∨) tr
-- tranRem ((∨→ s) ←∧→ s₁) (∧∨d tr)      = tranRem (∨→ (s ←∧→ s₁)) tr
-- tranRem ((s ←∨→ s₁) ←∧→ s₂) (∧∨d tr)  = tranRem ((s ←∧→ s₂) ←∨→ (s₁ ←∧→ s₂)) tr
-- tranRem (↓ mm) (∨∂d tr)                    = (↓ mm)
-- tranRem ((↓ mm) ←∨) (∨∂d tr)               = tranRem (((↓ mm) ←∨) ←∂→ ((↓ mm) ←∨)) tr
-- tranRem ((s ←∂) ←∨) (∨∂d tr)          = tranRem ((s ←∨) ←∂) tr
-- tranRem ((∂→ s) ←∨) (∨∂d tr)          = tranRem (∂→ (s ←∨)) tr
-- tranRem ((s ←∂→ s₁) ←∨) (∨∂d tr)      = tranRem ((s ←∨) ←∂→ (s₁ ←∨)) tr
-- tranRem (∨→ s) (∨∂d tr)               = tranRem ((∨→ s) ←∂→ (∨→ s)) tr
-- tranRem ((↓ mm) ←∨→ s₁) (∨∂d tr)           = tranRem (((↓ mm) ←∨→ s₁) ←∂→ ((↓ mm) ←∨→ s₁)) tr
-- tranRem ((s ←∂) ←∨→ s₁) (∨∂d tr)      = tranRem ((s ←∨→ s₁) ←∂) tr
-- tranRem ((∂→ s) ←∨→ s₁) (∨∂d tr)      = tranRem (∂→ (s ←∨→ s₁)) tr
-- tranRem ((s ←∂→ s₁) ←∨→ s₂) (∨∂d tr)  = tranRem ((s ←∨→ s₂) ←∂→ (s₁ ←∨→ s₂)) tr 
-- tranRem (↓ mm) (∂∨d tr)                    = (↓ mm)
-- tranRem ((↓ mm) ←∂) (∂∨d tr)               = tranRem (((↓ mm) ←∂) ←∨→ ((↓ mm) ←∂)) tr
-- tranRem ((s ←∨) ←∂) (∂∨d tr)          = tranRem ((s ←∂) ←∨) tr
-- tranRem ((∨→ s) ←∂) (∂∨d tr)          = tranRem (∨→ (s ←∂)) tr
-- tranRem ((s ←∨→ s₁) ←∂) (∂∨d tr)      = tranRem ((s ←∂) ←∨→ (s₁ ←∂)) tr
-- tranRem (∂→ s) (∂∨d tr)               = tranRem ((∂→ s) ←∨→ (∂→ s)) tr
-- tranRem ((↓ mm) ←∂→ s₁) (∂∨d tr)           = tranRem (((↓ mm) ←∂→ s₁) ←∨→ ((↓ mm) ←∂→ s₁)) tr
-- tranRem ((s ←∨) ←∂→ s₁) (∂∨d tr)      = tranRem ((s ←∂→ s₁) ←∨) tr
-- tranRem ((∨→ s) ←∂→ s₁) (∂∨d tr)      = tranRem (∨→ (s ←∂→ s₁)) tr
-- tranRem ((s ←∨→ s₁) ←∂→ s₂) (∂∨d tr)  = tranRem ((s ←∂→ s₂) ←∨→ (s₁ ←∂→ s₂)) tr 
tranRem ((s ←∧) ←∧) (∧∧d tr)          = tranRem (s ←∧) tr
tranRem ((∧→ s) ←∧) (∧∧d tr)          = tranRem (∧→ (s ←∧)) tr
tranRem ((s ←∧→ s₁) ←∧) (∧∧d tr)      = tranRem (s ←∧→ (s₁ ←∧)) tr
tranRem (∧→ s) (∧∧d tr)               = tranRem (∧→ (∧→ s)) tr
tranRem ((s ←∧) ←∧→ s₁) (∧∧d tr)      = tranRem (s ←∧→ (∧→ s₁)) tr
tranRem ((∧→ s) ←∧→ s₁) (∧∧d tr)      = tranRem (∧→ (s ←∧→ s₁)) tr
tranRem ((s ←∧→ s₁) ←∧→ s₂) (∧∧d tr)  = tranRem (s ←∧→ (s₁ ←∧→ s₂)) tr
tranRem (s ←∧) (¬∧∧d tr)              = tranRem ((s ←∧) ←∧) tr
tranRem (∧→ (s ←∧)) (¬∧∧d tr)         = tranRem ((∧→ s) ←∧) tr
tranRem (∧→ (∧→ s)) (¬∧∧d tr)         = tranRem (∧→ s) tr
tranRem (∧→ (s ←∧→ s₁)) (¬∧∧d tr)     = tranRem ((∧→ s) ←∧→ s₁) tr
tranRem (s ←∧→ (s₁ ←∧)) (¬∧∧d tr)     = tranRem ((s ←∧→ s₁) ←∧) tr
tranRem (s ←∧→ (∧→ s₁)) (¬∧∧d tr)     = tranRem ((s ←∧) ←∧→ s₁) tr
tranRem (s ←∧→ (s₁ ←∧→ s₂)) (¬∧∧d tr) = tranRem ((s ←∧→ s₁) ←∧→ s₂) tr
tranRem ((s ←∨) ←∨) (∨∨d tr)          = tranRem (s ←∨) tr
tranRem ((∨→ s) ←∨) (∨∨d tr)          = tranRem (∨→ (s ←∨)) tr
tranRem ((s ←∨→ s₁) ←∨) (∨∨d tr)      = tranRem (s ←∨→ (s₁ ←∨)) tr
tranRem (∨→ s) (∨∨d tr)               = tranRem (∨→ (∨→ s)) tr
tranRem ((s ←∨) ←∨→ s₁) (∨∨d tr)      = tranRem (s ←∨→ (∨→ s₁)) tr
tranRem ((∨→ s) ←∨→ s₁) (∨∨d tr)      = tranRem (∨→ (s ←∨→ s₁)) tr
tranRem ((s ←∨→ s₁) ←∨→ s₂) (∨∨d tr)  = tranRem (s ←∨→ (s₁ ←∨→ s₂)) tr
tranRem (s ←∨) (¬∨∨d tr)              = tranRem ((s ←∨) ←∨) tr
tranRem (∨→ (s ←∨)) (¬∨∨d tr)         = tranRem ((∨→ s) ←∨) tr
tranRem (∨→ (∨→ s)) (¬∨∨d tr)         = tranRem (∨→ s) tr
tranRem (∨→ (s ←∨→ s₁)) (¬∨∨d tr)     = tranRem ((∨→ s) ←∨→ s₁) tr
tranRem (s ←∨→ (s₁ ←∨)) (¬∨∨d tr)     = tranRem ((s ←∨→ s₁) ←∨) tr
tranRem (s ←∨→ (∨→ s₁)) (¬∨∨d tr)     = tranRem ((s ←∨) ←∨→ s₁) tr
tranRem (s ←∨→ (s₁ ←∨→ s₂)) (¬∨∨d tr) = tranRem ((s ←∨→ s₁) ←∨→ s₂) tr
tranRem ((s ←∂) ←∂) (∂∂d tr)          = tranRem (s ←∂) tr
tranRem ((∂→ s) ←∂) (∂∂d tr)          = tranRem (∂→ (s ←∂)) tr
tranRem ((s ←∂→ s₁) ←∂) (∂∂d tr)      = tranRem (s ←∂→ (s₁ ←∂)) tr
tranRem (∂→ s) (∂∂d tr)               = tranRem (∂→ (∂→ s)) tr
tranRem ((s ←∂) ←∂→ s₁) (∂∂d tr)      = tranRem (s ←∂→ (∂→ s₁)) tr
tranRem ((∂→ s) ←∂→ s₁) (∂∂d tr)      = tranRem (∂→ (s ←∂→ s₁)) tr
tranRem ((s ←∂→ s₁) ←∂→ s₂) (∂∂d tr)  = tranRem (s ←∂→ (s₁ ←∂→ s₂)) tr
tranRem (s ←∂) (¬∂∂d tr)              = tranRem ((s ←∂) ←∂) tr
tranRem (∂→ (s ←∂)) (¬∂∂d tr)         = tranRem ((∂→ s) ←∂) tr
tranRem (∂→ (∂→ s)) (¬∂∂d tr)         = tranRem (∂→ s) tr
tranRem (∂→ (s ←∂→ s₁)) (¬∂∂d tr)     = tranRem ((∂→ s) ←∂→ s₁) tr
tranRem (s ←∂→ (s₁ ←∂)) (¬∂∂d tr)     = tranRem ((s ←∂→ s₁) ←∂) tr
tranRem (s ←∂→ (∂→ s₁)) (¬∂∂d tr)     = tranRem ((s ←∂) ←∂→ s₁) tr
tranRem (s ←∂→ (s₁ ←∂→ s₂)) (¬∂∂d tr) = tranRem ((s ←∂→ s₁) ←∂→ s₂) tr




-- Transformations that start from a specific index.
itranRem : ∀{pi} → {i : Size< ↑ pi} → ∀{u ll rll pll vll} → SetLLRem {pi} pll ll → (ind : IndexLL {i} {u} vll ll) → (tr : LLTr rll vll)
        → SetLLRem pll (replLL ll ind rll)
itranRem s ↓ tr                 = tranRem s tr
itranRem (s ←∧) (ind ←∧) tr     = itranRem s ind tr ←∧
itranRem (∧→ s) (ind ←∧) tr     = ∧→ s
itranRem (s ←∧→ s₁) (ind ←∧) tr = itranRem s ind tr ←∧→ s₁ 
itranRem (s ←∧) (∧→ ind) tr     = s ←∧
itranRem (∧→ s) (∧→ ind) tr     = ∧→ itranRem s ind tr
itranRem (s ←∧→ s₁) (∧→ ind) tr = s ←∧→ itranRem s₁ ind tr
itranRem (s ←∨) (ind ←∨) tr     = itranRem s ind tr ←∨
itranRem (∨→ s) (ind ←∨) tr     = ∨→ s
itranRem (s ←∨→ s₁) (ind ←∨) tr = itranRem s ind tr ←∨→ s₁ 
itranRem (s ←∨) (∨→ ind) tr     = s ←∨
itranRem (∨→ s) (∨→ ind) tr     = ∨→ itranRem s ind tr
itranRem (s ←∨→ s₁) (∨→ ind) tr = s ←∨→ itranRem s₁ ind tr
itranRem (s ←∂) (ind ←∂) tr     = itranRem s ind tr ←∂
itranRem (∂→ s) (ind ←∂) tr     = ∂→ s
itranRem (s ←∂→ s₁) (ind ←∂) tr = itranRem s ind tr ←∂→ s₁ 
itranRem (s ←∂) (∂→ ind) tr     = s ←∂
itranRem (∂→ s) (∂→ ind) tr     = ∂→ itranRem s ind tr
itranRem (s ←∂→ s₁) (∂→ ind) tr = s ←∂→ itranRem s₁ ind tr


truncSetLLRem : ∀{pi} → {i : Size< ↑ pi} → ∀{u ll pll q} → {j : Size< ↑ i} → MSetLLRem {pi} {i} pll ll → (ind : IndexLL {i} {u} q ll) → MSetLLRem {pi} {i} pll q
truncSetLLRem ∅ ind = ∅
truncSetLLRem (¬∅ x) ↓ = ¬∅ x
truncSetLLRem (¬∅ (x ←∧)) (ind ←∧) = truncSetLLRem (¬∅ x) ind
truncSetLLRem (¬∅ (∧→ x)) (ind ←∧) = ∅
truncSetLLRem (¬∅ (x ←∧→ x₁)) (ind ←∧) = truncSetLLRem (¬∅ x) ind
truncSetLLRem (¬∅ (x ←∧)) (∧→ ind) = ∅
truncSetLLRem (¬∅ (∧→ x)) (∧→ ind) =  truncSetLLRem (¬∅ x) ind
truncSetLLRem (¬∅ (x ←∧→ x₁)) (∧→ ind) =  truncSetLLRem (¬∅ x₁) ind
truncSetLLRem (¬∅ (x ←∨)) (ind ←∨) = truncSetLLRem (¬∅ x) ind
truncSetLLRem (¬∅ (∨→ x)) (ind ←∨) = ∅
truncSetLLRem (¬∅ (x ←∨→ x₁)) (ind ←∨) = truncSetLLRem (¬∅ x) ind
truncSetLLRem (¬∅ (x ←∨)) (∨→ ind) = ∅
truncSetLLRem (¬∅ (∨→ x)) (∨→ ind) =  truncSetLLRem (¬∅ x) ind
truncSetLLRem (¬∅ (x ←∨→ x₁)) (∨→ ind) =  truncSetLLRem (¬∅ x₁) ind
truncSetLLRem (¬∅ (x ←∂)) (ind ←∂) = truncSetLLRem (¬∅ x) ind
truncSetLLRem (¬∅ (∂→ x)) (ind ←∂) = ∅
truncSetLLRem (¬∅ (x ←∂→ x₁)) (ind ←∂) = truncSetLLRem (¬∅ x) ind
truncSetLLRem (¬∅ (x ←∂)) (∂→ ind) = ∅
truncSetLLRem (¬∅ (∂→ x)) (∂→ ind) =  truncSetLLRem (¬∅ x) ind
truncSetLLRem (¬∅ (x ←∂→ x₁)) (∂→ ind) =  truncSetLLRem (¬∅ x₁) ind


extendRem : ∀{pi u oll} → {i : Size< ↑ pi} → ∀{ll pll} → IndexLL {i} {u} pll ll → SetLLRem {pi} {i} oll pll → SetLLRem oll ll
extendRem ↓ sr = sr
extendRem (ind ←∧) sr = (extendRem ind sr) ←∧
extendRem (∧→ ind) sr = ∧→ (extendRem ind sr)
extendRem (ind ←∨) sr = (extendRem ind sr) ←∨
extendRem (∨→ ind) sr = ∨→ (extendRem ind sr)
extendRem (ind ←∂) sr = (extendRem ind sr) ←∂
extendRem (∂→ ind) sr = ∂→ (extendRem ind sr)

replaceRem : ∀{pi u oll} → {i : Size< ↑ pi} → ∀{ll pll} → IndexLL {i} {u} pll ll → SetLLRem {pi} {i} oll pll → SetLLRem oll ll → SetLLRem oll ll
replaceRem ↓ esr sr = esr
replaceRem (ind ←∧) esr (sr ←∧) = replaceRem ind esr sr ←∧
replaceRem (ind ←∧) esr (∧→ sr) = (extendRem ind esr) ←∧→ sr
replaceRem (ind ←∧) esr (sr ←∧→ sr₁) = (replaceRem ind esr sr) ←∧→ sr₁
replaceRem (∧→ ind) esr (sr ←∧) = sr ←∧→ (extendRem ind esr)
replaceRem (∧→ ind) esr (∧→ sr) = ∧→ replaceRem ind esr sr
replaceRem (∧→ ind) esr (sr ←∧→ sr₁) = sr ←∧→ replaceRem ind esr sr₁
replaceRem (ind ←∨) esr (sr ←∨) = replaceRem ind esr sr ←∨
replaceRem (ind ←∨) esr (∨→ sr) = (extendRem ind esr) ←∨→ sr
replaceRem (ind ←∨) esr (sr ←∨→ sr₁) = (replaceRem ind esr sr) ←∨→ sr₁
replaceRem (∨→ ind) esr (sr ←∨) = sr ←∨→ (extendRem ind esr)
replaceRem (∨→ ind) esr (∨→ sr) = ∨→ replaceRem ind esr sr
replaceRem (∨→ ind) esr (sr ←∨→ sr₁) = sr ←∨→ replaceRem ind esr sr₁
replaceRem (ind ←∂) esr (sr ←∂) = replaceRem ind esr sr ←∂
replaceRem (ind ←∂) esr (∂→ sr) = (extendRem ind esr) ←∂→ sr
replaceRem (ind ←∂) esr (sr ←∂→ sr₁) = (replaceRem ind esr sr) ←∂→ sr₁
replaceRem (∂→ ind) esr (sr ←∂) = sr ←∂→ (extendRem ind esr)
replaceRem (∂→ ind) esr (∂→ sr) = ∂→ replaceRem ind esr sr
replaceRem (∂→ ind) esr (sr ←∂→ sr₁) = sr ←∂→ replaceRem ind esr sr₁

mreplaceRem : ∀{pi u oll} → {i : Size< ↑ pi} → ∀{ll pll} → IndexLL {i} {u} pll ll → MSetLLRem {pi} {i} oll pll → MSetLLRem oll ll → MSetLLRem oll ll
mreplaceRem ind ∅ ∅ = ∅
mreplaceRem {ll = ll} {pll = pll} ind ∅ (¬∅ x) with (replLL ll ind pll) | (delRem x ind pll) | (replLL-id ll ind pll refl)
... | m | g | refl = g
mreplaceRem ind (¬∅ x) ∅ = ¬∅ (extendRem ind x)
mreplaceRem ind (¬∅ x) (¬∅ x₁) = ¬∅ (replaceRem ind x x₁)


projToSetLL : {pi : Size} → {i : Size< ↑ pi} → ∀{u} → {pll : LinLogic pi {u}} → {ll : LinLogic i {u}} → SetLLRem {pi} {i} {u} pll ll → SetLL ll 
projToSetLL (↓∅ x) = ↓
projToSetLL (↓τ x) = ↓
projToSetLL (↓c x) = ↓
projToSetLL (sr ←∧) = (projToSetLL sr) ←∧
projToSetLL (∧→ sr) = ∧→( projToSetLL sr)
projToSetLL (sr ←∧→ sr₁) = (projToSetLL sr) ←∧→ (projToSetLL sr₁)
projToSetLL (sr ←∨) = (projToSetLL sr) ←∨
projToSetLL (∨→ sr) = ∨→( projToSetLL sr)
projToSetLL (sr ←∨→ sr₁) = (projToSetLL sr) ←∨→ (projToSetLL sr₁)
projToSetLL (sr ←∂) = (projToSetLL sr) ←∂
projToSetLL (∂→ sr) = ∂→( projToSetLL sr)
projToSetLL (sr ←∂→ sr₁) = (projToSetLL sr) ←∂→ (projToSetLL sr₁)

projToMSetLL : {pi : Size} → {i : Size< ↑ pi} → ∀{u} → {pll : LinLogic pi {u}} → {ll : LinLogic i {u}} → MSetLLRem {pi} {i} {u} pll ll → MSetLL ll 
projToMSetLL ∅ = ∅
projToMSetLL (¬∅ x) = ¬∅ (projToSetLL x)

oneElemRem : {pi : Size} → {i : Size< ↑ pi} → ∀{u} → {pll : LinLogic pi {u}} → {ll : LinLogic i {u}} → SetLLRem {pi} {i} {u} pll ll →  Σ (LinLogic pi {u}) (λ rll → IndexLL rll pll)
oneElemRem (↓∅ x)       = (_ , x)
oneElemRem (↓τ x)       = (_ , x)
oneElemRem (↓c x)       = (_ , x)
oneElemRem (sr ←∧)      = oneElemRem sr
oneElemRem (∧→ sr)      =  oneElemRem sr
oneElemRem (sr ←∧→ sr₁) =  oneElemRem sr
oneElemRem (sr ←∨)      =  oneElemRem sr
oneElemRem (∨→ sr)      =  oneElemRem sr
oneElemRem (sr ←∨→ sr₁) =  oneElemRem sr
oneElemRem (sr ←∂)      =  oneElemRem sr
oneElemRem (∂→ sr)      =  oneElemRem sr
oneElemRem (sr ←∂→ sr₁) =  oneElemRem sr


complem¬↓⇒¬∅ : {pi : Size} → {i : Size< ↑ pi} → ∀{u} → {pll : LinLogic pi {u}} → {ll : LinLogic i {u}}
                 → (ms : MSetLL ll) → (msr : MSetLLRem {pi} {i} {u} pll ll) → (ms ∪ₘₛ (projToMSetLL msr)) ≡ (¬∅ ↓)
                 → ¬ (ms ≡ ¬∅ ↓) → ¬ (msr ≡ ∅)
complem¬↓⇒¬∅ ∅ ∅ () nt
complem¬↓⇒¬∅ ∅ (¬∅ x) c nt                = λ ()
complem¬↓⇒¬∅ (¬∅ ↓) msr c nt              = λ _ → nt refl
complem¬↓⇒¬∅ (¬∅ (x ←∧)) ∅ c nt           = λ _ → nt c
complem¬↓⇒¬∅ (¬∅ (x ←∧)) (¬∅ x₁) c nt     = λ ()
complem¬↓⇒¬∅ (¬∅ (∧→ x)) ∅ c nt           = λ _ → nt c
complem¬↓⇒¬∅ (¬∅ (∧→ x)) (¬∅ x₁) c nt     = λ ()
complem¬↓⇒¬∅ (¬∅ (x ←∧→ x₁)) ∅ c nt       = λ _ → nt c
complem¬↓⇒¬∅ (¬∅ (x ←∧→ x₁)) (¬∅ x₂) c nt = λ ()
complem¬↓⇒¬∅ (¬∅ (x ←∨)) ∅ c nt           = λ _ → nt c
complem¬↓⇒¬∅ (¬∅ (x ←∨)) (¬∅ x₁) c nt     = λ ()
complem¬↓⇒¬∅ (¬∅ (∨→ x)) ∅ c nt           = λ _ → nt c
complem¬↓⇒¬∅ (¬∅ (∨→ x)) (¬∅ x₁) c nt     = λ ()
complem¬↓⇒¬∅ (¬∅ (x ←∨→ x₁)) ∅ c nt       = λ _ → nt c
complem¬↓⇒¬∅ (¬∅ (x ←∨→ x₁)) (¬∅ x₂) c nt = λ ()
complem¬↓⇒¬∅ (¬∅ (x ←∂)) ∅ c nt           = λ _ → nt c
complem¬↓⇒¬∅ (¬∅ (x ←∂)) (¬∅ x₁) c nt     = λ ()
complem¬↓⇒¬∅ (¬∅ (∂→ x)) ∅ c nt           = λ _ → nt c
complem¬↓⇒¬∅ (¬∅ (∂→ x)) (¬∅ x₁) c nt     = λ ()
complem¬↓⇒¬∅ (¬∅ (x ←∂→ x₁)) ∅ c nt       = λ _ → nt c
complem¬↓⇒¬∅ (¬∅ (x ←∂→ x₁)) (¬∅ x₂) c nt = λ ()
