{-# OPTIONS --exact-split #-}
module SetLLRem where

open import Common hiding (_≤_)
open import SetLL
open import LinLogic
open import IndexLLProp
open import LinLogicProp
import Data.List
open import Data.Vec
open import Data.Product



-- A SetLL that remembers the position of its elements under transformations.
data SetLLRem {i : Size} {u} (pll : LinLogic i {u}) : LinLogic i {u} → Set (lsuc u) where
  ↓∅    : ∀{rll} → IndexLL {i} rll pll         → SetLLRem pll ∅
  ↓τ    : ∀{rll} → ∀{n} {dt : Vec (Set u) n} → {gT : genT dt } →
           IndexLL {i} rll pll                 → SetLLRem pll (τ gT)
  ↓c    : ∀{∞ll rll} → IndexLL {i} rll pll     → SetLLRem pll (call ∞ll)
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
data MSetLLRem {i : Size} {u} (pll : LinLogic i {u}) : LinLogic i {u} → Set (lsuc u) where
  ∅   : ∀{ll}            → MSetLLRem pll ll
  ¬∅  : ∀{ll} → SetLLRem pll ll → MSetLLRem pll ll


conSet : {i : Size} → ∀{u} → {pll : LinLogic i {u}} → {ll : LinLogic i {u}} → SetLLRem {i} pll ll → SetLL pll
conSet {pll = pll} (↓∅ {rll = rll} x) with (∅-add x rll)
... | r with (replLL pll x rll) | (replLL-id pll x rll refl)
conSet {_} {_} {.g} (↓∅ {rll} x) | r | g | refl = r
conSet {pll = pll} (↓τ {rll = rll} x) with (∅-add x rll)
... | r with (replLL pll x rll) | (replLL-id pll x rll refl)
conSet {_} {_} {.g} (↓τ {rll} x) | r | g | refl = r
conSet {pll = pll} (↓c {rll = rll} x) with (∅-add x rll)
... | r with (replLL pll x rll) | (replLL-id pll x rll refl)
conSet {_} {_} {.g} (↓c {rll} x) | r | g | refl = r
conSet (sr ←∧) = conSet sr
conSet (∧→ sr) = conSet sr
conSet (sr ←∧→ sr₁) = (conSet sr) ∪ₛ (conSet sr₁)
conSet (sr ←∨) = conSet sr
conSet (∨→ sr) = conSet sr
conSet (sr ←∨→ sr₁) = (conSet sr) ∪ₛ (conSet sr₁)
conSet (sr ←∂) = conSet sr
conSet (∂→ sr) = conSet sr
conSet (sr ←∂→ sr₁) =  (conSet sr) ∪ₛ (conSet sr₁)



-- It is required to fill all the lower levels with the indexes that we are to truck.
-- This is used to fill the initial memory of SetLLRem

fillAllLowerRem : ∀{i u} → ∀ ll → SetLLRem {i} {u} ll ll
fillAllLowerRem ll = fillAllLowerRem` ll (λ x → x) where
  fillAllLowerRem` : ∀{i} → ∀{u pll} → ∀ ll → (∀{rll} → IndexLL rll ll → IndexLL rll pll) → SetLLRem {i} {u} pll ll
  fillAllLowerRem` ∅ f = ↓∅ (f ↓)
  fillAllLowerRem` (τ x) f = ↓τ (f ↓)
  fillAllLowerRem` (ll₁ ∧ ll₂) f = (fillAllLowerRem` ll₁ (λ x → f (x ←∧)) ) ←∧→ (fillAllLowerRem` ll₂ (λ x → f (∧→ x)) )
  fillAllLowerRem` (ll₁ ∨ ll₂) f = (fillAllLowerRem` ll₁ (λ x → f (x ←∨))) ←∨→ (fillAllLowerRem` ll₂ (λ x → f (∨→ x)))
  fillAllLowerRem` (ll₁ ∂ ll₂) f = (fillAllLowerRem` ll₁ (λ x → f (x ←∂))) ←∂→ (fillAllLowerRem` ll₂ (λ x → f (∂→ x)))
  fillAllLowerRem` (call x) f =  ↓c (f ↓)



delRem : ∀{i} → ∀{u ll pll q} → SetLLRem {i} pll ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic i)
      → MSetLLRem {i} pll (replLL ll ind rll)
delRem s ↓ rll = ∅
delRem (s ←∧) (ind ←∧) rll with (delRem s ind rll)
delRem (s ←∧) (ind ←∧) rll | ∅ = ∅
delRem (s ←∧) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧)
delRem (∧→ s) (ind ←∧) rll = ¬∅ (∧→ (s))
delRem (s ←∧→ s₁) (ind ←∧) rll with (delRem s ind rll)
delRem (s ←∧→ s₁) (ind ←∧) rll | ∅ = ¬∅ (∧→ (s₁))
delRem (s ←∧→ s₁) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧→ (s₁))
delRem (s ←∧) (∧→ ind) rll = ¬∅ ((s) ←∧)
delRem (∧→ s) (∧→ ind) rll with (delRem s ind rll)
delRem (∧→ s) (∧→ ind) rll | ∅ = ∅
delRem (∧→ s) (∧→ ind) rll | ¬∅ x = ¬∅ (∧→ x)
delRem (s ←∧→ s₁) (∧→ ind) rll with (delRem s₁ ind rll)
delRem (s ←∧→ s₁) (∧→ ind) rll | ∅ = ¬∅ ((s) ←∧)
delRem (s ←∧→ s₁) (∧→ ind) rll | ¬∅ x = ¬∅ ((s) ←∧→ x)
delRem (s ←∨) (ind ←∨) rll with (delRem s ind rll)
delRem (s ←∨) (ind ←∨) rll | ∅ = ∅
delRem (s ←∨) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨)
delRem (∨→ s) (ind ←∨) rll = ¬∅ (∨→ (s))
delRem (s ←∨→ s₁) (ind ←∨) rll with (delRem s ind rll)
delRem (s ←∨→ s₁) (ind ←∨) rll | ∅ = ¬∅ (∨→ (s₁))
delRem (s ←∨→ s₁) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨→ (s₁))
delRem (s ←∨) (∨→ ind) rll = ¬∅ ((s) ←∨)
delRem (∨→ s) (∨→ ind) rll with (delRem s ind rll)
delRem (∨→ s) (∨→ ind) rll | ∅ = ∅
delRem (∨→ s) (∨→ ind) rll | ¬∅ x = ¬∅ (∨→ x)
delRem (s ←∨→ s₁) (∨→ ind) rll with (delRem s₁ ind rll)
delRem (s ←∨→ s₁) (∨→ ind) rll | ∅ = ¬∅ ((s) ←∨)
delRem (s ←∨→ s₁) (∨→ ind) rll | ¬∅ x = ¬∅ ((s) ←∨→ x)
delRem (s ←∂) (ind ←∂) rll with (delRem s ind rll)
delRem (s ←∂) (ind ←∂) rll | ∅ = ∅
delRem (s ←∂) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂)
delRem (∂→ s) (ind ←∂) rll = ¬∅ (∂→ (s))
delRem (s ←∂→ s₁) (ind ←∂) rll with (delRem s ind rll)
delRem (s ←∂→ s₁) (ind ←∂) rll | ∅ = ¬∅ (∂→ (s₁))
delRem (s ←∂→ s₁) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂→ (s₁))
delRem (s ←∂) (∂→ ind) rll = ¬∅ ((s) ←∂)
delRem (∂→ s) (∂→ ind) rll with (delRem s ind rll)
delRem (∂→ s) (∂→ ind) rll | ∅ = ∅
delRem (∂→ s) (∂→ ind) rll | ¬∅ x = ¬∅ (∂→ x)
delRem (s ←∂→ s₁) (∂→ ind) rll with (delRem s₁ ind rll)
delRem (s ←∂→ s₁) (∂→ ind) rll | ∅ = ¬∅ ((s) ←∂)
delRem (s ←∂→ s₁) (∂→ ind) rll | ¬∅ x = ¬∅ ((s) ←∂→ x)

mdelRem : ∀{i} → ∀{u ll pll q} → MSetLLRem {i} pll ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic i)
      → MSetLLRem {i} pll (replLL ll ind rll)
mdelRem ∅ ind rll = ∅
mdelRem (¬∅ x) ind rll = delRem x ind rll




-- If we tranform the linear logic tree, we need to tranform the SetLLRem as well.
tranRem : ∀{i} → ∀{u pll ll rll} → SetLLRem {i} pll ll → (tr : LLTr {i} {u} rll ll)
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
itranRem : ∀{i} → ∀{u ll rll pll vll} → SetLLRem {i} pll ll → (ind : IndexLL {i} {u} vll ll) → (tr : LLTr rll vll)
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


truncSetLLRem : ∀{i} → ∀{u ll pll q} → MSetLLRem {i} pll ll → (ind : IndexLL {i} {u} q ll) → MSetLLRem {i} pll q
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


extendRem : ∀{i u oll} → ∀{ll pll} → IndexLL {i} {u} pll ll → SetLLRem {i} oll pll → SetLLRem oll ll
extendRem ↓ sr = sr
extendRem (ind ←∧) sr = (extendRem ind sr) ←∧
extendRem (∧→ ind) sr = ∧→ (extendRem ind sr)
extendRem (ind ←∨) sr = (extendRem ind sr) ←∨
extendRem (∨→ ind) sr = ∨→ (extendRem ind sr)
extendRem (ind ←∂) sr = (extendRem ind sr) ←∂
extendRem (∂→ ind) sr = ∂→ (extendRem ind sr)

replaceRem : ∀{i u oll} → ∀{ll pll rll} → (ind : IndexLL {i} {u} pll ll) → SetLLRem {i} oll rll → SetLLRem oll ll → SetLLRem oll (replLL ll ind rll)
replaceRem ↓ esr sr = esr
replaceRem {rll = rll} (ind ←∧) esr (sr ←∧) = replaceRem ind esr sr ←∧
replaceRem {rll = rll} (ind ←∧) esr (∧→ sr) = (extendRem (updInd rll ind) esr) ←∧→ sr
replaceRem {rll = rll} (ind ←∧) esr (sr ←∧→ sr₁) = (replaceRem ind esr sr) ←∧→ sr₁
replaceRem {rll = rll} (∧→ ind) esr (sr ←∧) = sr ←∧→ (extendRem (updInd rll ind) esr)
replaceRem {rll = rll} (∧→ ind) esr (∧→ sr) = ∧→ replaceRem ind esr sr
replaceRem {rll = rll} (∧→ ind) esr (sr ←∧→ sr₁) = sr ←∧→ replaceRem ind esr sr₁
replaceRem {rll = rll} (ind ←∨) esr (sr ←∨) = replaceRem ind esr sr ←∨
replaceRem {rll = rll} (ind ←∨) esr (∨→ sr) = (extendRem (updInd rll ind) esr) ←∨→ sr
replaceRem {rll = rll} (ind ←∨) esr (sr ←∨→ sr₁) = (replaceRem ind esr sr) ←∨→ sr₁
replaceRem {rll = rll} (∨→ ind) esr (sr ←∨) = sr ←∨→ (extendRem (updInd rll ind) esr)
replaceRem {rll = rll} (∨→ ind) esr (∨→ sr) = ∨→ replaceRem ind esr sr
replaceRem {rll = rll} (∨→ ind) esr (sr ←∨→ sr₁) = sr ←∨→ replaceRem ind esr sr₁
replaceRem {rll = rll} (ind ←∂) esr (sr ←∂) = replaceRem ind esr sr ←∂
replaceRem {rll = rll} (ind ←∂) esr (∂→ sr) = (extendRem (updInd rll ind) esr) ←∂→ sr
replaceRem {rll = rll} (ind ←∂) esr (sr ←∂→ sr₁) = (replaceRem ind esr sr) ←∂→ sr₁
replaceRem {rll = rll} (∂→ ind) esr (sr ←∂) = sr ←∂→ (extendRem (updInd rll ind) esr)
replaceRem {rll = rll} (∂→ ind) esr (∂→ sr) = ∂→ replaceRem ind esr sr
replaceRem {rll = rll} (∂→ ind) esr (sr ←∂→ sr₁) = sr ←∂→ replaceRem ind esr sr₁

mreplaceRem : ∀{i u oll} → ∀{ll pll rll} → (ind : IndexLL {i} {u} pll ll) → MSetLLRem {i} oll rll → MSetLLRem oll ll → MSetLLRem oll (replLL ll ind rll)
mreplaceRem ind ∅ ∅ = ∅
mreplaceRem {ll = ll} {pll = pll} {rll = rll} ind ∅ (¬∅ x) = delRem x ind rll
mreplaceRem {rll = rll} ind (¬∅ x) ∅ = ¬∅ (extendRem (updInd rll ind) x)
mreplaceRem ind (¬∅ x) (¬∅ x₁) = ¬∅ (replaceRem ind x x₁)


projToSetLL : {i : Size} → ∀{u} → {pll : LinLogic i {u}} → {ll : LinLogic i {u}} → SetLLRem {i} {u} pll ll → SetLL ll 
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

projToMSetLL : {i : Size} → ∀{u} → {pll : LinLogic i {u}} → {ll : LinLogic i {u}} → MSetLLRem {i} {u} pll ll → MSetLL ll 
projToMSetLL ∅ = ∅
projToMSetLL (¬∅ x) = ¬∅ (projToSetLL x)

oneElemRem : {i : Size} → ∀{u} → {pll : LinLogic i {u}} → {ll : LinLogic i {u}} → SetLLRem {i} {u} pll ll →  Σ (LinLogic i {u}) (λ rll → IndexLL rll pll)
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


complem¬↓⇒¬∅ : {i : Size} → ∀{u} → {pll : LinLogic i {u}} → {ll : LinLogic i {u}}
                 → (ms : MSetLL ll) → (msr : MSetLLRem {i} {u} pll ll) → (ms ∪ₘₛ (projToMSetLL msr)) ≡ (¬∅ ↓)
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
