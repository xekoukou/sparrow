module SetLL where

open import Common hiding (_≤_)
open import LinLogic
-- open import LinLogicProp
open import IndexLLProp -- hiding (tran)
import Data.List
open import Relation.Binary.PropositionalEquality
import Data.Product






data SetLL {i : Size} {u} : LinLogic i {u} → Set where
  ↓     : ∀{ll}                          → SetLL ll
  sic   : ∀{l r} → {il : LLCT} → (ds : IndexLLCT) → SetLL (pickLL ds l r) → SetLL (l < il > r)
  sbc   : ∀{l r} → {il : LLCT} → SetLL l → SetLL r → SetLL (l < il > r)


-- A possibly empty set of nodes in a Linear Logic tree. 
data MSetLL {i : Size} {u} : LinLogic i {u} → Set where
  ∅   : ∀{ll}            → MSetLL ll
  ¬∅  : ∀{ll} → SetLL ll → MSetLL ll



mapₛ : ∀{i u ll1 ll2} → (SetLL {i} {u} ll1 → SetLL {i} {u} ll2) → (MSetLL ll1 → MSetLL ll2)
mapₛ f ∅ = ∅
mapₛ f (¬∅ x) = ¬∅ (f x)


pickLLₛ : ∀{i u l r} → ∀ d → SetLL {i} {u} l → SetLL r → SetLL (pickLL d l r)
pickLLₛ ic← a b = a
pickLLₛ ic→ a b = b

~ₛ : ∀{i u l r} → ∀ d → SetLL {i} {u} (pickLL d l r) → SetLL (pickLL (~ict d) r l)
~ₛ ic← s = s
~ₛ ic→ s = s

-- -- sl-ext : ∀{i u ll tll ic} → SetLL {i} {u} (expLLT {ll = ll} ic tll) → MSetLL ll
-- -- sl-ext {ic = ic←∧} ↓ = ¬∅ ↓
-- -- sl-ext {ic = ic←∧} (s ←∧) = ¬∅ s
-- -- sl-ext {ic = ic←∧} (∧→ s) = ∅
-- -- sl-ext {ic = ic←∧} (s ←∧→ s₁) = ¬∅ s
-- -- sl-ext {ic = ic∧→} ↓ = ¬∅ ↓
-- -- sl-ext {ic = ic∧→} (s ←∧) = ∅
-- -- sl-ext {ic = ic∧→} (∧→ s) = ¬∅ s
-- -- sl-ext {ic = ic∧→} (s ←∧→ s₁) = ¬∅ s₁
-- -- sl-ext {ic = ic←∨} ↓ = ¬∅ ↓
-- -- sl-ext {ic = ic←∨} (s ←∨) = ¬∅ s
-- -- sl-ext {ic = ic←∨} (∨→ s) = ∅
-- -- sl-ext {ic = ic←∨} (s ←∨→ s₁) = ¬∅ s
-- -- sl-ext {ic = ic∨→} ↓ = ¬∅ ↓
-- -- sl-ext {ic = ic∨→} (s ←∨) = ∅
-- -- sl-ext {ic = ic∨→} (∨→ s) = ¬∅ s
-- -- sl-ext {ic = ic∨→} (s ←∨→ s₁) = ¬∅ s₁
-- -- sl-ext {ic = ic←∂} ↓ = ¬∅ ↓
-- -- sl-ext {ic = ic←∂} (s ←∂) = ¬∅ s
-- -- sl-ext {ic = ic←∂} (∂→ s) = ∅
-- -- sl-ext {ic = ic←∂} (s ←∂→ s₁) = ¬∅ s
-- -- sl-ext {ic = ic∂→} ↓ = ¬∅ ↓
-- -- sl-ext {ic = ic∂→} (s ←∂) = ∅
-- -- sl-ext {ic = ic∂→} (∂→ s) = ¬∅ s
-- -- sl-ext {ic = ic∂→} (s ←∂→ s₁) = ¬∅ s₁

-- -- sl-spec : ∀{i u ll tll ic} → SetLL {i} {u} ll → MSetLL tll → SetLL {i} {u} (expLLT {ll = ll} ic tll)
-- -- sl-spec {ic = ic←∧} s ∅ = s ←∧
-- -- sl-spec {ic = ic←∧} s (¬∅ x) = s ←∧→ x
-- -- sl-spec {ic = ic∧→} s ∅ = ∧→ s
-- -- sl-spec {ic = ic∧→} s (¬∅ x) = x ←∧→ s
-- -- sl-spec {ic = ic←∨} s ∅ = s ←∨
-- -- sl-spec {ic = ic←∨} s (¬∅ x) = s ←∨→ x
-- -- sl-spec {ic = ic∨→} s ∅ = ∨→ s
-- -- sl-spec {ic = ic∨→} s (¬∅ x) = x ←∨→ s
-- -- sl-spec {ic = ic←∂} s ∅ = s ←∂
-- -- sl-spec {ic = ic←∂} s (¬∅ x) = s ←∂→ x
-- -- sl-spec {ic = ic∂→} s ∅ = ∂→ s
-- -- sl-spec {ic = ic∂→} s (¬∅ x) = x ←∂→ s




mutual

  ∪ₛ-abs : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i} {ds ds₁} →
         SetLL (pickLL ds l r) →
         SetLL (pickLL ds₁ l r) → Dec (ds ≡ ds₁) → SetLL (l < il > r)
  ∪ₛ-abs {ds = ds} a b (yes refl) = sic ds (a ∪ₛ b)
  ∪ₛ-abs {ds = ic←} {ic←} a b (no ¬p) = ⊥-elim (¬p refl)
  ∪ₛ-abs {ds = ic←} {ic→} a b (no ¬p) = sbc a b
  ∪ₛ-abs {ds = ic→} {ic←} a b (no ¬p) = sbc b a
  ∪ₛ-abs {ds = ic→} {ic→} a b (no ¬p) = ⊥-elim (¬p refl) 

  _∪ₛ_ : ∀{i u ll} → SetLL {i} {u} ll → SetLL ll → SetLL ll
  ↓ ∪ₛ b = ↓
  sic ds a ∪ₛ ↓ = ↓
  sic ds a ∪ₛ sic ds₁ b = ∪ₛ-abs a b (isEqICT ds ds₁)
  sic ic← a ∪ₛ sbc b b₁ = sbc (a ∪ₛ b) b₁
  sic ic→ a ∪ₛ sbc b b₁ = sbc b (a ∪ₛ b₁)
  sbc a a₁ ∪ₛ ↓ = ↓
  sbc a a₁ ∪ₛ sic ic← b = sbc (a ∪ₛ b) a₁
  sbc a a₁ ∪ₛ sic ic→ b = sbc a (a₁ ∪ₛ b)
  sbc a a₁ ∪ₛ sbc b b₁ = sbc (a ∪ₛ b) (a₁ ∪ₛ b₁)
  

_∪ₘₛ_ : ∀{i u} → {ll : LinLogic i {u}} → MSetLL ll → MSetLL ll → MSetLL ll
_∪ₘₛ_ ∅ ∅            = ∅
_∪ₘₛ_ ∅ (¬∅ s)       = ¬∅ s
_∪ₘₛ_ (¬∅ fs) ∅      = ¬∅ fs
_∪ₘₛ_ (¬∅ fs) (¬∅ s) = ¬∅ (fs ∪ₛ s)



sbcm : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i} →
          MSetLL l → MSetLL r → MSetLL (l < il > r)
sbcm ∅ ∅ = ∅
sbcm ∅ (¬∅ b)= ¬∅ (sic ic→ b)
sbcm (¬∅ x) ∅ = ¬∅ (sic ic← x)
sbcm (¬∅ x) (¬∅ b) = ¬∅ (sbc x b)

∩ₛ-abs1 : ∀ {ds i u} {l : LinLogic i {u}} {il} {r : LinLogic i} →
          MSetLL (pickLL ds l r) → MSetLL (l < il > r)
∩ₛ-abs1 ∅ = ∅
∩ₛ-abs1 {ds} (¬∅ x) = ¬∅ (sic ds x)

mutual

  ∩ₛ-abs : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i} {ds ds₁} →
           SetLL (pickLL ds l r) →
           SetLL (pickLL ds₁ l r) → Dec (ds ≡ ds₁) → MSetLL (l < il > r)
  ∩ₛ-abs {ds = ds} {.ds} a b (yes refl) = ∩ₛ-abs1 {ds} (a ∩ₛ b)
  ∩ₛ-abs {ds = ds} {ds₁} a b (no ¬p) = ∅

  _∩ₛ_ : ∀{i u ll} → SetLL {i} {u} ll → SetLL ll → MSetLL ll
  ↓ ∩ₛ b = ¬∅ b
  sic ds a ∩ₛ ↓ = ¬∅ (sic ds a)
  sic ds a ∩ₛ sic ds₁ b = ∩ₛ-abs a b (isEqICT ds ds₁)
  sic ic← a ∩ₛ sbc b b₁ = sbcm (a ∩ₛ b) (¬∅ b₁)
  sic ic→ a ∩ₛ sbc b b₁ = sbcm (¬∅ b) (a ∩ₛ b₁)
  sbc a a₁ ∩ₛ ↓ = ¬∅ (sbc a a₁)
  sbc a a₁ ∩ₛ sic ic← b = sbcm (a ∩ₛ b) (¬∅ a₁)
  sbc a a₁ ∩ₛ sic ic→ b = sbcm (¬∅ a) (a₁ ∩ₛ b)
  sbc a a₁ ∩ₛ sbc b b₁ = sbcm (a ∩ₛ b) (a₁ ∩ₛ b₁)


fillAllLower : ∀{i u} → ∀ {ll} → SetLL {i} {u} ll
fillAllLower {ll = ∅} = ↓
fillAllLower {ll = (τ _)} = ↓
fillAllLower {ll = abs} = ↓
fillAllLower {ll = (call _)} = ↓
fillAllLower {ll = (_ < _ > _)} = sbc fillAllLower fillAllLower



complLₛ-abs : ∀ {i u} {l r : LinLogic i {u}} {il ds} →
              MSetLL (pickLL ds l r) → MSetLL (l < il > r)
complLₛ-abs {ds = ds} ∅ = ¬∅ (sic ds fillAllLower)
complLₛ-abs {ds = ic←} (¬∅ x) = ¬∅ (sbc x fillAllLower)
complLₛ-abs {ds = ic→} (¬∅ x) = ¬∅ (sbc fillAllLower x)

complLₛ : ∀{i u ll} → SetLL {i} {u} ll → MSetLL ll
complLₛ ↓ = ∅
complLₛ (sic ds s) = complLₛ-abs {ds = ds} (complLₛ s)
complLₛ (sbc s s₁) = sbcm (complLₛ s) (complLₛ s₁)




del-abs : ∀ {i u} {l r : LinLogic i {u}} {il} {q : LinLogic i} {d}
            {ind : IndexLL q (pickLL d l r)} {rll : LinLogic i} →
          MSetLL (replLL ind rll) →
          MSetLL
          (pickLL d (replLL ind rll) l < il > pickLL d r (replLL ind rll))
del-abs {d = ic←} is = sbcm is (¬∅ ↓)
del-abs {d = ic→} is = sbcm (¬∅ ↓) is



mutual

  del-abs1 : ∀ {i u} {l r q : LinLogic i {u}} {ds d} →
             SetLL (pickLL ds l r) →
             (ind : IndexLL q (pickLL d l r)) →
             Dec (ds ≡ d) →
             ∀ {il} {rll : LinLogic i} →
             MSetLL
             (pickLL d (replLL ind rll) l < il > pickLL d r (replLL ind rll))
  del-abs1 {d = d} s ind (yes refl) {rll = rll} = mapₛ (sic d) (subst MSetLL (trans (pickLL-id d (replLL ind rll)) (sym (pickLL-eq d pickLL pickLL _ _ _ _ refl refl))) (del s ind {rll}))
  del-abs1 s ind (no ¬p) = ∅
  
  
  -- Deletes an index if it is present, otherwise does nothing.
  del : ∀{i u ll q} → SetLL ll → (ind : IndexLL {i} {u} q ll) → {rll : LinLogic i}
        → MSetLL (replLL ind rll)
  del s ↓ = ∅
  del ↓ (ic d ind) {rll} = del-abs {d = d} {ind} (del ↓ ind {rll})
  del (sic ds s) (ic d ind) = del-abs1 s ind (isEqICT ds d)
  del (sbc s s₁) (ic ic← ind) = sbcm (del s ind) (¬∅ s₁)
  del (sbc s s₁) (ic ic→ ind) = sbcm (¬∅ s) (del s₁ ind)





s-extend : ∀{i u ll rll} → (ind : IndexLL {i} {u} rll ll) → SetLL {i} rll → SetLL ll
s-extend {ll = ll} {.ll} ↓ s = s
s-extend {ll = .(_ < _ > _)} {rll} (ic d ind) s = sic d (s-extend ind s)

s-extendG : ∀{i u ll q} → ∀{rll} → (ind : IndexLL {i} {u} q ll) → SetLL {i} rll → SetLL (replLL ind rll)
s-extendG ind s = s-extend (ind-rpl↓2 ind (a≤ᵢb-morph ind ind)) s


mutual

  replacePartOf-abs : ∀ {i u} {l r rll : LinLogic i {u}} {ds d} →
                       SetLL (pickLL ds l r) →
                       SetLL rll →
                       IndexLL rll (pickLL d l r) →
                       Dec (ds ≡ d) → ∀ {il} → SetLL (l < il > r)
  replacePartOf-abs {ds = ds} a b ind (yes refl) = sic ds (replacePartOf a to b at ind)
  replacePartOf-abs {ds = ic←} {ic←} a b ind (no ¬p) = ⊥-elim (¬p refl)
  replacePartOf-abs {ds = ic←} {ic→} a b ind (no ¬p) = sbc a (s-extend ind b)
  replacePartOf-abs {ds = ic→} {ic←} a b ind (no ¬p) = sbc (s-extend ind b) a
  replacePartOf-abs {ds = ic→} {ic→} a b ind (no ¬p) = ⊥-elim (¬p refl)



  replacePartOf_to_at_ : ∀{i u ll rll} → SetLL ll → SetLL {i} rll → (ind : IndexLL {i} {u} rll ll)
                 → SetLL ll
  replacePartOf a to b at ↓ = b
  replacePartOf ↓ to b at ic d ind = sic d (replacePartOf ↓ to b at ind)
  replacePartOf sic ds a to b at ic d ind = replacePartOf-abs a b ind (isEqICT ds d)
  replacePartOf sbc a a₁ to b at ic ic← ind = sbc (replacePartOf a to b at ind) a₁
  replacePartOf sbc a a₁ to b at ic ic→ ind = sbc a (replacePartOf a₁ to b at ind)


-- Add a node to an empty set (and potentially replace the linear logic sub-tree).
∅-add : ∀{i u ll rll} → (ind : IndexLL {i} {u} rll ll) 
        → SetLL ll
∅-add ind = s-extend ind ↓

-- Add a node to an empty set (and potentially replace the linear logic sub-tree).
∅-addG : ∀{i u ll rll} → (ind : IndexLL {i} {u} rll ll) → {nrll : LinLogic i}
        → SetLL (replLL ind nrll)
∅-addG ind = ∅-add (ind-rpl↓2 ind (a≤ᵢb-morph ind ind))


  -- Add a node to a set (and potentially replace the linear logic sub-tree).
add : ∀{i u ll q} → SetLL ll → (ind : IndexLL {i} {u} q ll)
        → SetLL ll
add s ind = replacePartOf s to ↓ at ind


madd : ∀{i u ll q} → MSetLL ll → (ind : IndexLL {i} {u} q ll)
      → MSetLL ll
madd ∅ ind = ¬∅ (∅-add ind)
madd (¬∅ x) ind = ¬∅ (add x ind)

mutual

  replacePartOfG-abs : ∀ {i u} {ll q rll : LinLogic i {u}}
                       {ind : IndexLL q ll} →
                     MSetLL (replLL ind rll) →
                     SetLL rll → IndexLL rll (replLL ind rll) → SetLL (replLL ind rll)
  replacePartOfG-abs ∅ b mind = s-extend mind b
  replacePartOfG-abs (¬∅ x) b mind = replacePartOf x to b at mind

  replacePartOfG_to_at_ : ∀{i u ll q} → ∀{rll} → SetLL ll → SetLL {i} rll → (ind : IndexLL {i} {u} q ll)
               → SetLL (replLL ind rll)
  replacePartOfG_to_at_ {rll = rll} a b ind = replacePartOfG-abs {ind = ind} (del a ind {rll}) b (ind-rpl↓2 ind (a≤ᵢb-morph ind ind {frll = rll}))


  -- Add a node to a set (and potentially replace the linear logic sub-tree).
addG : ∀{i u ll q} → SetLL ll → (ind : IndexLL {i} {u} q ll) → {rll : LinLogic i}
        → SetLL (replLL ind rll)
addG s ind {rll} = replacePartOfG s to ↓ at ind




mreplacePartOf_to_at_ : ∀{i u ll rll} → MSetLL ll → MSetLL {i} rll → (ind : IndexLL {i} {u} rll ll)
          → MSetLL ll
mreplacePartOf ∅ to mb at ind = mapₛ (s-extend ind) mb
mreplacePartOf ¬∅ x to ∅ at ind = subst MSetLL (replLL-id ind) (del x ind)
mreplacePartOf ¬∅ x to ¬∅ x₁ at ind = ¬∅ (replacePartOf x to x₁ at ind)



mreplacePartOfG_to_at_ : ∀{i u ll q} → ∀{rll} → MSetLL ll → MSetLL {i} rll → (ind : IndexLL {i} {u} q ll)
          → MSetLL (replLL ind rll)
mreplacePartOfG_to_at_ {rll = rll} ∅ mb ind = mapₛ (s-extendG ind) mb
mreplacePartOfG ¬∅ x to ∅ at ind = del x ind
mreplacePartOfG ¬∅ x to ¬∅ x₁ at ind = mreplacePartOf (del x ind) to (¬∅ x₁) at (ind-rpl↓2 ind (a≤ᵢb-morph ind ind))



-- -- module _ {u} where

-- --   open Relation.Binary.PropositionalEquality

-- -- --  open import Data.Maybe
-- --   open Data.Product
-- -- --  open import Category.Monad
-- -- --  open RawMonad {f = lsuc u} (monad)

-- -- -- -- This might not be used. 
-- -- --  setToIndex : ∀{i ll} → SetLL {i} {u} ll → Maybe $ Σ (LinLogic i {u}) (λ x → IndexLL x ll)
-- -- --  setToIndex {ll = ll} ↓ = just (ll , ↓)
-- -- --  setToIndex (s ←∧) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ind ←∧) })
-- -- --  setToIndex (∧→ s) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ∧→ ind) })
-- -- --  setToIndex (s ←∧→ s₁) = nothing
-- -- --  setToIndex (s ←∨) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ind ←∨) })
-- -- --  setToIndex (∨→ s) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ∨→ ind) })
-- -- --  setToIndex (s ←∨→ s₁) = nothing
-- -- --  setToIndex (s ←∂) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ind ←∂) })
-- -- --  setToIndex (∂→ s) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ∂→ ind) })
-- -- --  setToIndex (s ←∂→ s₁) = nothing
-- -- --  
-- -- --  msetToIndex : ∀{i ll} → MSetLL {i} {u} ll → Maybe $ Σ (LinLogic i {u}) (λ x → IndexLL x ll)
-- -- --  msetToIndex ∅ = nothing
-- -- --  msetToIndex (¬∅ x) = setToIndex x
-- -- --

-- -- -- This is used.
-- --   pickOne : ∀{i ll} → SetLL {i} {u} ll → Σ (LinLogic i {u}) (λ x → IndexLL x ll)
-- --   pickOne {ll = ll} ↓ = ll , ↓
-- --   pickOne (s ←∧) = (rll , ind ←∧) where
-- --     n = pickOne s
-- --     rll = proj₁ n
-- --     ind = proj₂ n
-- --   pickOne (∧→ s) = (rll , ∧→ ind) where
-- --     n = pickOne s
-- --     rll = proj₁ n
-- --     ind = proj₂ n
-- --   pickOne (s ←∧→ s₁) = rll , ind ←∧ where
-- --     n = pickOne s
-- --     rll = proj₁ n
-- --     ind = proj₂ n
-- --   pickOne (s ←∨) = rll , ind ←∨ where
-- --     n = pickOne s
-- --     rll = proj₁ n
-- --     ind = proj₂ n
-- --   pickOne (∨→ s) = rll , ∨→ ind where
-- --     n = pickOne s
-- --     rll = proj₁ n
-- --     ind = proj₂ n
-- --   pickOne (s ←∨→ s₁) = rll , ind ←∨ where
-- --     n = pickOne s
-- --     rll = proj₁ n
-- --     ind = proj₂ n
-- --   pickOne (s ←∂) = rll , ind ←∂ where
-- --     n = pickOne s
-- --     rll = proj₁ n
-- --     ind = proj₂ n
-- --   pickOne (∂→ s) = rll , ∂→ ind where
-- --     n = pickOne s
-- --     rll = proj₁ n
-- --     ind = proj₂ n
-- --   pickOne (s ←∂→ s₁) = rll , ind ←∂ where
-- --     n = pickOne s
-- --     rll = proj₁ n
-- --     ind = proj₂ n

-- --   pickadd-id : ∀{i pll ll} → (ind : IndexLL {i} {u} pll ll) → (pickOne (subst (λ x → SetLL x) (replLL-id ll ind pll refl) (∅-add ind pll))) ≡ (pll , ind)
-- --   pickadd-id ↓ = refl
-- --   pickadd-id {pll = pll} {ll = li ∧ ri} (ind ←∧) with replLL li ind pll | replLL-id li ind pll refl | oa | pickadd-id ind where
-- --     oa = ∅-add ind pll
-- --   pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∧ ri} (.(proj₂ (pickOne oa)) ←∧) | .li | refl | oa | refl = refl
-- --   pickadd-id {pll = pll} {ll = li ∧ ri} (∧→ ind) with replLL ri ind pll | replLL-id ri ind pll refl | oa | pickadd-id ind where
-- --     oa = ∅-add ind pll
-- --   pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∧ ri} (∧→ .(proj₂ (pickOne oa))) | .ri | refl | oa | refl = refl
-- --   pickadd-id {pll = pll} {ll = li ∨ ri} (ind ←∨) with replLL li ind pll | replLL-id li ind pll refl | oa | pickadd-id ind where
-- --     oa = ∅-add ind pll
-- --   pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∨ ri} (.(proj₂ (pickOne oa)) ←∨) | .li | refl | oa | refl = refl
-- --   pickadd-id {pll = pll} {ll = li ∨ ri} (∨→ ind) with replLL ri ind pll | replLL-id ri ind pll refl | oa | pickadd-id ind where
-- --     oa = ∅-add ind pll
-- --   pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∨ ri} (∨→ .(proj₂ (pickOne oa))) | .ri | refl | oa | refl = refl
-- --   pickadd-id {pll = pll} {ll = li ∂ ri} (ind ←∂) with replLL li ind pll | replLL-id li ind pll refl | oa | pickadd-id ind where
-- --     oa = ∅-add ind pll
-- --   pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∂ ri} (.(proj₂ (pickOne oa)) ←∂) | .li | refl | oa | refl = refl
-- --   pickadd-id {pll = pll} {ll = li ∂ ri} (∂→ ind) with replLL ri ind pll | replLL-id ri ind pll refl | oa | pickadd-id ind where
-- --     oa = ∅-add ind pll
-- --   pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∂ ri} (∂→ .(proj₂ (pickOne oa))) | .ri | refl | oa | refl = refl


isEqₛ-abs2 : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i}
               {a : SetLL l} {a₁ : SetLL r} {b : SetLL l} {b₁ : SetLL r} →
             Dec (a ≡ b) → Dec (a₁ ≡ b₁) → Dec (sbc {il = il} a a₁ ≡ sbc b b₁)
isEqₛ-abs2 (yes refl) (yes refl) = yes refl
isEqₛ-abs2 (yes p) (no ¬p) = no λ { refl → ¬p refl}
isEqₛ-abs2 (no ¬p) deq1 = no λ { refl → ¬p refl}

isEqₛ-abs1 : ∀ {ds i u} {l : LinLogic i {u}} {il} {r : LinLogic i}
               {a b : SetLL (pickLL ds l r)} →
             Dec (a ≡ b) → Dec (sic {il = il} ds a ≡ sic ds b)
isEqₛ-abs1 (yes refl) = yes refl
isEqₛ-abs1 (no ¬p) = no λ { refl → ¬p refl}

mutual
  
  isEqₛ-abs : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i} {ds ds₁}
                (a : SetLL (pickLL ds l r)) (b : SetLL (pickLL ds₁ l r)) →
              Dec (ds ≡ ds₁) → Dec (sic {il = il} ds a ≡ sic ds₁ b)
  isEqₛ-abs a b (yes refl) = isEqₛ-abs1 (isEqₛ a b)
  isEqₛ-abs a b (no ¬p) = no λ { refl → ¬p refl}
  
  -- Decidable Equality
  isEqₛ : {i : Size} → ∀{u} → {ll : LinLogic i {u}} → (a : SetLL ll) → (b : SetLL ll) → Dec (a ≡ b)
  isEqₛ ↓ ↓ = yes refl
  isEqₛ ↓ (sic ds b) = no (λ ())
  isEqₛ ↓ (sbc b b₁) = no (λ ())
  isEqₛ (sic ds a) ↓ = no (λ ())
  isEqₛ (sic ds a) (sic ds₁ b) = isEqₛ-abs a b (isEqICT ds ds₁)
  isEqₛ (sic ds a) (sbc b b₁) = no (λ ())
  isEqₛ (sbc a a₁) ↓ = no (λ ())
  isEqₛ (sbc a a₁) (sic ds b) = no (λ ())
  isEqₛ (sbc a a₁) (sbc b b₁) = isEqₛ-abs2 (isEqₛ a b) (isEqₛ a₁ b₁)



isEqMₛ-abs : ∀ {i u} {ll : LinLogic i {u}} {x y : SetLL ll} →
             Dec (x ≡ y) → Dec (¬∅ x ≡ ¬∅ y)
isEqMₛ-abs (yes refl) = yes refl
isEqMₛ-abs (no ¬p) = no λ { refl → ¬p refl}

isEqMₛ : {i : Size} → ∀{u} → {ll : LinLogic i {u}} → (a : MSetLL ll) → (b : MSetLL ll) → Dec (a ≡ b)
isEqMₛ ∅ ∅ = yes refl
isEqMₛ ∅ (¬∅ x) = no (λ ())
isEqMₛ (¬∅ x) ∅ = no (λ ())
isEqMₛ (¬∅ x) (¬∅ y) = isEqMₛ-abs (isEqₛ x y)


contruct-abs : ∀ {i u} {l r : LinLogic i {u}} {il} →
               SetLL l → SetLL r → SetLL (l < il > r)
contruct-abs ↓ ↓ = ↓
contruct-abs a b = sbc a b


-- If two adjacent nodes exist in the set, the higher node is in the set.
-- We contruct the set.
contruct : ∀{i u ll} → SetLL {i} {u} ll → SetLL ll
contruct ↓ = ↓
contruct (sic ds s) = sic ds (contruct s)
contruct (sbc s s₁) = contruct-abs (contruct s) (contruct s₁)



mcontruct : ∀{i u ll} → MSetLL {i} {u} ll → MSetLL ll
mcontruct ∅ = ∅
mcontruct (¬∅ x) = ¬∅ $ contruct x



contr$fillallL≡↓-abs : ∀ {i u} {ll : LinLogic i {u}} {il}
                       {ll₁ : LinLogic i {u}} →
                       ∀{x y} →
                       x ≡ ↓ →
                       y ≡ ↓ →
                       contruct-abs {l = ll} {r = ll₁} {il = il} x y ≡ ↓
contr$fillallL≡↓-abs refl refl = refl


contr$fillallL≡↓ : ∀{i u ll} → contruct (fillAllLower {i} {u} {ll = ll}) ≡ ↓
contr$fillallL≡↓ {ll = ∅} = refl
contr$fillallL≡↓ {ll = τ x} = refl
contr$fillallL≡↓ {ll = abs} = refl
contr$fillallL≡↓ {ll = call x} = refl
contr$fillallL≡↓ {ll = ll < x > ll₁} = contr$fillallL≡↓-abs (contr$fillallL≡↓ {ll = ll}) (contr$fillallL≡↓ {ll = ll₁})




-- -- -- This might not be used now but it might be used in the future, when I finish implementing the cut.

-- -- -- Resource-aware contruction used in cuttable. A node will only receive one resource from ∂ or ∨, by their semantic definition,
-- -- -- thus here we contruct based on whether the specific subtree has all the possible resources that it could
-- -- -- get from the network.
-- -- res-contruct : ∀{i u ll} → SetLL {i} {u} ll → SetLL ll
-- -- res-contruct ↓          = ↓
-- -- res-contruct (x ←∧)     = (res-contruct x) ←∧
-- -- res-contruct (∧→ x)     = ∧→ (res-contruct x)
-- -- res-contruct (x ←∧→ x₁) with res-contruct x | res-contruct x₁
-- -- ... | ↓ | ↓ = ↓
-- -- {-# CATCHALL #-}
-- -- ... | g | r = (g ←∧→ r)
-- -- res-contruct (x ←∨) with res-contruct x
-- -- ... | ↓ = ↓
-- -- {-# CATCHALL #-}
-- -- ... | g = (g ←∨)
-- -- res-contruct (∨→ x) with res-contruct x 
-- -- ... | ↓ = ↓
-- -- {-# CATCHALL #-}
-- -- ... | g = (∨→ g)
-- -- res-contruct (x ←∨→ x₁) with res-contruct x | res-contruct x₁
-- -- ... | ↓ | ↓ = ↓
-- -- {-# CATCHALL #-}
-- -- ... | g | r = (g ←∨→ r)
-- -- res-contruct (x ←∂) with res-contruct x
-- -- ... | ↓ = ↓
-- -- {-# CATCHALL #-}
-- -- ... | g = (g ←∂)
-- -- res-contruct (∂→ x) with res-contruct x
-- -- ... | ↓ = ↓
-- -- {-# CATCHALL #-}
-- -- ... | g = (∂→ g)
-- -- res-contruct (x ←∂→ x₁) with res-contruct x | res-contruct x₁
-- -- ... | ↓ | ↓ = ↓
-- -- {-# CATCHALL #-}
-- -- ... | g | r = (g ←∂→ r)




-- If we transform the linear logic tree, we need to transform the SetLL as well.
tran : ∀ {i u ll rll} → SetLL ll → (tr : LLTr {i} {u} rll ll)
       → SetLL rll
tran s I = s
tran ↓ (cₜᵣ tr) = ↓
tran (sic ds s) (cₜᵣ tr) = tran (sic (~ict ds) (~ₛ ds s)) tr
tran (sbc s s₁) (cₜᵣ tr) = tran (sbc s₁ s) tr
tran ↓ (aₜᵣ tr) = ↓
tran (sic ic← ↓) (aₜᵣ tr) = tran (sbc ↓ (sic ic← ↓)) tr
tran (sic ic← (sic ic← s)) (aₜᵣ tr) = tran (sic ic← s) tr
tran (sic ic← (sic ic→ s)) (aₜᵣ tr) = tran (sic ic→ (sic ic← s)) tr
tran (sic ic← (sbc s s₁)) (aₜᵣ tr) = tran (sbc s (sic ic← s₁)) tr
tran (sic ic→ s) (aₜᵣ tr) = tran (sic ic→ (sic ic→ s)) tr
tran (sbc ↓ s₁) (aₜᵣ tr) = tran (sbc ↓ (sbc ↓ s₁)) tr
tran (sbc (sic ic← s) s₁) (aₜᵣ tr) = tran (sbc s (sic ic→ s₁)) tr
tran (sbc (sic ic→ s) s₁) (aₜᵣ tr) = tran (sic ic→ (sbc s s₁)) tr
tran (sbc (sbc s s₂) s₁) (aₜᵣ tr) = tran (sbc s (sbc s₂ s₁)) tr






-- -- -- Transformations that start from a specific index.
-- -- itran : ∀ {i u ll rll pll} → SetLL ll → (ind : IndexLL {i} {u} pll ll) → (tr : LLTr rll pll)
-- --         → SetLL (replLL ll ind rll)
-- -- itran s ↓ tr                 = tran s tr
-- -- itran ↓ (ind ←∧) tr          = ↓
-- -- itran (s ←∧) (ind ←∧) tr     = itran s ind tr ←∧
-- -- itran (∧→ s) (ind ←∧) tr     = ∧→ s
-- -- itran (s ←∧→ s₁) (ind ←∧) tr = itran s ind tr ←∧→ s₁ 
-- -- itran ↓ (∧→ ind) tr          = ↓
-- -- itran (s ←∧) (∧→ ind) tr     = s ←∧
-- -- itran (∧→ s) (∧→ ind) tr     = ∧→ itran s ind tr
-- -- itran (s ←∧→ s₁) (∧→ ind) tr = s ←∧→ itran s₁ ind tr
-- -- itran ↓ (ind ←∨) tr          = ↓
-- -- itran (s ←∨) (ind ←∨) tr     = itran s ind tr ←∨
-- -- itran (∨→ s) (ind ←∨) tr     = ∨→ s
-- -- itran (s ←∨→ s₁) (ind ←∨) tr = itran s ind tr ←∨→ s₁ 
-- -- itran ↓ (∨→ ind) tr          = ↓
-- -- itran (s ←∨) (∨→ ind) tr     = s ←∨
-- -- itran (∨→ s) (∨→ ind) tr     = ∨→ itran s ind tr
-- -- itran (s ←∨→ s₁) (∨→ ind) tr = s ←∨→ itran s₁ ind tr
-- -- itran ↓ (ind ←∂) tr          = ↓
-- -- itran (s ←∂) (ind ←∂) tr     = itran s ind tr ←∂
-- -- itran (∂→ s) (ind ←∂) tr     = ∂→ s
-- -- itran (s ←∂→ s₁) (ind ←∂) tr = itran s ind tr ←∂→ s₁ 
-- -- itran ↓ (∂→ ind) tr          = ↓
-- -- itran (s ←∂) (∂→ ind) tr     = s ←∂
-- -- itran (∂→ s) (∂→ ind) tr     = ∂→ itran s ind tr
-- -- itran (s ←∂→ s₁) (∂→ ind) tr = s ←∂→ itran s₁ ind tr


mutual

  truncₛ-abs : ∀ {i u} {l r pll : LinLogic i {u}} {ds d} →
             SetLL (pickLL ds l r) →
             IndexLL pll (pickLL d l r) → Dec (ds ≡ d) → MSetLL pll
  truncₛ-abs s ind (yes refl) = truncₛ s ind
  truncₛ-abs s ind (no ¬p) = ∅

  truncₛ : ∀ {i u ll pll} → SetLL ll → (ind : IndexLL {i} {u} pll ll)
                → MSetLL pll
  truncₛ s ↓ = ¬∅ s
  truncₛ ↓ (ic d ind) = ¬∅ ↓
  truncₛ (sic ds s) (ic d ind) = truncₛ-abs s ind (isEqICT ds d)
  truncₛ (sbc s s₁) (ic ic← ind) = truncₛ s ind
  truncₛ (sbc s s₁) (ic ic→ ind) = truncₛ s₁ ind


mutual

  tr-ext⇒id-abs : ∀ {i u} {l r pll : LinLogic i {u}} {d} (s : SetLL pll)
                  (ind : IndexLL pll (pickLL d l r)) (w : Dec (d ≡ d)) →
                  truncₛ-abs (s-extend ind s) ind w ≡ ¬∅ s
  tr-ext⇒id-abs s ind (yes refl) = tr-ext⇒id ind
  tr-ext⇒id-abs s ind (no ¬p) = ⊥-elim (¬p refl)

  tr-ext⇒id : ∀{i u pll ll} → ∀ {s} → (ind : IndexLL {i} {u} pll ll) →  truncₛ (s-extend ind s) ind ≡ ¬∅ s
  tr-ext⇒id ↓ = refl
  tr-ext⇒id {s = s} (ic d ind) = tr-ext⇒id-abs s ind (isEqICT d d)



-- -- module _ where

-- --   open Relation.Binary.PropositionalEquality
-- -- -- TODO Check if we could use tr-ext⇒id to prove this.
-- --   tr-extg⇒id : ∀{i u pll ll rll} → ∀ (s : SetLL rll) → (ind : IndexLL {i} {u} pll ll)
-- --         → let tlind = subst (λ z → IndexLL z (replLL ll ind rll)) (replLL-↓ ind) ((a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind)))
-- --           in truncSetLL (extendg ind s) tlind ≡ ¬∅ s
-- --   tr-extg⇒id s ↓ = refl
-- --   tr-extg⇒id {pll = pll} {rll = rll} s (ind ←∧) with replLL pll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | (a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind)) | tr-extg⇒id s ind
-- --   tr-extg⇒id {pll = pll} {rll = .g} s (ind ←∧) | g | refl | t | is = is
-- --   tr-extg⇒id {pll = pll} {rll = rll} s (∧→ ind) with replLL pll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | (a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind)) | tr-extg⇒id s ind
-- --   tr-extg⇒id {pll = pll} {rll = .g} s (∧→ ind) | g | refl | e | is = is
-- --   tr-extg⇒id {pll = pll} {rll = rll} s (ind ←∨) with replLL pll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | (a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind)) | tr-extg⇒id s ind
-- --   tr-extg⇒id {pll = pll} {rll = .g} s (ind ←∨) | g | refl | t | is = is
-- --   tr-extg⇒id {pll = pll} {rll = rll} s (∨→ ind) with replLL pll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | (a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind)) | tr-extg⇒id s ind
-- --   tr-extg⇒id {pll = pll} {rll = .g} s (∨→ ind) | g | refl | e | is = is
-- --   tr-extg⇒id {pll = pll} {rll = rll} s (ind ←∂) with replLL pll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | (a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind)) | tr-extg⇒id s ind
-- --   tr-extg⇒id {pll = pll} {rll = .g} s (ind ←∂) | g | refl | t | is = is
-- --   tr-extg⇒id {pll = pll} {rll = rll} s (∂→ ind) with replLL pll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | (a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind)) | tr-extg⇒id s ind
-- --   tr-extg⇒id {pll = pll} {rll = .g} s (∂→ ind) | g | refl | e | is = is


mutual

  tr-repl⇒id-abs : ∀ {d} (w : Dec (d ≡ d)) {i u}
                   {l r pll : LinLogic i {u}} {s : SetLL (pickLL d l r)} {ind : IndexLL pll (pickLL d l r)}
                   {vs : SetLL pll} →
                 truncₛ-abs (replacePartOf s to vs at ind) ind w ≡ ¬∅ vs
  tr-repl⇒id-abs (yes refl) {ind = ind} {vs} = tr-repl⇒id ind
  tr-repl⇒id-abs (no ¬p) {ind = ind} {vs} = ⊥-elim (¬p refl)


  tr-repl⇒id-abs1 : ∀ {ds d} (w : Dec (ds ≡ d)) {i u}
                    {l : LinLogic i {u}} {il} {r pll : LinLogic i}
                    {s : SetLL (pickLL ds l r)} {ind : IndexLL pll (pickLL d l r)}
                    {vs : SetLL pll} →
                  truncₛ (replacePartOf-abs s vs ind w {il}) (ic d ind) ≡ ¬∅ vs
  tr-repl⇒id-abs1 {ds} (yes refl) {s = s} {ind} {vs} = tr-repl⇒id-abs (isEqICT ds ds)
  tr-repl⇒id-abs1 {ic←} {ic←} (no ¬p) {s = s} {ind} {vs} = ⊥-elim (¬p refl)
  tr-repl⇒id-abs1 {ic←} {ic→} (no ¬p) {s = s} {ind} {vs} = tr-ext⇒id ind
  tr-repl⇒id-abs1 {ic→} {ic←} (no ¬p) {s = s} {ind} {vs} = tr-ext⇒id ind
  tr-repl⇒id-abs1 {ic→} {ic→} (no ¬p) {s = s} {ind} {vs} = ⊥-elim (¬p refl)



  tr-repl⇒id : ∀{i u ll pll} → {s : SetLL ll} → (ind : IndexLL {i} {u} pll ll)
             → {vs : SetLL pll} 
             → let mx = replacePartOf s to vs at ind in
             truncₛ mx ind ≡ ¬∅ vs
  tr-repl⇒id {s = s} ↓ {vs} = refl
  tr-repl⇒id {s = ↓} (ic d ind) {vs} = tr-repl⇒id-abs (isEqICT d d)
  tr-repl⇒id {s = sic ds s} (ic d ind) {vs} = tr-repl⇒id-abs1 (isEqICT ds d)
  tr-repl⇒id {s = sbc s s₁} (ic ic← ind) {vs} = tr-repl⇒id ind
  tr-repl⇒id {s = sbc s s₁} (ic ic→ ind) {vs} = tr-repl⇒id ind


mutual

  tr-repl⇒idG-abs : ∀ {i u} {ll ell pll : LinLogic i {u}}
                (ind : IndexLL pll ll) {vs : SetLL ell}
                (w : MSetLL (replLL ind ell)) →
             let tind = ind-rpl↓2 ind (a≤ᵢb-morph ind ind) in
              truncₛ
              (replacePartOfG-abs {ind = ind} w vs tind) tind
              ≡ ¬∅ vs
  tr-repl⇒idG-abs ind ∅ = tr-ext⇒id (ind-rpl↓2 ind (a≤ᵢb-morph ind ind))
  tr-repl⇒idG-abs ind (¬∅ x) = tr-repl⇒id (ind-rpl↓2 ind (a≤ᵢb-morph ind ind))


  tr-repl⇒idG : ∀{i u ll ell pll} → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
           → (vs : SetLL ell) 
           → let mx = replacePartOfG s to vs at ind in
             let tind = ind-rpl↓2 ind (a≤ᵢb-morph ind ind) in
           truncₛ mx tind ≡ ¬∅ vs
  tr-repl⇒idG s ind vs = tr-repl⇒idG-abs ind (del s ind)



data _⊂ₛ_ {i : Size} {u} : {ll : LinLogic i {u}} → SetLL ll → SetLL ll → Set where
  instance
    ⊂↓   : ∀{ll s} → _⊂ₛ_ {ll = ll} s ↓
    ⊂sic : ∀{lll llr il d sx sy} → {{ieq : _⊂ₛ_ {ll = pickLL d lll llr} sx sy}} → _⊂ₛ_ {ll = lll < il > llr} (sic d sx) (sic d sy)
    ⊂sbc : ∀{lll llr il slx sly srx sry} → {{ieql : _⊂ₛ_ {ll = lll} slx sly}} → {{ieqr : _⊂ₛ_ {ll = llr} srx sry}} → _⊂ₛ_ {ll = lll < il > llr} (sbc slx srx) (sbc sly sry)
    ⊂dsbc : ∀{lll llr il d sx sly sry} → {{ieq : _⊂ₛ_ sx (pickLLₛ d sly sry)}} → _⊂ₛ_ {ll = lll < il > llr} (sic d sx) (sbc sly sry)


⊂ₛ-ext : ∀{i u pll ll ss} → (ind : IndexLL {i} {u} pll ll) → {s : SetLL pll} → {{rl : ss ⊂ₛ s }} → s-extend ind ss ⊂ₛ s-extend ind s
⊂ₛ-ext ↓ {{rl}} = rl
⊂ₛ-ext (ic d ind) = ⊂sic {{ieq = ⊂ₛ-ext ind}}


instance
  ⊂ₛ-refl : ∀{i u ll} → {s : SetLL {i} {u} ll} → s ⊂ₛ s
  ⊂ₛ-refl {s = ↓} = ⊂↓
  ⊂ₛ-refl {s = sic ds s} = ⊂sic
  ⊂ₛ-refl {s = sbc s s₁} = ⊂sbc




⊂ₛ-trans : ∀{i u ll b c} → {a : SetLL {i} {u} ll} → a ⊂ₛ b → b ⊂ₛ c → a ⊂ₛ c
⊂ₛ-trans x ⊂↓ = ⊂↓
⊂ₛ-trans ⊂sic (⊂sic {{ieq = ieqy}}) = ⊂sic {{ieq = ⊂ₛ-trans it ieqy}}
⊂ₛ-trans ⊂sbc (⊂sbc {{ieql = ieql}} {{ieqr = ieqr}}) = ⊂sbc {{ieql = ⊂ₛ-trans it ieql}} {{ieqr = ⊂ₛ-trans it ieqr}}
⊂ₛ-trans (⊂dsbc {d = ic←}) (⊂sbc {{ieql = ieq}}) = ⊂dsbc {{ieq = ⊂ₛ-trans it ieq}}
⊂ₛ-trans (⊂dsbc {d = ic→}) (⊂sbc {{ieqr = ieq}}) = ⊂dsbc {{ieq = ⊂ₛ-trans it ieq}}
⊂ₛ-trans ⊂sic (⊂dsbc {{ieq = ieq}}) = ⊂dsbc {{ieq = ⊂ₛ-trans it ieq}}


-- TODO This could very well be emulated by ((∅-add ind) ⊂ₛ s)
-- -- data _∈ₛ_ {i u rll} : ∀{ll} → IndexLL {i} {u} rll ll → SetLL ll → Set where
-- --   inS ↓ : ∀{ll ind} → _∈ₛ_ {ll = ll} ind ↓
-- --   inS←∧←∧ : ∀{li ri ind s} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∧ ri} (ind ←∧) (s ←∧)
-- --   inS←∧←∧→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∧ ri} (ind ←∧) (s ←∧→ s₁)
-- --   inS∧→∧→ : ∀{li ri ind s} → _∈ₛ_ {ll = ri} ind s → _∈ₛ_ {ll = li ∧ ri} (∧→ ind) (∧→ s)
-- --   inS∧→←∧→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = ri} ind s₁ → _∈ₛ_ {ll = li ∧ ri} (∧→ ind) (s ←∧→ s₁)
-- --   inS←∨←∨ : ∀{li ri ind s} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∨ ri} (ind ←∨) (s ←∨)
-- --   inS←∨←∨→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∨ ri} (ind ←∨) (s ←∨→ s₁)
-- --   inS∨→∨→ : ∀{li ri ind s} → _∈ₛ_ {ll = ri} ind s → _∈ₛ_ {ll = li ∨ ri} (∨→ ind) (∨→ s)
-- --   inS∨→←∨→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = ri} ind s₁ → _∈ₛ_ {ll = li ∨ ri} (∨→ ind) (s ←∨→ s₁)
-- --   inS←∂←∂ : ∀{li ri ind s} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∂ ri} (ind ←∂) (s ←∂)
-- --   inS←∂←∂→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∂ ri} (ind ←∂) (s ←∂→ s₁)
-- --   inS∂→∂→ : ∀{li ri ind s} → _∈ₛ_ {ll = ri} ind s → _∈ₛ_ {ll = li ∂ ri} (∂→ ind) (∂→ s)
-- --   inS∂→←∂→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = ri} ind s₁ → _∈ₛ_ {ll = li ∂ ri} (∂→ ind) (s ←∂→ s₁)




