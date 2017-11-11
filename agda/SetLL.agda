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



∅-add-abs : ∀ {i u} {l r rll : LinLogic i {u}} {ds}
                {ind : IndexLL rll (pickLL ds l r)} {nrll : LinLogic i} →
              SetLL (replLL ind nrll) →
              SetLL
              (pickLL ds (pickLL ds (replLL ind nrll) l)
               (pickLL ds r (replLL ind nrll)))
∅-add-abs {ds = ic←} s = s
∅-add-abs {ds = ic→} s = s

-- Add a node to an empty set (and potentially replace the linear logic sub-tree).
∅-add : ∀{i u ll rll} → (ind : IndexLL {i} {u} rll ll) → {nrll : LinLogic i}
        → SetLL (replLL ind nrll)
∅-add ↓ = ↓
∅-add (ic ds ind) {nrll} = sic ds (∅-add-abs {ds = ds} {ind} (∅-add ind))









add-abs3 : ∀ {i u} {l : LinLogic i {u}} {r : LinLogic i} {ds d}
             {q : LinLogic i} {ind : IndexLL q (pickLL d l r)}
             {rll : LinLogic i} →
           (ds ≡ d → ⊥) →
           SetLL (pickLL ds l r) →
           SetLL (replLL ind rll) → SetLL (pickLL d (replLL ind rll) l) × SetLL (pickLL d r (replLL ind rll))
add-abs3 {ds = ic←} {ic←} ¬p s r = ⊥-elim (¬p refl)
add-abs3 {ds = ic←} {ic→} ¬p s r = s , r
add-abs3 {ds = ic→} {ic←} ¬p s r = r , s
add-abs3 {ds = ic→} {ic→} ¬p s r = ⊥-elim (¬p refl)



add-abs2 : ∀ {ds i u} {l r q : LinLogic i {u}}
             {ind : IndexLL q (pickLL ds l r)} {rll : LinLogic i} →
           SetLL (replLL ind rll) →
           SetLL
           (pickLL ds (pickLL ds (replLL ind rll) l)
            (pickLL ds r (replLL ind rll)))
add-abs2 {ic←} ns = ns
add-abs2 {ic→} ns = ns




mutual

  add-abs : ∀ {i u} {l r : LinLogic i {u}} {ds d} →
            SetLL (pickLL ds l r) →
            Dec (ds ≡ d) →
            ∀ {il} {q : LinLogic i} {ind : IndexLL q (pickLL d l r)}
              {rll : LinLogic i} →
            SetLL
            (pickLL d (replLL ind rll) l < il > pickLL d r (replLL ind rll))
  add-abs {ds = ds} s (yes refl) {ind = ind} {rll} = sic ds (add-abs2 {ds = ds} {ind = ind} (add s ind))
  add-abs s (no ¬p) {ind = ind} {rll} = sbc (proj₁ q) (proj₂ q) where
    r = ∅-add ind {rll}
    q = add-abs3 {ind = ind} ¬p s r


  -- Add a node to a set (and potentially replace the linear logic sub-tree).
  add : ∀{i u ll q} → SetLL ll → (ind : IndexLL {i} {u} q ll) → {rll : LinLogic i}
        → SetLL (replLL ind rll)
  add ↓ ind = ↓
  add (sic ds s) ↓ = ↓
  add (sic ds s) (ic d ind) = add-abs s (isEqICT ds d) {ind = ind}
  add (sbc s s₁) ↓ = ↓
  add (sbc s s₁) (ic ic← ind) = sbc (add s ind) s₁
  add (sbc s s₁) (ic ic→ ind) = sbc s (add s₁ ind) 



madd : ∀{i u ll q} → MSetLL ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic i)
      → MSetLL (replLL ind rll)
madd ∅ ind rll = ¬∅ (∅-add ind)
madd (¬∅ x) ind rll = ¬∅ (add x ind)




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



s-extendg : ∀{i u ll q} → ∀{rll} → (ind : IndexLL {i} {u} q ll) → SetLL {i} rll → SetLL (replLL ind rll)
s-extendg ↓ s = s
s-extendg {rll = rll} (ic d ind) s = sic d (subst SetLL (trans (pickLL-id d (replLL ind rll)) (sym (pickLL-eq d pickLL pickLL _ _ _ _ refl refl))) (s-extendg ind s))


s-extend : ∀{i u ll rll} → (ind : IndexLL {i} {u} rll ll) → SetLL {i} rll → SetLL ll
s-extend {ll = ll} {rll = rll} ind b = subst (λ x → SetLL x) (replLL-id ind) (s-extendg ind b)


mutual

  replacePartOf-abs : ∀ {i u} {l r q rll : LinLogic i {u}} {ds d} →
                    SetLL (pickLL ds l r) →
                    SetLL rll →
                    (ind : IndexLL q (pickLL d l r)) →
                    Dec (ds ≡ d) →
                    ∀ {il} →
                    SetLL
                    (pickLL d (replLL ind rll) l < il > pickLL d r (replLL ind rll))
  replacePartOf-abs {rll = rll} {ds = ds} a b ind (yes refl) = sic ds (subst SetLL (trans (pickLL-id ds (replLL ind rll)) (sym (pickLL-eq ds pickLL pickLL _ _ _ _ refl refl))) is) where
    is = replacePartOf a to b at ind
  replacePartOf-abs {ds = ic←} {ic←} a b ind (no ¬p) = ⊥-elim (¬p refl)
  replacePartOf-abs {ds = ic←} {ic→} a b ind (no ¬p) = sbc a (s-extendg ind b)
  replacePartOf-abs {ds = ic→} {ic←} a b ind (no ¬p) = sbc (s-extendg ind b) a
  replacePartOf-abs {ds = ic→} {ic→} a b ind (no ¬p) = ⊥-elim (¬p refl)


  replacePartOf_to_at_ : ∀{i u ll q} → ∀{rll} → SetLL ll → SetLL {i} rll → (ind : IndexLL {i} {u} q ll)
               → SetLL (replLL ind rll)
  replacePartOf a to b at ↓ = b
  replacePartOf_to_at_ {rll = rll} ↓ b (ic {l = l} {r = r} {il = il} d ind) = sbc (pickLLₛ d is ↓) (pickLLₛ d ↓ is) where
    is = replacePartOf ↓ to b at ind
  replacePartOf sic ds a to b at ic d ind = replacePartOf-abs a b ind (isEqICT ds d)
  replacePartOf sbc a a₁ to b at ic ic← ind = sbc (replacePartOf a to b at ind) a₁
  replacePartOf sbc a a₁ to b at ic ic→ ind = sbc a (replacePartOf a₁ to b at ind)


mreplacePartOf_to_at_ : ∀{i u ll q} → ∀{rll} → MSetLL ll → MSetLL {i} rll → (ind : IndexLL {i} {u} q ll)
          → MSetLL (replLL ind rll)
mreplacePartOf ∅ to ∅ at ind = ∅
mreplacePartOf_to_at_ {q = q} {rll = rll} ∅ (¬∅ x) ind = ¬∅ (s-extendg ind x)
mreplacePartOf_to_at_ {rll = rll} (¬∅ x) ∅ ind = del x ind
mreplacePartOf ¬∅ x to ¬∅ x₁ at ind = ¬∅ (replacePartOf x to x₁ at ind)


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
tran ↓ (dₜᵣ tr) = ↓
tran (sic ic← s) (dₜᵣ tr) = {!!}
tran (sic ic→ s) (dₜᵣ tr) = {!!} -- tran {!!} tr
tran (sbc s s₁) (dₜᵣ tr) = {!!}
tran s (¬dₜᵣ tr) = {!!}


-- -- -- If we transform the linear logic tree, we need to transform the SetLL as well.
-- -- tran : ∀ {i u ll rll} → SetLL ll → (tr : LLTr {i} {u} rll ll)
-- --        → SetLL rll
-- -- tran s I                           = s
-- -- tran ↓ (∂c tr)                     = ↓
-- -- tran (s ←∂) (∂c tr)                = tran (∂→ s) tr
-- -- tran (∂→ s) (∂c tr)                = tran (s ←∂) tr
-- -- tran (s ←∂→ s₁) (∂c tr)            = tran (s₁ ←∂→ s) tr
-- -- tran ↓ (∨c tr)                     = ↓
-- -- tran (s ←∨) (∨c tr)                = tran (∨→ s) tr
-- -- tran (∨→ s) (∨c tr)                = tran (s ←∨) tr
-- -- tran (s ←∨→ s₁) (∨c tr)            = tran (s₁ ←∨→ s) tr
-- -- tran ↓ (∧c tr)                     = ↓
-- -- tran (s ←∧) (∧c tr)                = tran (∧→ s) tr
-- -- tran (∧→ s) (∧c tr)                = tran (s ←∧) tr
-- -- tran (s ←∧→ s₁) (∧c tr)            = tran (s₁ ←∧→ s) tr
-- -- tran ↓ (∧∧d tr)                    = ↓
-- -- tran (↓ ←∧) (∧∧d tr)               = tran (↓ ←∧→ (↓ ←∧)) tr
-- -- tran ((s ←∧) ←∧) (∧∧d tr)          = tran (s ←∧) tr
-- -- tran ((∧→ s) ←∧) (∧∧d tr)          = tran (∧→ (s ←∧)) tr
-- -- tran ((s ←∧→ s₁) ←∧) (∧∧d tr)      = tran (s ←∧→ (s₁ ←∧)) tr
-- -- tran (∧→ s) (∧∧d tr)               = tran (∧→ (∧→ s)) tr
-- -- tran (↓ ←∧→ s₁) (∧∧d tr)           = tran (↓ ←∧→ (↓ ←∧→ s₁)) tr
-- -- tran ((s ←∧) ←∧→ s₁) (∧∧d tr)      = tran (s ←∧→ (∧→ s₁)) tr
-- -- tran ((∧→ s) ←∧→ s₁) (∧∧d tr)      = tran (∧→ (s ←∧→ s₁)) tr
-- -- tran ((s ←∧→ s₁) ←∧→ s₂) (∧∧d tr)  = tran (s ←∧→ (s₁ ←∧→ s₂)) tr
-- -- tran ↓ (¬∧∧d tr)                   = ↓
-- -- tran (s ←∧) (¬∧∧d tr)              = tran ((s ←∧) ←∧) tr
-- -- tran (∧→ ↓) (¬∧∧d tr)              = tran ((∧→ ↓) ←∧→ ↓) tr
-- -- tran (∧→ (s ←∧)) (¬∧∧d tr)         = tran ((∧→ s) ←∧) tr
-- -- tran (∧→ (∧→ s)) (¬∧∧d tr)         = tran (∧→ s) tr
-- -- tran (∧→ (s ←∧→ s₁)) (¬∧∧d tr)     = tran ((∧→ s) ←∧→ s₁) tr
-- -- tran (s ←∧→ ↓) (¬∧∧d tr)           = tran ((s ←∧→ ↓) ←∧→ ↓) tr
-- -- tran (s ←∧→ (s₁ ←∧)) (¬∧∧d tr)     = tran ((s ←∧→ s₁) ←∧) tr
-- -- tran (s ←∧→ (∧→ s₁)) (¬∧∧d tr)     = tran ((s ←∧) ←∧→ s₁) tr
-- -- tran (s ←∧→ (s₁ ←∧→ s₂)) (¬∧∧d tr) = tran ((s ←∧→ s₁) ←∧→ s₂) tr
-- -- tran ↓ (∨∨d tr)                    = ↓
-- -- tran (↓ ←∨) (∨∨d tr)               = tran (↓ ←∨→ (↓ ←∨)) tr
-- -- tran ((s ←∨) ←∨) (∨∨d tr)          = tran (s ←∨) tr
-- -- tran ((∨→ s) ←∨) (∨∨d tr)          = tran (∨→ (s ←∨)) tr
-- -- tran ((s ←∨→ s₁) ←∨) (∨∨d tr)      = tran (s ←∨→ (s₁ ←∨)) tr
-- -- tran (∨→ s) (∨∨d tr)               = tran (∨→ (∨→ s)) tr
-- -- tran (↓ ←∨→ s₁) (∨∨d tr)           = tran (↓ ←∨→ (↓ ←∨→ s₁)) tr
-- -- tran ((s ←∨) ←∨→ s₁) (∨∨d tr)      = tran (s ←∨→ (∨→ s₁)) tr
-- -- tran ((∨→ s) ←∨→ s₁) (∨∨d tr)      = tran (∨→ (s ←∨→ s₁)) tr
-- -- tran ((s ←∨→ s₁) ←∨→ s₂) (∨∨d tr)  = tran (s ←∨→ (s₁ ←∨→ s₂)) tr
-- -- tran ↓ (¬∨∨d tr)                   = ↓
-- -- tran (s ←∨) (¬∨∨d tr)              = tran ((s ←∨) ←∨) tr
-- -- tran (∨→ ↓) (¬∨∨d tr)              = tran ((∨→ ↓) ←∨→ ↓) tr
-- -- tran (∨→ (s ←∨)) (¬∨∨d tr)         = tran ((∨→ s) ←∨) tr
-- -- tran (∨→ (∨→ s)) (¬∨∨d tr)         = tran (∨→ s) tr
-- -- tran (∨→ (s ←∨→ s₁)) (¬∨∨d tr)     = tran ((∨→ s) ←∨→ s₁) tr
-- -- tran (s ←∨→ ↓) (¬∨∨d tr)           = tran ((s ←∨→ ↓) ←∨→ ↓) tr
-- -- tran (s ←∨→ (s₁ ←∨)) (¬∨∨d tr)     = tran ((s ←∨→ s₁) ←∨) tr
-- -- tran (s ←∨→ (∨→ s₁)) (¬∨∨d tr)     = tran ((s ←∨) ←∨→ s₁) tr
-- -- tran (s ←∨→ (s₁ ←∨→ s₂)) (¬∨∨d tr) = tran ((s ←∨→ s₁) ←∨→ s₂) tr
-- -- tran ↓ (∂∂d tr)                    = ↓
-- -- tran (↓ ←∂) (∂∂d tr)               = tran (↓ ←∂→ (↓ ←∂)) tr
-- -- tran ((s ←∂) ←∂) (∂∂d tr)          = tran (s ←∂) tr
-- -- tran ((∂→ s) ←∂) (∂∂d tr)          = tran (∂→ (s ←∂)) tr
-- -- tran ((s ←∂→ s₁) ←∂) (∂∂d tr)      = tran (s ←∂→ (s₁ ←∂)) tr
-- -- tran (∂→ s) (∂∂d tr)               = tran (∂→ (∂→ s)) tr
-- -- tran (↓ ←∂→ s₁) (∂∂d tr)           = tran (↓ ←∂→ (↓ ←∂→ s₁)) tr
-- -- tran ((s ←∂) ←∂→ s₁) (∂∂d tr)      = tran (s ←∂→ (∂→ s₁)) tr
-- -- tran ((∂→ s) ←∂→ s₁) (∂∂d tr)      = tran (∂→ (s ←∂→ s₁)) tr
-- -- tran ((s ←∂→ s₁) ←∂→ s₂) (∂∂d tr)  = tran (s ←∂→ (s₁ ←∂→ s₂)) tr
-- -- tran ↓ (¬∂∂d tr)                   = ↓
-- -- tran (s ←∂) (¬∂∂d tr)              = tran ((s ←∂) ←∂) tr
-- -- tran (∂→ ↓) (¬∂∂d tr)              = tran ((∂→ ↓) ←∂→ ↓) tr
-- -- tran (∂→ (s ←∂)) (¬∂∂d tr)         = tran ((∂→ s) ←∂) tr
-- -- tran (∂→ (∂→ s)) (¬∂∂d tr)         = tran (∂→ s) tr
-- -- tran (∂→ (s ←∂→ s₁)) (¬∂∂d tr)     = tran ((∂→ s) ←∂→ s₁) tr
-- -- tran (s ←∂→ ↓) (¬∂∂d tr)           = tran ((s ←∂→ ↓) ←∂→ ↓) tr
-- -- tran (s ←∂→ (s₁ ←∂)) (¬∂∂d tr)     = tran ((s ←∂→ s₁) ←∂) tr
-- -- tran (s ←∂→ (∂→ s₁)) (¬∂∂d tr)     = tran ((s ←∂) ←∂→ s₁) tr
-- -- tran (s ←∂→ (s₁ ←∂→ s₂)) (¬∂∂d tr) = tran ((s ←∂→ s₁) ←∂→ s₂) tr




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




-- -- truncSetLL : ∀ {i u ll pll} → SetLL ll → (ind : IndexLL {i} {u} pll ll)
-- --              → MSetLL pll
-- -- truncSetLL s ↓ = ¬∅ s
-- -- truncSetLL ↓ (ind ←∧) = ¬∅ ↓
-- -- truncSetLL (s ←∧) (ind ←∧) = truncSetLL s ind
-- -- truncSetLL (∧→ s) (ind ←∧) = ∅
-- -- truncSetLL (s ←∧→ s₁) (ind ←∧) = truncSetLL s ind
-- -- truncSetLL ↓ (∧→ ind) = ¬∅ ↓
-- -- truncSetLL (s ←∧) (∧→ ind) = ∅
-- -- truncSetLL (∧→ s) (∧→ ind) = truncSetLL s ind
-- -- truncSetLL (s ←∧→ s₁) (∧→ ind) = truncSetLL s₁ ind
-- -- truncSetLL ↓ (ind ←∨) = ¬∅ ↓
-- -- truncSetLL (s ←∨) (ind ←∨) = truncSetLL s ind
-- -- truncSetLL (∨→ s) (ind ←∨) = ∅
-- -- truncSetLL (s ←∨→ s₁) (ind ←∨) = truncSetLL s ind
-- -- truncSetLL ↓ (∨→ ind) = ¬∅ ↓
-- -- truncSetLL (s ←∨) (∨→ ind) = ∅
-- -- truncSetLL (∨→ s) (∨→ ind) = truncSetLL s ind
-- -- truncSetLL (s ←∨→ s₁) (∨→ ind) = truncSetLL s₁ ind
-- -- truncSetLL ↓ (ind ←∂) = ¬∅ ↓
-- -- truncSetLL (s ←∂) (ind ←∂) = truncSetLL s ind
-- -- truncSetLL (∂→ s) (ind ←∂) = ∅
-- -- truncSetLL (s ←∂→ s₁) (ind ←∂) = truncSetLL s ind
-- -- truncSetLL ↓ (∂→ ind) = ¬∅ ↓
-- -- truncSetLL (s ←∂) (∂→ ind) = ∅
-- -- truncSetLL (∂→ s) (∂→ ind) = truncSetLL s ind
-- -- truncSetLL (s ←∂→ s₁) (∂→ ind) = truncSetLL s₁ ind


-- -- tr-ext⇒id : ∀{i u pll ll} → ∀ s → (ind : IndexLL {i} {u} pll ll) →  truncSetLL (extend ind s) ind ≡ ¬∅ s
-- -- tr-ext⇒id s ↓ = refl
-- -- tr-ext⇒id {pll = pll} {ll = li ∧ ri} s (ind ←∧)
-- --   with replLL li ind pll | replLL-id li ind pll refl | extendg ind s | tr-ext⇒id s ind
-- -- ... | .li | refl | q | e = e
-- -- tr-ext⇒id {pll = pll} {ll = li ∧ ri} s (∧→ ind)
-- --   with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind s | tr-ext⇒id s ind
-- -- ... | .ri | refl | g | e = e
-- -- tr-ext⇒id {pll = pll} {ll = li ∨ ri} s (ind ←∨)
-- --   with replLL li ind pll | replLL-id li ind pll refl | extendg ind s | tr-ext⇒id s ind
-- -- ... | .li | refl | q | e = e
-- -- tr-ext⇒id {pll = pll} {ll = li ∨ ri} s (∨→ ind)
-- --   with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind s | tr-ext⇒id s ind
-- -- ... | .ri | refl | g | e = e
-- -- tr-ext⇒id {pll = pll} {ll = li ∂ ri} s (ind ←∂)
-- --   with replLL li ind pll | replLL-id li ind pll refl | extendg ind s | tr-ext⇒id s ind
-- -- ... | .li | refl | q | e = e
-- -- tr-ext⇒id {pll = pll} {ll = li ∂ ri} s (∂→ ind)
-- --   with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind s | tr-ext⇒id s ind
-- -- ... | .ri | refl | g | e = e


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



-- --   tr-repl⇒id : ∀{i u ll ell pll} → (s : SetLL ll) → (lind : IndexLL {i} {u} pll ll)
-- --           → (vs : SetLL ell) 
-- --           → let mx = replacePartOf s to vs at lind in
-- --             let tlind = subst (λ z → IndexLL z (replLL ll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))) in
-- --           truncSetLL mx tlind ≡ ¬∅ vs
-- --   tr-repl⇒id s ↓ vs = refl
-- --   tr-repl⇒id {ll = lll ∧ rll} {ell} {pll} ↓ (lind ←∧) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id ↓ lind vs
-- --   tr-repl⇒id {u = _} {lll ∧ rll} {.g} {pll} ↓ (lind ←∧) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∧ rll} {ell} {pll} (s ←∧) (lind ←∧) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s lind vs
-- --   tr-repl⇒id {u = _} {lll ∧ rll} {.g} {pll} (s ←∧) (lind ←∧) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∧ rll} {ell} {pll} (∧→ s) (lind ←∧) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-extg⇒id vs lind
-- --   tr-repl⇒id {u = _} {lll ∧ rll} {.g} {pll} (∧→ s) (lind ←∧) vs | g | refl | t | m = m
-- --   tr-repl⇒id {ll = lll ∧ rll} {ell} {pll} (s ←∧→ s₁) (lind ←∧) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s lind vs
-- --   tr-repl⇒id {u = _} {lll ∧ rll} {.g} {pll} (s ←∧→ s₁) (lind ←∧) vs | g | refl | e | is = is
-- --   tr-repl⇒id {ll = lll ∧ rll} {ell} {pll} ↓ (∧→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id ↓ lind vs
-- --   tr-repl⇒id {u = _} {lll ∧ rll} {.g} {pll} ↓ (∧→ lind) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∧ rll} {ell} {pll} (s ←∧) (∧→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-extg⇒id vs lind
-- --   tr-repl⇒id {u = _} {lll ∧ rll} {.g} {pll} (s ←∧) (∧→ lind) vs | g | refl | t | m = m
-- --   tr-repl⇒id {ll = lll ∧ rll} {ell} {pll} (∧→ s) (∧→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s lind vs
-- --   tr-repl⇒id {u = _} {lll ∧ rll} {.g} {pll} (∧→ s) (∧→ lind) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∧ rll} {ell} {pll} (s ←∧→ s₁) (∧→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s₁ lind vs
-- --   tr-repl⇒id {u = _} {lll ∧ rll} {.g} {pll} (s ←∧→ s₁) (∧→ lind) vs | g | refl | e | is = is
-- --   tr-repl⇒id {ll = lll ∨ rll} {ell} {pll} ↓ (lind ←∨) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id ↓ lind vs
-- --   tr-repl⇒id {u = _} {lll ∨ rll} {.g} {pll} ↓ (lind ←∨) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∨ rll} {ell} {pll} (s ←∨) (lind ←∨) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s lind vs
-- --   tr-repl⇒id {u = _} {lll ∨ rll} {.g} {pll} (s ←∨) (lind ←∨) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∨ rll} {ell} {pll} (∨→ s) (lind ←∨) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-extg⇒id vs lind
-- --   tr-repl⇒id {u = _} {lll ∨ rll} {.g} {pll} (∨→ s) (lind ←∨) vs | g | refl | t | m = m
-- --   tr-repl⇒id {ll = lll ∨ rll} {ell} {pll} (s ←∨→ s₁) (lind ←∨) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s lind vs
-- --   tr-repl⇒id {u = _} {lll ∨ rll} {.g} {pll} (s ←∨→ s₁) (lind ←∨) vs | g | refl | e | is = is
-- --   tr-repl⇒id {ll = lll ∨ rll} {ell} {pll} ↓ (∨→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id ↓ lind vs
-- --   tr-repl⇒id {u = _} {lll ∨ rll} {.g} {pll} ↓ (∨→ lind) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∨ rll} {ell} {pll} (s ←∨) (∨→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-extg⇒id vs lind
-- --   tr-repl⇒id {u = _} {lll ∨ rll} {.g} {pll} (s ←∨) (∨→ lind) vs | g | refl | t | m = m
-- --   tr-repl⇒id {ll = lll ∨ rll} {ell} {pll} (∨→ s) (∨→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s lind vs
-- --   tr-repl⇒id {u = _} {lll ∨ rll} {.g} {pll} (∨→ s) (∨→ lind) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∨ rll} {ell} {pll} (s ←∨→ s₁) (∨→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s₁ lind vs
-- --   tr-repl⇒id {u = _} {lll ∨ rll} {.g} {pll} (s ←∨→ s₁) (∨→ lind) vs | g | refl | e | is = is
-- --   tr-repl⇒id {ll = lll ∂ rll} {ell} {pll} ↓ (lind ←∂) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id ↓ lind vs
-- --   tr-repl⇒id {u = _} {lll ∂ rll} {.g} {pll} ↓ (lind ←∂) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∂ rll} {ell} {pll} (s ←∂) (lind ←∂) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s lind vs
-- --   tr-repl⇒id {u = _} {lll ∂ rll} {.g} {pll} (s ←∂) (lind ←∂) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∂ rll} {ell} {pll} (∂→ s) (lind ←∂) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-extg⇒id vs lind
-- --   tr-repl⇒id {u = _} {lll ∂ rll} {.g} {pll} (∂→ s) (lind ←∂) vs | g | refl | t | m = m
-- --   tr-repl⇒id {ll = lll ∂ rll} {ell} {pll} (s ←∂→ s₁) (lind ←∂) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s lind vs
-- --   tr-repl⇒id {u = _} {lll ∂ rll} {.g} {pll} (s ←∂→ s₁) (lind ←∂) vs | g | refl | e | is = is
-- --   tr-repl⇒id {ll = lll ∂ rll} {ell} {pll} ↓ (∂→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id ↓ lind vs
-- --   tr-repl⇒id {u = _} {lll ∂ rll} {.g} {pll} ↓ (∂→ lind) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∂ rll} {ell} {pll} (s ←∂) (∂→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-extg⇒id vs lind
-- --   tr-repl⇒id {u = _} {lll ∂ rll} {.g} {pll} (s ←∂) (∂→ lind) vs | g | refl | t | m = m
-- --   tr-repl⇒id {ll = lll ∂ rll} {ell} {pll} (∂→ s) (∂→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s lind vs
-- --   tr-repl⇒id {u = _} {lll ∂ rll} {.g} {pll} (∂→ s) (∂→ lind) vs | g | refl | t | r = r
-- --   tr-repl⇒id {ll = lll ∂ rll} {ell} {pll} (s ←∂→ s₁) (∂→ lind) vs with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | tr-repl⇒id s₁ lind vs
-- --   tr-repl⇒id {u = _} {lll ∂ rll} {.g} {pll} (s ←∂→ s₁) (∂→ lind) vs | g | refl | e | is = is








-- -- data _≤s_ {i : Size} {u} : {ll : LinLogic i {u}} → SetLL ll → SetLL ll → Set where
-- --   ≤↓   : ∀{ll s} → _≤s_ {ll = ll} s ↓
-- --   ≤←∧  : ∀{lll llr sx sy} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∧ llr} (sx ←∧) (sy ←∧)
-- --   ≤∧→  : ∀{lll llr sx sy} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∧ llr} (∧→ sx) (∧→ sy)
-- --   ≤←∨  : ∀{lll llr sx sy} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∨ llr} (sx ←∨) (sy ←∨)
-- --   ≤∨→  : ∀{lll llr sx sy} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∨ llr} (∨→ sx) (∨→ sy)
-- --   ≤←∂  : ∀{lll llr sx sy} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∂ llr} (sx ←∂) (sy ←∂)
-- --   ≤∂→  : ∀{lll llr sx sy} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∂ llr} (∂→ sx) (∂→ sy)
-- --   ≤←∧→ : ∀{lll llr slx sly srx sry} → _≤s_ {ll = lll} slx sly → _≤s_ {ll = llr} srx sry → _≤s_ {ll = lll ∧ llr} (slx ←∧→ srx) (sly ←∧→ sry)
-- --   ≤←∨→ : ∀{lll llr slx sly srx sry} → _≤s_ {ll = lll} slx sly → _≤s_ {ll = llr} srx sry → _≤s_ {ll = lll ∨ llr} (slx ←∨→ srx) (sly ←∨→ sry)
-- --   ≤←∂→ : ∀{lll llr slx sly srx sry} → _≤s_ {ll = lll} slx sly → _≤s_ {ll = llr} srx sry → _≤s_ {ll = lll ∂ llr} (slx ←∂→ srx) (sly ←∂→ sry)
-- --   ≤d←∧ : ∀{lll llr sx sy s} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∧ llr} (sx ←∧) (sy ←∧→ s)
-- --   ≤d∧→ : ∀{lll llr sx sy s} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∧ llr} (∧→ sx) (s ←∧→ sy)
-- --   ≤d←∨ : ∀{lll llr sx sy s} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∨ llr} (sx ←∨) (sy ←∨→ s)
-- --   ≤d∨→ : ∀{lll llr sx sy s} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∨ llr} (∨→ sx) (s ←∨→ sy)
-- --   ≤d←∂ : ∀{lll llr sx sy s} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∂ llr} (sx ←∂) (sy ←∂→ s)
-- --   ≤d∂→ : ∀{lll llr sx sy s} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∂ llr} (∂→ sx) (s ←∂→ sy)





-- -- ≤s-ext : ∀{i u pll ll q ss} → (ind : IndexLL {i} {u} q ll) → {s : SetLL pll} → ss ≤s s → extendg ind ss ≤s extendg ind s
-- -- ≤s-ext ↓ ss≤s = ss≤s
-- -- ≤s-ext (ind ←∧) ss≤s = ≤←∧ (≤s-ext ind ss≤s)
-- -- ≤s-ext (∧→ ind) ss≤s = ≤∧→ (≤s-ext ind ss≤s)
-- -- ≤s-ext (ind ←∨) ss≤s = ≤←∨ (≤s-ext ind ss≤s)
-- -- ≤s-ext (∨→ ind) ss≤s = ≤∨→ (≤s-ext ind ss≤s)
-- -- ≤s-ext (ind ←∂) ss≤s = ≤←∂ (≤s-ext ind ss≤s)
-- -- ≤s-ext (∂→ ind) ss≤s = ≤∂→ (≤s-ext ind ss≤s)




-- -- ≤s-refl : ∀{i u ll} → (s : SetLL {i} {u} ll) → s ≤s s
-- -- ≤s-refl ↓ = ≤↓
-- -- ≤s-refl (s ←∧) = ≤←∧ (≤s-refl s)
-- -- ≤s-refl (∧→ s) = ≤∧→ (≤s-refl s)
-- -- ≤s-refl (s ←∧→ s₁) = ≤←∧→ (≤s-refl s) (≤s-refl s₁)
-- -- ≤s-refl (s ←∨) = ≤←∨ (≤s-refl s)
-- -- ≤s-refl (∨→ s) = ≤∨→ (≤s-refl s)
-- -- ≤s-refl (s ←∨→ s₁) = ≤←∨→ (≤s-refl s) (≤s-refl s₁)
-- -- ≤s-refl (s ←∂) = ≤←∂ (≤s-refl s)
-- -- ≤s-refl (∂→ s) = ≤∂→ (≤s-refl s)
-- -- ≤s-refl (s ←∂→ s₁) = ≤←∂→ (≤s-refl s) (≤s-refl s₁)




-- -- ≤s-trans : ∀{i u ll b c} → {a : SetLL {i} {u} ll} → a ≤s b → b ≤s c → a ≤s c
-- -- ≤s-trans ≤↓ ≤↓ = ≤↓
-- -- ≤s-trans (≤←∧ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤←∧ x) (≤←∧ x₁) = ≤←∧ (≤s-trans x x₁)
-- -- ≤s-trans (≤←∧ x) (≤d←∧ x₁) = ≤d←∧ (≤s-trans x x₁)
-- -- ≤s-trans (≤∧→ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤∧→ x) (≤∧→ x₁) = ≤∧→ (≤s-trans x x₁)
-- -- ≤s-trans (≤∧→ x) (≤d∧→ x₁) = ≤d∧→ (≤s-trans x x₁)
-- -- ≤s-trans (≤←∨ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤←∨ x) (≤←∨ x₁) = ≤←∨ (≤s-trans x x₁)
-- -- ≤s-trans (≤←∨ x) (≤d←∨ x₁) = ≤d←∨ (≤s-trans x x₁)
-- -- ≤s-trans (≤∨→ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤∨→ x) (≤∨→ x₁) = ≤∨→ (≤s-trans x x₁)
-- -- ≤s-trans (≤∨→ x) (≤d∨→ x₁) = ≤d∨→ (≤s-trans x x₁)
-- -- ≤s-trans (≤←∂ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤←∂ x) (≤←∂ x₁) = ≤←∂ (≤s-trans x x₁)
-- -- ≤s-trans (≤←∂ x) (≤d←∂ x₁) = ≤d←∂ (≤s-trans x x₁)
-- -- ≤s-trans (≤∂→ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤∂→ x) (≤∂→ x₁) = ≤∂→ (≤s-trans x x₁)
-- -- ≤s-trans (≤∂→ x) (≤d∂→ x₁) = ≤d∂→ (≤s-trans x x₁)
-- -- ≤s-trans (≤←∧→ x x₁) ≤↓ = ≤↓
-- -- ≤s-trans (≤←∧→ x x₁) (≤←∧→ x₂ x₃) = ≤←∧→ (≤s-trans x x₂) (≤s-trans x₁ x₃)
-- -- ≤s-trans (≤←∨→ x x₁) ≤↓ = ≤↓
-- -- ≤s-trans (≤←∨→ x x₁) (≤←∨→ x₂ x₃) = ≤←∨→ (≤s-trans x x₂) (≤s-trans x₁ x₃)
-- -- ≤s-trans (≤←∂→ x x₁) ≤↓ = ≤↓
-- -- ≤s-trans (≤←∂→ x x₁) (≤←∂→ x₂ x₃) = ≤←∂→ (≤s-trans x x₂) (≤s-trans x₁ x₃)
-- -- ≤s-trans (≤d←∧ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤d←∧ x) (≤←∧→ x₁ x₂) = ≤d←∧ (≤s-trans x x₁)
-- -- ≤s-trans (≤d∧→ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤d∧→ x) (≤←∧→ x₁ x₂) = ≤d∧→ (≤s-trans x x₂)
-- -- ≤s-trans (≤d←∨ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤d←∨ x) (≤←∨→ x₁ x₂) = ≤d←∨ (≤s-trans x x₁)
-- -- ≤s-trans (≤d∨→ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤d∨→ x) (≤←∨→ x₁ x₂) = ≤d∨→ (≤s-trans x x₂)
-- -- ≤s-trans (≤d←∂ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤d←∂ x) (≤←∂→ x₁ x₂) = ≤d←∂ (≤s-trans x x₁)
-- -- ≤s-trans (≤d∂→ x) ≤↓ = ≤↓
-- -- ≤s-trans (≤d∂→ x) (≤←∂→ x₁ x₂) = ≤d∂→ (≤s-trans x x₂)



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




