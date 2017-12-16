module SetLL where

open import Common hiding (_≤_)
open import LinLogic
-- open import LinLogicProp
open import IndexLLProp -- hiding (tran)
import Data.List
open import Relation.Binary.PropositionalEquality
import Data.Product
open import Data.Sum





data SetLL {i : Size} {u} : LinLogic i {u} → Set where
  ↓     : ∀{ll}                          → SetLL ll
  sic   : ∀{l r} → {il : LLCT} → (ds : IndexLLCT) → SetLL (pickLL ds l r) → SetLL (l < il > r)
  sbc   : ∀{l r} → {il : LLCT} → SetLL l → SetLL r → SetLL (l < il > r)


-- A possibly empty set of nodes in a Linear Logic tree. 
data MSetLL {i : Size} {u} : LinLogic i {u} → Set where
  ∅   : ∀{ll}            → MSetLL ll
  ¬∅  : ∀{ll} → SetLL ll → MSetLL ll

-- To be removed
∅-neq-¬∅ : ∀{i u ll} → {s : SetLL {i} {u} ll} → ¬ (∅ ≡ ¬∅ s)
∅-neq-¬∅ ()

-- Defining a functor and a Monad from SetLL to MSetLL
mapₛ : ∀{i u ll1 ll2} → (SetLL {i} {u} ll1 → SetLL {i} {u} ll2) → (MSetLL ll1 → MSetLL ll2)
mapₛ f ∅ = ∅
mapₛ f (¬∅ x) = ¬∅ (f x)

mapₛ-id : ∀{i u ll} → (x : MSetLL ll) → mapₛ {i} {u} {ll} (λ z → z) x ≡ x
mapₛ-id ∅ = refl
mapₛ-id (¬∅ x) = refl

mapₛ-fg : ∀{i u ll1 ll2 lli} → {g : SetLL {i} {u} ll1 → SetLL {i} {u} lli} → {f : SetLL lli → SetLL {i} {u} ll2} → (x : MSetLL ll1)
          → mapₛ (f ∘ g) x ≡ mapₛ f (mapₛ g x)
mapₛ-fg ∅ = refl
mapₛ-fg (¬∅ x) = refl


_>>=ₛ_ : ∀{i u ll1 ll2} → MSetLL {i} {u} ll1 → (SetLL ll1 → MSetLL {i} {u} ll2) → MSetLL ll2
∅ >>=ₛ f = ∅
¬∅ x >>=ₛ f = f x


>>=ₛ-id : ∀ {i u} {rll : LinLogic i {u}} (w : MSetLL rll) →
                   w ≡ (w >>=ₛ ¬∅)
>>=ₛ-id ∅ = refl
>>=ₛ-id (¬∅ x) = refl


pickLLₛ : ∀{i u l r} → ∀ d → SetLL {i} {u} l → SetLL r → SetLL (pickLL d l r)
pickLLₛ ic← a b = a
pickLLₛ ic→ a b = b

~ₛ : ∀{i u l r} → ∀ d → SetLL {i} {u} (pickLL d l r) → SetLL (pickLL (~ict d) r l)
~ₛ ic← s = s
~ₛ ic→ s = s

pickLLₛ-sbc : ∀{i u il l r} → ∀ d → SetLL {i} {u} (pickLL d l r) → SetLL (pickLL (~ict d) l r) → SetLL (l < il > r)
pickLLₛ-sbc {l = l} {r} ic← s1 s2 = sbc s1 s2
pickLLₛ-sbc {l = l} {r} ic→ s1 s2 = sbc s2 s1

pickLLₛ-sbc-id : ∀{i u il l r} → ∀ d → {s : SetLL {i} {u} l} → {s1 : SetLL r} → pickLLₛ-sbc {il =  il} d (pickLLₛ d s s1) (pickLLₛ (~ict d) s s1) ≡ sbc s s1
pickLLₛ-sbc-id ic← {s} {s1} = refl
pickLLₛ-sbc-id ic→ {s} {s1} = refl


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



-- It hits at least once.

data hitsAtLeastOnce {i u} : ∀{ll rll} → SetLL ll → (ind : IndexLL {i} {u} rll ll) → Set where
  instance
    hLO↓ic     : ∀{d il l r rll ind}                      → hitsAtLeastOnce {ll = l < il > r} {rll = rll} ↓ (ic d ind)
    hLOs↓   : ∀{rll s}                                  → hitsAtLeastOnce {rll = rll} s ↓
    hLOsic  : ∀{d il ll rll  q s ind} → {{ieq : hitsAtLeastOnce s ind}}  → hitsAtLeastOnce {ll = q < il > ll} {rll = rll} (sic d s) (ic d ind) 
    hLOsbc : ∀{d il ll rll s q s₁ ind} → {{ieq : hitsAtLeastOnce (pickLLₛ d s s₁) ind}}  → hitsAtLeastOnce {ll = ll < il > q} {rll = rll} (sbc s s₁) (ic d ind)


data onlyInside {i u rll} : ∀{ll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → Set where
  instance
    oIs↓ : ∀{s} → onlyInside {ll = rll} s ↓
    oIic : ∀{d il l r s ind} → {{ieq : onlyInside s ind}} → onlyInside {ll = l < il > r} (sic d s) (ic d ind)


oi⇒ho : ∀{i u ll rll} → {s : SetLL ll} → {ind : IndexLL {i} {u} rll ll} → {{oi : onlyInside s ind}} → hitsAtLeastOnce s ind
oi⇒ho {{oi = oIs↓}} = hLOs↓
oi⇒ho {{oi = oIic}} = hLOsic {{ieq = oi⇒ho}}



mutual

  ∪ₛ-abs : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i} {ds ds₁} →
         SetLL (pickLL ds l r) →
         SetLL (pickLL ds₁ l r) → DecICT ds ds₁ → SetLL (l < il > r)
  ∪ₛ-abs {ds = ds} a b (yes refl) = sic ds (a ∪ₛ b)
  ∪ₛ-abs {ds = .(~ict ds₁)} {ds₁} a b (no refl) = pickLLₛ-sbc ds₁ b a

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


pickLLₘₛ : ∀ {i u} {l : LinLogic i {u}} {r : LinLogic i} →
          ∀ d → MSetLL l → MSetLL r → MSetLL (pickLL d l r)
pickLLₘₛ ic← ms ms1 = ms
pickLLₘₛ ic→ ms ms1 = ms1

pickLLₘₛ&¬∅⇒pickLLₛ : ∀ {i u} {l : LinLogic i {u}} {r : LinLogic i} → ∀{s s₁} →
          ∀ d → {ms : MSetLL l} → (ms ≡ ¬∅ s) → {ms₁ : MSetLL r} → (ms₁ ≡ ¬∅ s₁) → pickLLₘₛ d ms ms₁ ≡ ¬∅ (pickLLₛ d s s₁)
pickLLₘₛ&¬∅⇒pickLLₛ ic← eq eq1 = eq
pickLLₘₛ&¬∅⇒pickLLₛ ic→ eq eq1 = eq1         

sbcm : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i} →
          MSetLL l → MSetLL r → MSetLL (l < il > r)
sbcm ∅ ∅ = ∅
sbcm ∅ (¬∅ b)= ¬∅ (sic ic→ b)
sbcm (¬∅ x) ∅ = ¬∅ (sic ic← x)
sbcm (¬∅ x) (¬∅ b) = ¬∅ (sbc x b)

module _ where


  sbcm¬∅ : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i} →
           {ms : MSetLL l} → {ms₁ : MSetLL r} → (Σ _ (λ z → ¬∅ z ≡ ms)) ⊎ (Σ _ (λ z → ¬∅ z ≡ ms₁)) → Σ _ (λ z → sbcm {il = il} ms ms₁ ≡ ¬∅ z)
  sbcm¬∅ {ms = ∅} {ms₁} (inj₁ (proj₃ , ()))
  sbcm¬∅ {ms = ¬∅ x₁} {∅} (inj₁ x) = sic ic← x₁ , refl
  sbcm¬∅ {ms = ¬∅ x₁} {¬∅ x₂} (inj₁ x) = sbc x₁ x₂ , refl
  sbcm¬∅ {ms = ms} {∅} (inj₂ (proj₃ , ()))
  sbcm¬∅ {ms = ∅} {¬∅ x} (inj₂ y) = sic ic→ x , refl
  sbcm¬∅ {ms = ¬∅ x₁} {¬∅ x} (inj₂ y) = sbc x₁ x , refl


pickLLₛ-sbcm : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i} → ∀ d →
          MSetLL (pickLL d l r) → MSetLL (pickLL (~ict d) l r) → MSetLL (l < il > r)
pickLLₛ-sbcm ic← ms1 ms2 = sbcm ms1 ms2
pickLLₛ-sbcm ic→ ms1 ms2 = sbcm ms2 ms1


module _ where


  pickLLₛ-sbcm¬∅ : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i} → ∀ d
           {ms : MSetLL (pickLL d l r)} → {ms₁ : MSetLL (pickLL (~ict d) l r)} → (Σ _ (λ z → ¬∅ z ≡ ms)) ⊎ (Σ _ (λ z → ¬∅ z ≡ ms₁)) → Σ _ (λ z → pickLLₛ-sbcm {il = il} d ms ms₁ ≡ ¬∅ z)
  pickLLₛ-sbcm¬∅ ic← eq = sbcm¬∅ eq
  pickLLₛ-sbcm¬∅ ic→ {ms₁ = ms₁} (inj₁ x) = sbcm¬∅ {ms = ms₁} (inj₂ x)
  pickLLₛ-sbcm¬∅ ic→ {ms} (inj₂ y) = sbcm¬∅ {ms₁ = ms} (inj₁ y)


pickLLₛ-sbcm&¬∅⇒pickLLₛ-sbc : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i} → ∀ d → ∀{s s1} →
          (ms : MSetLL (pickLL d l r)) → (ms1 : MSetLL (pickLL (~ict d) l r)) → (ms ≡ ¬∅ s) → (ms1 ≡ ¬∅ s1) → pickLLₛ-sbcm {il = il} d ms ms1 ≡ ¬∅ (pickLLₛ-sbc d s s1)
pickLLₛ-sbcm&¬∅⇒pickLLₛ-sbc ic← .(¬∅ _) .(¬∅ _) refl refl = refl
pickLLₛ-sbcm&¬∅⇒pickLLₛ-sbc ic→ .(¬∅ _) .(¬∅ _) refl refl = refl  


pickLLₛ-sbcm⇒¬sic : ∀ d → ∀{ i u} {l : LinLogic i {u}} {il}
                       {r : LinLogic i} (a : MSetLL (pickLL d l r)) {b : SetLL (pickLL (~ict d) l r)}
                       {x : SetLL (pickLL d l r)} 
                     → ¬ (¬∅ (sic {il = il} d x) ≡ pickLLₛ-sbcm d a (¬∅ b))
pickLLₛ-sbcm⇒¬sic ic← ∅ = λ ()
pickLLₛ-sbcm⇒¬sic ic→ ∅ = λ ()
pickLLₛ-sbcm⇒¬sic ic← (¬∅ x) = λ ()
pickLLₛ-sbcm⇒¬sic ic→ (¬∅ x) = λ ()



∩ₛ-abs1 : ∀ {ds i u} {l : LinLogic i {u}} {il} {r : LinLogic i} →
          MSetLL (pickLL ds l r) → MSetLL (l < il > r)
∩ₛ-abs1 ∅ = ∅
∩ₛ-abs1 {ds} (¬∅ x) = ¬∅ (sic ds x)

mutual

  ∩ₛ-abs : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i} {ds ds₁} →
           SetLL (pickLL ds l r) →
           SetLL (pickLL ds₁ l r) → DecICT ds ds₁ → MSetLL (l < il > r)
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



complLₛ : ∀{i u ll} → SetLL {i} {u} ll → MSetLL ll
complLₛ ↓ = ∅
complLₛ (sic ds s) = pickLLₛ-sbcm ds (complLₛ s) (¬∅ fillAllLower)
complLₛ (sbc s s₁) = sbcm (complLₛ s) (complLₛ s₁)


mcomplLₛ : ∀{i u ll} → MSetLL {i} {u} ll → MSetLL ll
mcomplLₛ ∅ = ¬∅ fillAllLower
mcomplLₛ (¬∅ x) = complLₛ x


module _ where


  mutual
  
    compl≡∅⇒ho-abs1 : ∀ {i u} {l r : LinLogic i {u}} {il} {d}
                      {rll : LinLogic i} {s : SetLL l} {s₁ : SetLL r}
                      {ind : IndexLL rll (pickLL d l r)} (w : MSetLL l) (ieq : w ≡ complLₛ s) (w₁ : MSetLL r) (ieq1 : w₁ ≡ complLₛ s₁) →
                    sbcm {il = il} w w₁ ≡ ∅ → hitsAtLeastOnce (sbc {il = il} s s₁) (ic d ind)
    compl≡∅⇒ho-abs1 {d = ic←} ∅ ieq ∅ ieq1 eq = hLOsbc {{ieq = compl≡∅⇒ho (sym ieq)}}
    compl≡∅⇒ho-abs1 {d = ic→} ∅ ieq ∅ ieq1 eq = hLOsbc {{ieq = compl≡∅⇒ho (sym ieq1)}}
    compl≡∅⇒ho-abs1 ∅ ieq (¬∅ x) ieq1 ()
    compl≡∅⇒ho-abs1 (¬∅ x) ieq ∅ ieq1 ()
    compl≡∅⇒ho-abs1 (¬∅ x) ieq (¬∅ x₁) ieq1 ()
  
    compl≡∅⇒ho : ∀{i u rll ll} → {s : SetLL {i} {u} ll} → complLₛ s ≡ ∅
                 → {ind : IndexLL rll ll} → (hitsAtLeastOnce s ind)
    compl≡∅⇒ho {s = ↓} eq {↓} = hLOs↓
    compl≡∅⇒ho {s = ↓} eq {ic d ind} = hLO↓ic
    compl≡∅⇒ho {s = sic {il = il} ds s} eq {ind} = ⊥-elim (∅-neq-¬∅ a) where
      r = proj₂ (pickLLₛ-sbcm¬∅ {il = il} ds {ms = complLₛ s} {ms₁ = ¬∅ fillAllLower} (inj₂ (_ , refl)))
      a = trans (sym eq) r 
    compl≡∅⇒ho {s = sbc s s₁} eq {↓} = hLOs↓
    compl≡∅⇒ho {s = sbc s s₁} eq {ic d ind} = compl≡∅⇒ho-abs1 (complLₛ s) refl (complLₛ s₁) refl eq
  

module _ where

  
  compl≡∅⇒¬oi : ∀{i u rll l r il} → {s : SetLL {i} {u} (l < il > r)} → complLₛ s ≡ ∅
                → ∀{d ind} → ¬ (onlyInside s (ic {rll = rll} d ind))
  compl≡∅⇒¬oi {s = ↓} eq {ind = ind} = λ ()
  compl≡∅⇒¬oi {s = sic ds s} eq {ind = ind} = ⊥-elim (∅-neq-¬∅ (trans (sym eq) (proj₂ (pickLLₛ-sbcm¬∅ ds (inj₂ (fillAllLower , refl)))))) 
  compl≡∅⇒¬oi {s = sbc s s₁} eq {ind = ind} = λ ()



mutual

  del-abs : ∀ {i u} {l r q : LinLogic i {u}} {ds d}
            {s : SetLL (pickLL ds l r)} →
          IndexLL q (pickLL d l r) →
          DecICT ds d → ∀ {il} → MSetLL (l < il > r)
  del-abs {ds = ds} {s = s} ind (yes refl) = del s ind >>=ₛ (λ z → ¬∅ (sic ds z))
  del-abs {ds = ds} {s = s} ind (no x) = ¬∅ (sic ds s)
  
  -- Deletes an index if it is present, otherwise does nothing.
  del : ∀{i u ll q} → SetLL ll → (ind : IndexLL {i} {u} q ll)
        → MSetLL ll
  del s ↓ = ∅
  del ↓ (ic d ind) = pickLLₛ-sbcm d (del ↓ ind) (¬∅ (pickLLₛ (~ict d) ↓ ↓))
  del (sic ds s) (ic d ind) = del-abs {s = s} ind (isEqICT ds d) 
  del (sbc s s₁) (ic d ind) = pickLLₛ-sbcm d (del (pickLLₛ d s s₁) ind) (¬∅ (pickLLₛ (~ict d) s s₁))

mutual

  del⇒¬ho-abs3 : ∀ {i u} {l : LinLogic i {u}} {il} {r pll : LinLogic i}
                 {d} {dls : SetLL (l < il > r)} (lind : IndexLL pll (pickLL d l r))
                 (s : SetLL l) (s₁ : SetLL r) (w : MSetLL (pickLL d l r)) → (is : w ≡ del (pickLLₛ d s s₁) lind) →
               ¬∅ dls ≡ pickLLₛ-sbcm d w (¬∅ (pickLLₛ (~ict d) s s₁)) →
               hitsAtLeastOnce dls (ic d lind) → ⊥
  del⇒¬ho-abs3 {d = ic←} lind s s₁ ∅ is refl = λ { ()}
  del⇒¬ho-abs3 {d = ic→} lind s s₁ ∅ is refl = λ { ()}
  del⇒¬ho-abs3 {d = ic←} lind s s₁ (¬∅ x) is refl = λ { hLOsbc → del⇒¬ho lind is it}
  del⇒¬ho-abs3 {d = ic→} lind s s₁ (¬∅ x) is refl = λ { hLOsbc →  del⇒¬ho lind is it}


  del⇒¬ho-abs2 : ∀ {ds i u} {l : LinLogic i {u}} {il}
                 {r pll : LinLogic i} {dls : SetLL (l < il > r)} {s : SetLL (pickLL ds l r)}
                 {lind : IndexLL pll (pickLL ds l r)} (w : MSetLL (pickLL ds l r)) → (is : w ≡ del s lind) →
               ¬∅ dls ≡ (w >>=ₛ (λ z → ¬∅ (sic ds z))) →
               hitsAtLeastOnce dls (ic ds lind) → ⊥
  del⇒¬ho-abs2 ∅ is ()
  del⇒¬ho-abs2 {lind = lind} (¬∅ x) is refl = λ { hLOsic → del⇒¬ho lind is it}

  del⇒¬ho-abs1 : ∀ {i u} {l : LinLogic i {u}} {il} {r pll : LinLogic i}
                 {ds d} {dls : SetLL (l < il > r)} (s : SetLL (pickLL ds l r))
                 (lind : IndexLL pll (pickLL d l r)) (w : DecICT ds d) →
               ¬∅ dls ≡ del-abs {s = s} lind w → hitsAtLeastOnce dls (ic d lind) → ⊥
  del⇒¬ho-abs1 s lind (yes refl) deq = del⇒¬ho-abs2 (del s lind) refl deq
  del⇒¬ho-abs1 s lind (no x) refl = λ { hLOsic → ⊥-elim (~ict-eq⇒¬ x)}

  del⇒¬ho-abs : ∀ {i u} {l r : LinLogic i {u}} {il} {pll : LinLogic i}
                {d} {lind : IndexLL pll (pickLL d l r)} {dls : SetLL (l < il > r)}
                (w : MSetLL (pickLL d l r)) → (ieq : w ≡ del ↓ lind) →
              ¬∅ dls ≡ pickLLₛ-sbcm d w (¬∅ (pickLLₛ (~ict d) ↓ ↓)) →
              hitsAtLeastOnce dls (ic d lind) → ⊥
  del⇒¬ho-abs {d = ic←} {lind} ∅ ieq refl = λ {()}
  del⇒¬ho-abs {d = ic←} {lind} (¬∅ x) ieq refl = λ { hLOsbc → del⇒¬ho lind ieq it} 
  del⇒¬ho-abs {d = ic→} {lind} ∅ ieq refl = λ {()}
  del⇒¬ho-abs {d = ic→} {lind} (¬∅ x) ieq refl = λ { hLOsbc → del⇒¬ho lind ieq it}


  del⇒¬ho : ∀{i u pll ll} → {s : SetLL ll}
            → (lind : IndexLL {i} {u} pll ll) → ∀{dls}
            → ¬∅ dls ≡ del s lind
            → ¬ (hitsAtLeastOnce dls lind)
  del⇒¬ho {s = s} ↓ ()
  del⇒¬ho {s = ↓} (ic d lind) deq =  del⇒¬ho-abs (del ↓ lind) refl deq 
  del⇒¬ho {s = sic ds s} (ic d lind) deq = del⇒¬ho-abs1 s lind (isEqICT ds d) deq
  del⇒¬ho {s = sbc s s₁} (ic d lind) deq = del⇒¬ho-abs3 lind s s₁ (del (pickLLₛ d s s₁) lind) refl deq

module _ where


  mutual

    del⇒oi-abs2 : ∀ {ds i u} {l : LinLogic i {u}} {il} {r pll : LinLogic i}
                  {s : SetLL (pickLL ds l r)} {lind : IndexLL pll (pickLL ds l r)}
                  (w : MSetLL (pickLL ds l r)) → (ieq : w ≡ del s lind) →
                  (w >>=ₛ (λ z → ¬∅ (sic {il = il} ds z))) ≡ ∅ → 
                  onlyInside (sic {il = il} ds s) (ic ds lind)
    del⇒oi-abs2 ∅ ieq eq = oIic {{ieq = del⇒oi (sym ieq)}}
    del⇒oi-abs2 (¬∅ x) ieq ()

    del⇒oi-abs : ∀ {i u} {l : LinLogic i {u}} {il} {r pll : LinLogic i}
                 {ds} {s : SetLL (pickLL ds l r)} {d}
                 {lind : IndexLL pll (pickLL d l r)} (w : DecICT ds d) →
                 del-abs {s = s} lind w {il = il} ≡ ∅ → onlyInside (sic {il = il} ds s) (ic d lind)
    del⇒oi-abs {s = s} {lind = lind} (yes refl) eq = del⇒oi-abs2 (del s lind) refl eq
    del⇒oi-abs (no x) ()

    del⇒oi : ∀{i u pll ll} → {s : SetLL ll}
                → {lind : IndexLL {i} {u} pll ll}
                → del s lind ≡ ∅
                → onlyInside s lind
    del⇒oi {s = s} {↓} eq = oIs↓
    del⇒oi {s = ↓} {ic d lind} eq = ⊥-elim (∅-neq-¬∅ (trans (sym eq) (proj₂ (pickLLₛ-sbcm¬∅ d (inj₂ (_ , refl))))))
    del⇒oi {s = sic ds s} {ic d lind} eq = del⇒oi-abs (isEqICT ds d) eq
    del⇒oi {s = sbc s s₁} {ic d lind} eq = ⊥-elim (∅-neq-¬∅ (trans (sym eq) (proj₂ (pickLLₛ-sbcm¬∅ d (inj₂ (_ , refl))))))


mutual

  oi⇒del-abs : ∀ {i u} {l r : LinLogic i {u}} {ds}
               {s : SetLL (pickLL ds l r)} {pll : LinLogic i}
               {lind : IndexLL pll (pickLL ds l r)} →
             onlyInside s lind → ∀ (w : DecICT ds ds) {il} → del-abs {s = s} lind w {il = il} ≡ ∅
  oi⇒del-abs {s = s} {lind = lind} oi (yes refl) = cong (λ k → k >>=ₛ _) (oi⇒del {s = s} lind {{oi = oi}})
  oi⇒del-abs oi (no x) = ⊥-elim (~ict-eq⇒¬ x)

  oi⇒del : ∀{i u pll ll} → {s : SetLL ll}
           → (lind : IndexLL {i} {u} pll ll)
           → {{oi : onlyInside s lind}}
           → del s lind ≡ ∅
  oi⇒del {s = s} ↓ = refl
  oi⇒del {s = ↓} (ic d lind) {{()}}
  oi⇒del {s = sic ds s} (ic .ds lind) {{oIic {{ieq = ieq}}}} = oi⇒del-abs ieq (isEqICT ds ds)
  oi⇒del {s = sbc s s₁} (ic d lind) {{()}}


mutual
  
  s-morph-abs : ∀ {i u} {l : LinLogic i {u}} {il} {r q : LinLogic i}
                {ds d} →
              DecICT ds d →
              (s : SetLL (pickLL ds l r)) (ind : IndexLL q (pickLL d l r)) →
              (hitsAtLeastOnce (sic {il = il} ds s) (ic d ind) → ⊥) →
              {rll : LinLogic i} →
              SetLL
              (pickLL d (replLL ind rll) l < il > pickLL d r (replLL ind rll))
  s-morph-abs {ds = ds} (yes refl) s ind ¬ho = sic ds (subst SetLL (trans (pickLL-id ds (replLL ind _)) (sym (pickLL-eq ds pickLL pickLL (replLL ind _)  _ _ (replLL ind _) refl refl)) ) is) where
    is = s-morph s ind λ x → ¬ho (hLOsic {{ieq = x}})
  s-morph-abs {ds = ds} {d = d} (no x) s ind ¬ho = sic ds (subst SetLL (sym (pickLL-neq ds d x pickLL pickLL (replLL ind _)  _ _ (replLL ind _) refl refl)) s)

  s-morph : ∀{i u ll rll q} → (s : SetLL {i} {u} ll) → (ind : IndexLL q ll) → ¬ (hitsAtLeastOnce s ind) → SetLL (replLL ind rll)
  s-morph s ↓ ¬ho = ⊥-elim (¬ho hLOs↓)
  s-morph ↓ (ic d ind) ¬ho = ⊥-elim (¬ho hLO↓ic)
  s-morph (sic ds s) (ic d ind) ¬ho = s-morph-abs (isEqICT ds d) s ind ¬ho
  s-morph (sbc s s₁) (ic d ind) ¬ho = sbc (pickLLₛ d is s) (pickLLₛ d s₁ is) where
    is = s-morph (pickLLₛ d s s₁) ind λ {x → ¬ho (hLOsbc {{ieq = x}})}
  

delG-abs : ∀ {i u} {ll q rll : LinLogic i {u}} {s : SetLL ll} (ind : IndexLL q ll) →
           (w : MSetLL ll) → (eq : w ≡ del s ind) → MSetLL (replLL ind rll)
delG-abs ind ∅ eq = ∅
delG-abs ind (¬∅ x) eq = ¬∅ (s-morph _ ind (del⇒¬ho ind eq))

delG : ∀{i u ll q} → SetLL ll → (ind : IndexLL {i} {u} q ll) → {rll : LinLogic i}
      → MSetLL (replLL ind rll)
delG s ind = delG-abs {s = s} ind (del s ind) refl


s-extend : ∀{i u ll rll} → (ind : IndexLL {i} {u} rll ll) → SetLL {i} rll → SetLL ll
s-extend {ll = ll} {.ll} ↓ s = s
s-extend {ll = .(_ < _ > _)} {rll} (ic d ind) s = sic d (s-extend ind s)

s-extendG : ∀{i u ll q} → ∀{rll} → (ind : IndexLL {i} {u} q ll) → SetLL {i} rll → SetLL (replLL ind rll)
s-extendG ind s = s-extend (ind-rpl↓2 ind (a≤ᵢb-morph ind ind)) s


mutual

  `replacePartOf-abs : ∀ {i u} {l r rll : LinLogic i {u}} {ds d} →
                       SetLL (pickLL ds l r) →
                       SetLL rll →
                       IndexLL rll (pickLL d l r) →
                       DecICT ds d → ∀ {il} → SetLL (l < il > r)
  `replacePartOf-abs {ds = ds} a b ind (yes refl) = sic ds (`replacePartOf a to b at ind)
  `replacePartOf-abs {ds = .(~ict d)} {d} a b ind (no refl) = pickLLₛ-sbc d (s-extend ind b) a


-- It does not delete the contents before replacing, thus it does not work like replacePartOfG.
  `replacePartOf_to_at_ : ∀{i u ll rll} → SetLL ll → SetLL {i} rll → (ind : IndexLL {i} {u} rll ll)
                 → SetLL ll
  `replacePartOf a to b at ↓ = b
  `replacePartOf ↓ to b at ic {il = il} d ind = pickLLₛ-sbc {il = il} d (`replacePartOf ↓ to b at ind) ↓ -- sic d (`replacePartOf ↓ to b at ind)
  `replacePartOf sic ds a to b at ic d ind = `replacePartOf-abs a b ind (isEqICT ds d)
  `replacePartOf sbc a a₁ to b at ic d ind = pickLLₛ-sbc d (`replacePartOf (pickLLₛ d a a₁) to b at ind) (pickLLₛ (~ict d) a a₁)




replacePartOf-abs : ∀ {i u} {ll rll : LinLogic i {u}} {b : SetLL rll} →
                    IndexLL rll ll → MSetLL ll → SetLL ll
replacePartOf-abs {b = b} ind ∅ = s-extend ind b
replacePartOf-abs {b = b} ind (¬∅ x) = `replacePartOf x to b at ind

-- It deletes the contents before replacing so as to be consistent with replacePartOfG.
replacePartOf_to_at_ : ∀{i u ll rll} → SetLL ll → SetLL {i} rll → (ind : IndexLL {i} {u} rll ll)
                       → SetLL ll
replacePartOf a to b at ind = replacePartOf-abs {b = b} ind (del a ind) 



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
  replacePartOfG_to_at_ {rll = rll} a b ind = replacePartOfG-abs {ind = ind} (delG a ind {rll}) b (ind-rpl↓2 ind (a≤ᵢb-morph ind ind {frll = rll}))


  -- Add a node to a set (and potentially replace the linear logic sub-tree).
addG : ∀{i u ll q} → SetLL ll → (ind : IndexLL {i} {u} q ll) → {rll : LinLogic i}
        → SetLL (replLL ind rll)
addG s ind {rll} = replacePartOfG s to ↓ at ind




mreplacePartOf_to_at_ : ∀{i u ll rll} → MSetLL ll → MSetLL {i} rll → (ind : IndexLL {i} {u} rll ll)
          → MSetLL ll
mreplacePartOf ∅ to mb at ind = mapₛ (s-extend ind) mb
mreplacePartOf ¬∅ x to ∅ at ind = del x ind
mreplacePartOf ¬∅ x to ¬∅ x₁ at ind = ¬∅ (replacePartOf x to x₁ at ind)



mreplacePartOfG_to_at_ : ∀{i u ll q} → ∀{rll} → MSetLL ll → MSetLL {i} rll → (ind : IndexLL {i} {u} q ll)
          → MSetLL (replLL ind rll)
mreplacePartOfG_to_at_ {rll = rll} ∅ mb ind = mapₛ (s-extendG ind) mb
mreplacePartOfG ¬∅ x to ∅ at ind = delG x ind
mreplacePartOfG ¬∅ x to ¬∅ x₁ at ind = mreplacePartOf (delG x ind) to (¬∅ x₁) at (ind-rpl↓2 ind (a≤ᵢb-morph ind ind))



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
              DecICT ds ds₁ → Dec (sic {il = il} ds a ≡ sic ds₁ b)
  isEqₛ-abs a b (yes refl) = isEqₛ-abs1 (isEqₛ a b)
  isEqₛ-abs a b (no p) = no λ { refl → ~ict⇒¬≡ p refl}
  
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
             IndexLL pll (pickLL d l r) → DecICT ds d → MSetLL pll
  truncₛ-abs s ind (yes refl) = truncₛ s ind
  truncₛ-abs s ind (no p) = ∅

  truncₛ : ∀ {i u ll pll} → SetLL ll → (ind : IndexLL {i} {u} pll ll)
                → MSetLL pll
  truncₛ s ↓ = ¬∅ s
  truncₛ ↓ (ic d ind) = ¬∅ ↓
  truncₛ (sic ds s) (ic d ind) = truncₛ-abs s ind (isEqICT ds d)
  truncₛ (sbc s s₁) (ic d ind) = truncₛ (pickLLₛ d s s₁) ind

truncₛ-psbc← : ∀ {i u il l r pll} → ∀ d → ∀{s s1} → (ind : IndexLL {i} {u} pll (pickLL d l r)) → truncₛ (pickLLₛ-sbc {il = il} d s s1) (ic d ind) ≡ truncₛ s ind
truncₛ-psbc← ic← ind = refl
truncₛ-psbc← ic→ ind = refl


truncₛ-psbc→ : ∀ {i u il l r pll} → ∀ d → ∀{s s1} → (ind : IndexLL {i} {u} pll (pickLL (~ict d) l r)) → truncₛ (pickLLₛ-sbc {il = il} d s s1) (ic (~ict d) ind) ≡ truncₛ s1 ind
truncₛ-psbc→ ic← ind = refl
truncₛ-psbc→ ic→ ind = refl


truncₛ-sbcm : ∀ {i u il l r pll} → ∀ d ms ms₁ → (ind : IndexLL {i} {u} pll (pickLL d l r)) → sbcm {il = il} ms ms₁ >>=ₛ (λ z → truncₛ z (ic d ind)) ≡ pickLLₘₛ d ms ms₁ >>=ₛ (λ z → truncₛ z ind)
truncₛ-sbcm ic← ∅ ∅ ind = refl
truncₛ-sbcm ic→ ∅ ∅ ind = refl
truncₛ-sbcm ic← ∅ (¬∅ x) ind = refl
truncₛ-sbcm ic→ ∅ (¬∅ x) ind = refl
truncₛ-sbcm ic← (¬∅ x) ∅ ind = refl
truncₛ-sbcm ic→ (¬∅ x) ∅ ind = refl
truncₛ-sbcm ic← (¬∅ x) (¬∅ x₁) ind = refl
truncₛ-sbcm ic→ (¬∅ x) (¬∅ x₁) ind = refl


truncₛ-psbcm← : ∀ {i u il l r pll} → ∀ d → ∀{ms ms₁} → (ind : IndexLL {i} {u} pll (pickLL d l r)) → (pickLLₛ-sbcm {il = il} d ms ms₁) >>=ₛ (λ z → truncₛ z (ic d ind)) ≡ ms >>=ₛ (λ z → truncₛ z ind)
truncₛ-psbcm← ic← {ms} {ms₁} ind =  truncₛ-sbcm ic← ms ms₁ ind 
truncₛ-psbcm← ic→ {ms} {ms₁} ind = truncₛ-sbcm ic→ ms₁ ms ind 


truncₛ-psbcm→ : ∀ {i u il l r pll} → ∀ d → ∀{ms ms₁} → (ind : IndexLL {i} {u} pll (pickLL (~ict d) l r)) → (pickLLₛ-sbcm {il = il} d ms ms₁) >>=ₛ (λ z → truncₛ z (ic (~ict d) ind)) ≡ ms₁ >>=ₛ (λ z → truncₛ z ind)
truncₛ-psbcm→ ic← {ms} {ms₁} ind = truncₛ-sbcm ic→ ms ms₁ ind
truncₛ-psbcm→ ic→ {ms} {ms₁} ind = truncₛ-sbcm ic← ms₁ ms ind




mutual

  tr-fAL : ∀{i u pll ll} → (ind : IndexLL {i} {u} pll ll) →  truncₛ fillAllLower ind ≡ ¬∅ fillAllLower
  tr-fAL ↓ = refl
  tr-fAL (ic d ind) = tr-fAL-p d ind
  
  tr-fAL-p : ∀{i u pll l r} → ∀ d → (ind : IndexLL {i} {u} pll (pickLL d l r))
             →  truncₛ (pickLLₛ d fillAllLower fillAllLower) ind ≡ ¬∅ fillAllLower
  tr-fAL-p ic← ind = tr-fAL ind
  tr-fAL-p ic→ ind = tr-fAL ind


-- truncₛ-psbc : truncₛ (pickLLₛ-sbc d s s1) (ic d ind) ≡

mutual

  tr-ext⇒id-abs : ∀ {i u} {l r pll : LinLogic i {u}} {d} (s : SetLL pll)
                  (ind : IndexLL pll (pickLL d l r)) (w : DecICT d d) →
                  truncₛ-abs (s-extend ind s) ind w ≡ ¬∅ s
  tr-ext⇒id-abs s ind (yes refl) = tr-ext⇒id ind
  tr-ext⇒id-abs s ind (no p) = ⊥-elim (~ict⇒¬≡ p refl)

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

  `tr-repl⇒id-abs : ∀ {d} (w : DecICT d d) {i u}
                   {l r pll : LinLogic i {u}} {s : SetLL (pickLL d l r)} {ind : IndexLL pll (pickLL d l r)}
                   {vs : SetLL pll} →
                 truncₛ-abs (`replacePartOf s to vs at ind) ind w ≡ ¬∅ vs
  `tr-repl⇒id-abs (yes refl) {ind = ind} {vs} = `tr-repl⇒id ind
  `tr-repl⇒id-abs (no p) {ind = ind} {vs} = ⊥-elim (~ict⇒¬≡ p refl)


  `tr-repl⇒id-abs1 : ∀ {ds d} (w : DecICT ds d) {i u}
                    {l : LinLogic i {u}} {il} {r pll : LinLogic i}
                    {s : SetLL (pickLL ds l r)} {ind : IndexLL pll (pickLL d l r)}
                    {vs : SetLL pll} →
                  truncₛ (`replacePartOf-abs s vs ind w {il}) (ic d ind) ≡ ¬∅ vs
  `tr-repl⇒id-abs1 {ds} (yes refl) {s = s} {ind} {vs} = `tr-repl⇒id-abs (isEqICT ds ds)
  `tr-repl⇒id-abs1 {.(~ict d)} {d} (no refl) {s = s} {ind} {vs} = trans (truncₛ-psbc← d ind) (tr-ext⇒id ind)



  `tr-repl⇒id : ∀{i u ll pll} → {s : SetLL ll} → (ind : IndexLL {i} {u} pll ll)
             → {vs : SetLL pll} 
             → let mx = `replacePartOf s to vs at ind in
             truncₛ mx ind ≡ ¬∅ vs
  `tr-repl⇒id {s = s} ↓ {vs} = refl
  `tr-repl⇒id {s = ↓} (ic d ind) {vs} = trans (truncₛ-psbc← d ind) (`tr-repl⇒id ind) 
  `tr-repl⇒id {s = sic ds s} (ic d ind) {vs} = `tr-repl⇒id-abs1 (isEqICT ds d)
  `tr-repl⇒id {s = sbc s s₁} (ic d ind) {vs} = trans (truncₛ-psbc← d ind) (`tr-repl⇒id ind)

mutual

  tr-repl⇒id-abs : ∀ {i u} {ll pll : LinLogic i {u}} {s : SetLL ll}
                   (ind : IndexLL pll ll) {vs : SetLL pll} (w : MSetLL ll) →
                 truncₛ (replacePartOf-abs {b = vs} ind w) ind ≡ ¬∅ vs
  tr-repl⇒id-abs {s = s} ind {vs} ∅ = tr-ext⇒id ind
  tr-repl⇒id-abs {s = s} ind {vs} (¬∅ x) = `tr-repl⇒id ind

  tr-repl⇒id : ∀{i u ll pll} → {s : SetLL ll} → (ind : IndexLL {i} {u} pll ll)
           → {vs : SetLL pll} 
           → let mx = replacePartOf s to vs at ind in
           truncₛ mx ind ≡ ¬∅ vs
  tr-repl⇒id {s = s} ind {vs} = tr-repl⇒id-abs {s = s} ind {vs} (del s ind)


-- This is equal if we first contruct them.
-- If (truncₛ s ind) is not ↓ then, then the statement holds without contruction.
-- Would this be useful though?

--  tr-repl⇒id2 : ∀{i u ll pll} → {s : SetLL ll} → (ind : IndexLL {i} {u} pll ll)
--             → mreplacePartOf (¬∅ s) to (truncₛ s ind) at ind ≡ ¬∅ s


-- TODO Can this be reduced to something simpler?
mutual

  tr-del⇒id-abs : ∀ {i u} {l : LinLogic i {u}} {il} {r pll : LinLogic i}
              {ds d} {s : SetLL (pickLL ds l r)}
              (ind : IndexLL pll (pickLL d l r)) (w : DecICT ds d) →
              truncₛ-abs s ind w ≡ ∅ → del-abs {s = s} ind w ≡ ¬∅ (sic {il = il} ds s)
  tr-del⇒id-abs {s = s} ind (yes refl) eq = cong (λ z → z >>=ₛ _) is  where
    is = tr-del⇒id ind eq
  tr-del⇒id-abs {s = s} ind (no x) eq = refl 

  tr-del⇒id : ∀{i u ll pll} → {s : SetLL ll} → (ind : IndexLL {i} {u} pll ll) → truncₛ s ind ≡ ∅ → del s ind ≡ ¬∅ s
  tr-del⇒id {s = s} ↓ ()
  tr-del⇒id {s = ↓} (ic d ind) ()
  tr-del⇒id {s = sic ds s} (ic d ind) eq = tr-del⇒id-abs {s = s} ind (isEqICT ds d) eq
  tr-del⇒id {s = sbc s s₁} (ic d ind) eq = trans (cong (λ z → pickLLₛ-sbcm d z (¬∅ (pickLLₛ (~ict d) s s₁))) is) (trans (pickLLₛ-sbcm&¬∅⇒pickLLₛ-sbc d (¬∅ (pickLLₛ d s s₁)) (¬∅ (pickLLₛ (~ict d) s s₁)) refl refl) (cong ¬∅ (pickLLₛ-sbc-id d))) where
    is = tr-del⇒id ind eq



mutual

  tr-repl⇒idG-abs : ∀ {i u} {ll ell pll : LinLogic i {u}}
                (ind : IndexLL pll ll) {s : SetLL ll} {vs : SetLL ell}
                (w : MSetLL ll) → (eq : w ≡ del s ind) →
             let tind = ind-rpl↓2 ind (a≤ᵢb-morph ind ind) in
              truncₛ
              (replacePartOfG-abs {ind = ind} (delG-abs ind w eq) vs tind) tind
              ≡ ¬∅ vs
  tr-repl⇒idG-abs ind ∅ eq = tr-ext⇒id (ind-rpl↓2 ind (a≤ᵢb-morph ind ind))
  tr-repl⇒idG-abs ind (¬∅ x) eq = tr-repl⇒id (ind-rpl↓2 ind (a≤ᵢb-morph ind ind))


  tr-repl⇒idG : ∀{i u ll ell pll} → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
           → (vs : SetLL ell) 
           → let mx = replacePartOfG s to vs at ind in
             let tind = ind-rpl↓2 ind (a≤ᵢb-morph ind ind) in
           truncₛ mx tind ≡ ¬∅ vs
  tr-repl⇒idG s ind vs = tr-repl⇒idG-abs ind (del s ind) refl




mutual

  trunc≡¬∅⇒ho-abs : ∀ {i u} {l : LinLogic i {u}} {il}
                    {r rll : LinLogic i} {trs : SetLL rll} {ds}
                    {s : SetLL (pickLL ds l r)} {d} {ind : IndexLL rll (pickLL d l r)}
                    (w : DecICT ds d) →
                  truncₛ-abs s ind w ≡ ¬∅ trs → hitsAtLeastOnce (sic {il = il} ds s) (ic d ind)
  trunc≡¬∅⇒ho-abs (yes refl) eq = hLOsic {{ieq = trunc≡¬∅⇒ho eq}}
  trunc≡¬∅⇒ho-abs (no x) ()
  
  trunc≡¬∅⇒ho : ∀{i u rll ll trs} → {s : SetLL {i} {u} ll} → {ind : IndexLL rll ll} → (truncₛ s ind ≡ ¬∅ trs) → hitsAtLeastOnce s ind
  trunc≡¬∅⇒ho {s = s} {↓} eq = hLOs↓
  trunc≡¬∅⇒ho {s = ↓} {ic d ind} eq = hLO↓ic
  trunc≡¬∅⇒ho {s = sic ds s} {ic d ind} eq = trunc≡¬∅⇒ho-abs (isEqICT ds d) eq
  trunc≡¬∅⇒ho {s = sbc s s₁} {ic d ind} eq = hLOsbc {{ieq = trunc≡¬∅⇒ho eq}}


module _ where

  open Data.Product

  ho⇒trunc≡¬∅-abs : ∀ {i u} {l r : LinLogic i {u}} {ds}
                    {s : SetLL (pickLL ds l r)} {rll : LinLogic i}
                    (ind : IndexLL rll (pickLL ds l r)) (w : DecICT ds ds) →
                   Σ (SetLL rll) (λ trs → truncₛ s ind ≡ ¬∅ trs) →
                  Σ (SetLL rll) (λ trs → truncₛ-abs s ind w ≡ ¬∅ trs)
  ho⇒trunc≡¬∅-abs {ds = ds} ind (yes refl) is = is
  ho⇒trunc≡¬∅-abs {ds = ds} ind (no x) is = ⊥-elim (~ict-eq⇒¬ x)


  ho⇒trunc≡¬∅ : ∀{i u rll ll} → {s : SetLL {i} {u} ll} → (ind : IndexLL rll ll) → {{eq : hitsAtLeastOnce s ind}} → Σ (SetLL rll) (λ trs → truncₛ s ind ≡ ¬∅ trs)
  ho⇒trunc≡¬∅ {s = s} ↓ {{eq}} = s , refl
  ho⇒trunc≡¬∅ {s = ↓} (ic d ind) {{eq}} = ↓ , refl
  ho⇒trunc≡¬∅ {s = sic ds s} (ic .ds ind) {{hLOsic}} = ho⇒trunc≡¬∅-abs ind (isEqICT ds ds) (ho⇒trunc≡¬∅ ind)
  ho⇒trunc≡¬∅ {s = sbc s s₁} (ic d ind) {{hLOsbc}} = ho⇒trunc≡¬∅ ind 





data _⊂ₛ_ {i : Size} {u} : {ll : LinLogic i {u}} → SetLL ll → SetLL ll → Set where
  instance
    ⊂↓   : ∀{ll s} → _⊂ₛ_ {ll = ll} s ↓
    ⊂sic : ∀{lll llr il d sx sy} → {{ieq : _⊂ₛ_ {ll = pickLL d lll llr} sx sy}} → _⊂ₛ_ {ll = lll < il > llr} (sic d sx) (sic d sy)
    ⊂sbc : ∀{lll llr il slx sly srx sry} → {{ieql : _⊂ₛ_ {ll = lll} slx sly}} → {{ieqr : _⊂ₛ_ {ll = llr} srx sry}} → _⊂ₛ_ {ll = lll < il > llr} (sbc slx srx) (sbc sly sry)
    ⊂dsbc : ∀{lll llr il d sx sly sry} → {{ieq : _⊂ₛ_ sx (pickLLₛ d sly sry)}} → _⊂ₛ_ {ll = lll < il > llr} (sic d sx) (sbc sly sry)


data _⊂ₘₛ_ {i : Size} {u} : {ll : LinLogic i {u}} → MSetLL ll → MSetLL ll → Set where
  instance
    ⊂∅ : ∀{ll ms} → _⊂ₘₛ_ {ll = ll} ∅ ms
    ⊂ic : ∀{ll s s₁} → {{eq : _⊂ₛ_ {ll = ll} s s₁}} → (¬∅ s) ⊂ₘₛ (¬∅ s₁)


⊂ₛ-ext : ∀{i u pll ll ss} → (ind : IndexLL {i} {u} pll ll) → {s : SetLL pll} → {{rl : ss ⊂ₛ s }} → s-extend ind ss ⊂ₛ s-extend ind s
⊂ₛ-ext ↓ {{rl}} = rl
⊂ₛ-ext (ic d ind) = ⊂sic {{ieq = ⊂ₛ-ext ind}}


instance
  ⊂ₛ-refl : ∀{i u ll} → {s : SetLL {i} {u} ll} → s ⊂ₛ s
  ⊂ₛ-refl {s = ↓} = ⊂↓
  ⊂ₛ-refl {s = sic ds s} = ⊂sic
  ⊂ₛ-refl {s = sbc s s₁} = ⊂sbc

⊂ₛ-pickLLₛ : ∀{i u l r} → {s ss : SetLL {i} {u} l} → {s₁ ss₁ : SetLL {i} {u} r} → ∀ d
             → {{eq : s ⊂ₛ ss}} → {{eq1 : s₁ ⊂ₛ ss₁}} → pickLLₛ d s s₁ ⊂ₛ pickLLₛ d ss ss₁
⊂ₛ-pickLLₛ ic← = it
⊂ₛ-pickLLₛ ic→ = it

⊂ₛ-trans : ∀{i u ll b c} → {a : SetLL {i} {u} ll} → a ⊂ₛ b → b ⊂ₛ c → a ⊂ₛ c
⊂ₛ-trans x ⊂↓ = ⊂↓
⊂ₛ-trans ⊂sic (⊂sic {{ieq = ieqy}}) = ⊂sic {{ieq = ⊂ₛ-trans it ieqy}}
⊂ₛ-trans ⊂sbc (⊂sbc {{ieql = ieql}} {{ieqr = ieqr}}) = ⊂sbc {{ieql = ⊂ₛ-trans it ieql}} {{ieqr = ⊂ₛ-trans it ieqr}}
⊂ₛ-trans (⊂dsbc {d = ic←}) (⊂sbc {{ieql = ieq}}) = ⊂dsbc {{ieq = ⊂ₛ-trans it ieq}}
⊂ₛ-trans (⊂dsbc {d = ic→}) (⊂sbc {{ieqr = ieq}}) = ⊂dsbc {{ieq = ⊂ₛ-trans it ieq}}
⊂ₛ-trans ⊂sic (⊂dsbc {{ieq = ieq}}) = ⊂dsbc {{ieq = ⊂ₛ-trans it ieq}}


instance
  ⊂ₘₛ↓ : ∀{i u} {ll : LinLogic i {u}} → {ms : MSetLL ll} → ms ⊂ₘₛ ¬∅ ↓
  ⊂ₘₛ↓ {ms = ∅} = ⊂∅
  ⊂ₘₛ↓ {ms = ¬∅ x} = ⊂ic







-- The ⊂ₛs relationship and hitsAtLeastOnce and onlyInside

oi&ss⊂ₛs⇒oiss : ∀ {i u ll pll} → (s ss : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
               → {{oi : onlyInside s ind}} → {{eq : ss ⊂ₛ s}} → onlyInside ss ind
oi&ss⊂ₛs⇒oiss .↓ ss .↓ {{oIs↓}} {{⊂↓}} = oIs↓
oi&ss⊂ₛs⇒oiss .(sic _ _) .(sic _ _) .↓ {{oIs↓}} {{⊂sic}} = oIs↓
oi&ss⊂ₛs⇒oiss (sic _ s) (sic _ ss) (ic _ ind) {{oIic}} {{⊂sic}} = oIic {{ieq = oi&ss⊂ₛs⇒oiss s ss ind}}
oi&ss⊂ₛs⇒oiss .(sbc _ _) .(sbc _ _) .↓ {{oIs↓}} {{⊂sbc}} = oIs↓
oi&ss⊂ₛs⇒oiss .(sbc _ _) .(sic _ _) .↓ {{oIs↓}} {{⊂dsbc}} = oIs↓



ho&s⊂ₛss⇒hoss : ∀ {i u ll pll} → (s ss : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
               → {{ho : hitsAtLeastOnce s ind}} → {{eq : s ⊂ₛ ss}} → hitsAtLeastOnce ss ind
ho&s⊂ₛss⇒hoss .↓ .↓ .(ic _ _) {{hLO↓ic}} {{⊂↓}} = hLO↓ic
ho&s⊂ₛss⇒hoss s .↓ .↓ {{hLOs↓}} {{⊂↓}} = hLOs↓
ho&s⊂ₛss⇒hoss .(sic _ _) .↓ .(ic _ _) {{hLOsic}} {{⊂↓}} = hLO↓ic
ho&s⊂ₛss⇒hoss .(sbc _ _) .↓ .(ic _ _) {{hLOsbc}} {{⊂↓}} = hLO↓ic
ho&s⊂ₛss⇒hoss .(sic _ _) .(sic _ _) .↓ {{hLOs↓}} {{⊂sic}} = hLOs↓
ho&s⊂ₛss⇒hoss (sic _ s) (sic _ ss) (ic _ ind) {{hLOsic}} {{⊂sic}} = hLOsic {{ieq = ho&s⊂ₛss⇒hoss s ss ind}}
ho&s⊂ₛss⇒hoss (sbc _ s) (sbc _ ss) .↓ {{hLOs↓}} {{⊂sbc}} = hLOs↓
ho&s⊂ₛss⇒hoss (sbc s s1) (sbc ss ss1) (ic d ind) {{hLOsbc}} {{⊂sbc}} = hLOsbc {{ieq = ho&s⊂ₛss⇒hoss (pickLLₛ d s s1) (pickLLₛ d ss ss1) ind {{eq = ⊂ₛ-pickLLₛ d}}}}
ho&s⊂ₛss⇒hoss (sic _ s) (sbc _ ss) .↓ {{hLOs↓}} {{⊂dsbc}} = hLOs↓
ho&s⊂ₛss⇒hoss (sic _ s) (sbc ss ss1) (ic d ind) {{hLOsic}} {{⊂dsbc}} = hLOsbc {{ieq = ho&s⊂ₛss⇒hoss s (pickLLₛ d ss ss1) ind}}



¬ho&s⊂ₛss⇒¬hos : ∀ {i u ll pll} → (s ss : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
                → ¬ (hitsAtLeastOnce ss ind) → {{eq : s ⊂ₛ ss}} → ¬ (hitsAtLeastOnce s ind)
¬ho&s⊂ₛss⇒¬hos s ss ind ¬ho x = x asInst ¬ho (ho&s⊂ₛss⇒hoss s ss ind)





mutual

  ⊂&tr⇒⊂-abs1 : ∀ {i u} {l r : LinLogic i {u}} {ds} {pll : LinLogic i}
                {d} (ind : IndexLL pll (pickLL d l r)) (w : DecICT ds d)
                {s : SetLL (pickLL ds l r)} {ss : SetLL l} {ss₁ : SetLL r} → {{eq : s ⊂ₛ pickLLₛ ds ss ss₁ }} →
              truncₛ-abs s ind w ⊂ₘₛ truncₛ (pickLLₛ d ss ss₁) ind
  ⊂&tr⇒⊂-abs1 ind (yes refl) = ⊂&tr⇒⊂ ind
  ⊂&tr⇒⊂-abs1 ind (no x) = ⊂∅

  ⊂&tr⇒⊂-abs : ∀ {i u} {l r : LinLogic i {u}} {ds} {pll : LinLogic i} {d}
               (ind : IndexLL pll (pickLL d l r)) (w : DecICT ds d)
               {s ss : SetLL (pickLL ds l r)} → {{eq : s ⊂ₛ ss}} →
             truncₛ-abs s ind w ⊂ₘₛ truncₛ-abs ss ind w
  ⊂&tr⇒⊂-abs ind (yes refl) = ⊂&tr⇒⊂ ind
  ⊂&tr⇒⊂-abs ind (no x) = ⊂∅


  ⊂&tr⇒⊂ : ∀{i u pll ll} → ∀{s ss} → (ind : IndexLL {i} {u} pll ll) → {{eq : s ⊂ₛ ss}}
           → truncₛ s ind ⊂ₘₛ truncₛ ss ind
  ⊂&tr⇒⊂ {s = s} {ss} ↓ = ⊂ic
  ⊂&tr⇒⊂ {s = ↓} {.↓} (ic d ind) {{⊂↓}} = ⊂ic
  ⊂&tr⇒⊂ {s = sic ds s} {↓} (ic d ind) = ⊂ₘₛ↓
  ⊂&tr⇒⊂ {s = sic ds s} {sic .ds ss} (ic d ind) {{⊂sic}} = ⊂&tr⇒⊂-abs ind (isEqICT ds d) 
  ⊂&tr⇒⊂ {s = sic ds s} {sbc ss ss₁} (ic d ind) {{⊂dsbc}} = ⊂&tr⇒⊂-abs1 ind (isEqICT ds d)
  ⊂&tr⇒⊂ {s = sbc s s₁} {↓} (ic d ind) {{eq}} = it 
  ⊂&tr⇒⊂ {s = sbc s s₁} {sic ds ss} (ic d ind) {{()}}
  ⊂&tr⇒⊂ {s = sbc s s₁} {sbc ss ss₁} (ic d ind) {{⊂sbc}} = ⊂&tr⇒⊂ ind {{eq = ⊂ₛ-pickLLₛ d}}



tr-ext⇒⊂-abs : ∀ {i u} {l : LinLogic i {u}} {il} {r pll : LinLogic i}
                 {s : SetLL l} {s₁ : SetLL r} {d} (ind : IndexLL pll (pickLL d l r))
                 (w : MSetLL pll) →
               (w >>=ₛ (λ z → ¬∅ (s-extend ind z))) ⊂ₘₛ ¬∅ (pickLLₛ d s s₁) →
               (w >>=ₛ (λ z → ¬∅ (sic {il = il} d (s-extend ind z)))) ⊂ₘₛ ¬∅ (sbc s s₁)
tr-ext⇒⊂-abs ind ∅ is = ⊂∅
tr-ext⇒⊂-abs ind (¬∅ x) ⊂ic = it


tr-ext⇒⊂-abs2 : ∀ {ds i u} {l r pll : LinLogic i {u}} {il}
                  {s : SetLL (pickLL ds l r)} (ind : IndexLL pll (pickLL ds l r))
                  (w : MSetLL pll) →
                (w >>=ₛ (λ z → ¬∅ (s-extend ind z))) ⊂ₘₛ ¬∅ s →
                (w >>=ₛ (λ z → ¬∅ (sic {il = il} ds (s-extend ind z)))) ⊂ₘₛ ¬∅ (sic ds s)
tr-ext⇒⊂-abs2 ind ∅ is = ⊂∅
tr-ext⇒⊂-abs2 ind (¬∅ x) ⊂ic = ⊂ic

mutual

  tr-ext⇒⊂-abs1 : ∀ {i u} {l r pll : LinLogic i {u}} {ds d}
                  (ind : IndexLL pll (pickLL d l r)) (w : DecICT ds d) {il}
                  {s : SetLL (pickLL ds l r)} →
                (truncₛ-abs s ind w >>=ₛ (λ z → ¬∅ (sic {il = il} d (s-extend ind z)))) ⊂ₘₛ
                ¬∅ (sic ds s)
  tr-ext⇒⊂-abs1 {ds = ds} ind (yes refl) {s = s} =  tr-ext⇒⊂-abs2 ind (truncₛ s ind) is   where
    is = tr-ext⇒⊂ {s = s} ind
  tr-ext⇒⊂-abs1 ind (no x) = ⊂∅

  instance
    tr-ext⇒⊂ : ∀{i u pll ll} → ∀ {s} → (ind : IndexLL {i} {u} pll ll) → (truncₛ s ind >>=ₛ (λ z → ¬∅ (s-extend ind z))) ⊂ₘₛ (¬∅ s)
    tr-ext⇒⊂ {s = s} ↓ = ⊂ic
    tr-ext⇒⊂ {s = ↓} (ic d ind) = ⊂ic
    tr-ext⇒⊂ {s = sic ds s} (ic d ind) = tr-ext⇒⊂-abs1 ind (isEqICT ds d)
    tr-ext⇒⊂ {s = sbc s s₁} (ic d ind) = tr-ext⇒⊂-abs ind (truncₛ (pickLLₛ d s s₁) ind) is where
      is = tr-ext⇒⊂ {s = pickLLₛ d s s₁} ind


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




