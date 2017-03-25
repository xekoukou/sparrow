module SetLLProp where

open import Common
open import LinLogic
open import SetLL



module _ where


  data onlyInside {i u rll} : ∀{ll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → Set where
    onlyInsideCs↓ : ∀{s} → onlyInside {ll = rll} s ↓
    onlyInsideC←∧←∧ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = ll ∧ q} (s ←∧) (ind ←∧)
    onlyInsideC∧→∧→ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = q ∧ ll} (∧→ s) (∧→ ind)
    onlyInsideC←∨←∨ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = ll ∨ q} (s ←∨) (ind ←∨)
    onlyInsideC∨→∨→ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = q ∨ ll} (∨→ s) (∨→ ind)
    onlyInsideC←∂←∂ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = ll ∂ q} (s ←∂) (ind ←∂)
    onlyInsideC∂→∂→ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = q ∂ ll} (∂→ s) (∂→ ind)




  onlyInsideUnique : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) 
                   → (a : onlyInside s ind) → (b : onlyInside s ind)
                   → a ≡ b
  onlyInsideUnique ↓ ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
  onlyInsideUnique ↓ (ind ←∧) () b
  onlyInsideUnique ↓ (∧→ ind) () b
  onlyInsideUnique ↓ (ind ←∨) () b
  onlyInsideUnique ↓ (∨→ ind) () b
  onlyInsideUnique ↓ (ind ←∂) () b
  onlyInsideUnique ↓ (∂→ ind) () b
  onlyInsideUnique (s ←∧) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
  onlyInsideUnique (s ←∧) (ind ←∧) (onlyInsideC←∧←∧ a) (onlyInsideC←∧←∧ b) with (onlyInsideUnique s ind a b)
  onlyInsideUnique (s ←∧) (ind ←∧) (onlyInsideC←∧←∧ a) (onlyInsideC←∧←∧ .a) | refl = refl
  onlyInsideUnique (s ←∧) (∧→ ind) () b
  onlyInsideUnique (∧→ s) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
  onlyInsideUnique (∧→ s) (ind ←∧) () b
  onlyInsideUnique (∧→ s) (∧→ ind) (onlyInsideC∧→∧→ a) (onlyInsideC∧→∧→ b) with (onlyInsideUnique s ind a b)
  onlyInsideUnique (∧→ s) (∧→ ind) (onlyInsideC∧→∧→ a) (onlyInsideC∧→∧→ .a) | refl = refl
  onlyInsideUnique (s ←∧→ s₁) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
  onlyInsideUnique (s ←∧→ s₁) (ind ←∧) () b
  onlyInsideUnique (s ←∧→ s₁) (∧→ ind) () b
  onlyInsideUnique (s ←∨) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
  onlyInsideUnique (s ←∨) (ind ←∨) (onlyInsideC←∨←∨ a) (onlyInsideC←∨←∨ b) with (onlyInsideUnique s ind a b)
  onlyInsideUnique (s ←∨) (ind ←∨) (onlyInsideC←∨←∨ a) (onlyInsideC←∨←∨ .a) | refl = refl
  onlyInsideUnique (s ←∨) (∨→ ind) () b
  onlyInsideUnique (∨→ s) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
  onlyInsideUnique (∨→ s) (ind ←∨) () b
  onlyInsideUnique (∨→ s) (∨→ ind) (onlyInsideC∨→∨→ a) (onlyInsideC∨→∨→ b) with (onlyInsideUnique s ind a b)
  onlyInsideUnique (∨→ s) (∨→ ind) (onlyInsideC∨→∨→ a) (onlyInsideC∨→∨→ .a) | refl = refl
  onlyInsideUnique (s ←∨→ s₁) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
  onlyInsideUnique (s ←∨→ s₁) (ind ←∨) () b
  onlyInsideUnique (s ←∨→ s₁) (∨→ ind) () b
  onlyInsideUnique (s ←∂) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
  onlyInsideUnique (s ←∂) (ind ←∂) (onlyInsideC←∂←∂ a) (onlyInsideC←∂←∂ b) with (onlyInsideUnique s ind a b)
  onlyInsideUnique (s ←∂) (ind ←∂) (onlyInsideC←∂←∂ a) (onlyInsideC←∂←∂ .a) | refl = refl
  onlyInsideUnique (s ←∂) (∂→ ind) () b
  onlyInsideUnique (∂→ s) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
  onlyInsideUnique (∂→ s) (ind ←∂) () b
  onlyInsideUnique (∂→ s) (∂→ ind) (onlyInsideC∂→∂→ a) (onlyInsideC∂→∂→ b) with (onlyInsideUnique s ind a b)
  onlyInsideUnique (∂→ s) (∂→ ind) (onlyInsideC∂→∂→ a) (onlyInsideC∂→∂→ .a) | refl = refl
  onlyInsideUnique (s ←∂→ s₁) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
  onlyInsideUnique (s ←∂→ s₁) (ind ←∂) () b
  onlyInsideUnique (s ←∂→ s₁) (∂→ ind) () b


  isOnlyInside : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → Dec (onlyInside s ind)
  isOnlyInside ↓ ↓ = yes onlyInsideCs↓
  isOnlyInside ↓ (ind ←∧) = no (λ ())
  isOnlyInside ↓ (∧→ ind) = no (λ ())
  isOnlyInside ↓ (ind ←∨) = no (λ ())
  isOnlyInside ↓ (∨→ ind) = no (λ ())
  isOnlyInside ↓ (ind ←∂) = no (λ ())
  isOnlyInside ↓ (∂→ ind) = no (λ ())
  isOnlyInside (s ←∧) ↓ = yes onlyInsideCs↓
  isOnlyInside (s ←∧) (ind ←∧) with (isOnlyInside s ind)
  isOnlyInside (s ←∧) (ind ←∧) | yes p = yes (onlyInsideC←∧←∧ p)
  isOnlyInside (s ←∧) (ind ←∧) | no ¬p = no (λ {(onlyInsideC←∧←∧ x) → ¬p x})
  isOnlyInside (s ←∧) (∧→ ind) = no (λ ())
  isOnlyInside (∧→ s) ↓ = yes onlyInsideCs↓
  isOnlyInside (∧→ s) (ind ←∧) = no (λ ())
  isOnlyInside (∧→ s) (∧→ ind) with (isOnlyInside s ind)
  isOnlyInside (∧→ s) (∧→ ind) | yes p = yes (onlyInsideC∧→∧→ p)
  isOnlyInside (∧→ s) (∧→ ind) | no ¬p = no (λ { (onlyInsideC∧→∧→ x) → ¬p x})
  isOnlyInside (s ←∧→ s₁) ↓ = yes onlyInsideCs↓
  isOnlyInside (s ←∧→ s₁) (ind ←∧) = no (λ ())
  isOnlyInside (s ←∧→ s₁) (∧→ ind) = no (λ ())
  isOnlyInside (s ←∨) ↓ = yes onlyInsideCs↓
  isOnlyInside (s ←∨) (ind ←∨) with (isOnlyInside s ind)
  isOnlyInside (s ←∨) (ind ←∨) | yes p = yes (onlyInsideC←∨←∨ p)
  isOnlyInside (s ←∨) (ind ←∨) | no ¬p = no ( λ { (onlyInsideC←∨←∨ x) → ¬p x})
  isOnlyInside (s ←∨) (∨→ ind) = no (λ ())
  isOnlyInside (∨→ s) ↓ = yes onlyInsideCs↓
  isOnlyInside (∨→ s) (ind ←∨) = no (λ ())
  isOnlyInside (∨→ s) (∨→ ind) with (isOnlyInside s ind)
  isOnlyInside (∨→ s) (∨→ ind) | yes p = yes (onlyInsideC∨→∨→ p)
  isOnlyInside (∨→ s) (∨→ ind) | no ¬p = no ( λ { (onlyInsideC∨→∨→ x) → ¬p x})
  isOnlyInside (s ←∨→ s₁) ↓ = yes onlyInsideCs↓
  isOnlyInside (s ←∨→ s₁) (ind ←∨) = no (λ ())
  isOnlyInside (s ←∨→ s₁) (∨→ ind) = no (λ ())
  isOnlyInside (s ←∂) ↓ = yes onlyInsideCs↓
  isOnlyInside (s ←∂) (ind ←∂) with (isOnlyInside s ind)
  isOnlyInside (s ←∂) (ind ←∂) | yes p = yes (onlyInsideC←∂←∂ p)
  isOnlyInside (s ←∂) (ind ←∂) | no ¬p = no ( λ { (onlyInsideC←∂←∂ x) → ¬p x})
  isOnlyInside (s ←∂) (∂→ ind) = no (λ ())
  isOnlyInside (∂→ s) ↓ = yes onlyInsideCs↓
  isOnlyInside (∂→ s) (ind ←∂) = no (λ ())
  isOnlyInside (∂→ s) (∂→ ind) with (isOnlyInside s ind)
  isOnlyInside (∂→ s) (∂→ ind) | yes p = yes (onlyInsideC∂→∂→ p)
  isOnlyInside (∂→ s) (∂→ ind) | no ¬p = no (λ { (onlyInsideC∂→∂→ x) → ¬p x})
  isOnlyInside (s ←∂→ s₁) ↓ = yes onlyInsideCs↓
  isOnlyInside (s ←∂→ s₁) (ind ←∂) = no (λ ())
  isOnlyInside (s ←∂→ s₁) (∂→ ind) = no (λ ())





-- It hits at least once.

  data hitsAtLeastOnce {i u} : ∀{ll rll} → SetLL ll → (ind : IndexLL {i} {u} rll ll) → Set where
    hitsAtLeastOnce↓     : ∀{ll rll ind}                                 → hitsAtLeastOnce {ll = ll} {rll = rll} ↓ ind
    hitsAtLeastOnce←∧↓   : ∀{lll llr s}                                  → hitsAtLeastOnce {ll = lll ∧ llr} {rll = lll ∧ llr} (s ←∧) ↓
    hitsAtLeastOnce←∧←∧  : ∀{ll rll s q ind}    → hitsAtLeastOnce s ind  → hitsAtLeastOnce {ll = ll ∧ q} {rll = rll} (s ←∧) (ind ←∧)
    hitsAtLeastOnce∧→↓   : ∀{lll llr s}                                  → hitsAtLeastOnce {ll = lll ∧ llr} {rll = lll ∧ llr} (∧→ s) ↓
    hitsAtLeastOnce∧→∧→  : ∀{ll rll s q ind}    → hitsAtLeastOnce s ind  → hitsAtLeastOnce {ll = q ∧ ll} {rll = rll} (∧→ s) (∧→ ind) 
    hitsAtLeastOnce←∧→↓  : ∀{lll llr s s₁}                               → hitsAtLeastOnce {ll = lll ∧ llr} {rll = lll ∧ llr} (s ←∧→ s₁) ↓
    hitsAtLeastOnce←∧→←∧ : ∀{ll rll s q s₁ ind} → hitsAtLeastOnce s ind  → hitsAtLeastOnce {ll = ll ∧ q} {rll = rll} (s ←∧→ s₁) (ind ←∧)
    hitsAtLeastOnce←∧→∧→ : ∀{ll rll q s s₁ ind} → hitsAtLeastOnce s₁ ind → hitsAtLeastOnce {ll = q ∧ ll} {rll = rll} (s ←∧→ s₁) (∧→ ind) 
    hitsAtLeastOnce←∨↓   : ∀{lll llr s}                                  → hitsAtLeastOnce {ll = lll ∨ llr} {rll = lll ∨ llr} (s ←∨) ↓
    hitsAtLeastOnce←∨←∨  : ∀{ll rll s q ind}    → hitsAtLeastOnce s ind  → hitsAtLeastOnce {ll = ll ∨ q} {rll = rll} (s ←∨) (ind ←∨)
    hitsAtLeastOnce∨→↓   : ∀{lll llr s}                                  → hitsAtLeastOnce {ll = lll ∨ llr} {rll = lll ∨ llr} (∨→ s) ↓
    hitsAtLeastOnce∨→∨→  : ∀{ll rll s q ind}    → hitsAtLeastOnce s ind  → hitsAtLeastOnce {ll = q ∨ ll} {rll = rll} (∨→ s) (∨→ ind) 
    hitsAtLeastOnce←∨→↓  : ∀{lll llr s s₁}                               → hitsAtLeastOnce {ll = lll ∨ llr} {rll = lll ∨ llr} (s ←∨→ s₁) ↓
    hitsAtLeastOnce←∨→←∨ : ∀{ll rll s q s₁ ind} → hitsAtLeastOnce s ind  → hitsAtLeastOnce {ll = ll ∨ q} {rll = rll} (s ←∨→ s₁) (ind ←∨)
    hitsAtLeastOnce←∨→∨→ : ∀{ll rll q s s₁ ind} → hitsAtLeastOnce s₁ ind → hitsAtLeastOnce {ll = q ∨ ll} {rll = rll} (s ←∨→ s₁) (∨→ ind) 
    hitsAtLeastOnce←∂↓   : ∀{lll llr s}                                  → hitsAtLeastOnce {ll = lll ∂ llr} {rll = lll ∂ llr} (s ←∂) ↓
    hitsAtLeastOnce←∂←∂  : ∀{ll rll s q ind}    → hitsAtLeastOnce s ind  → hitsAtLeastOnce {ll = ll ∂ q} {rll = rll} (s ←∂) (ind ←∂)
    hitsAtLeastOnce∂→↓   : ∀{lll llr s}                                  → hitsAtLeastOnce {ll = lll ∂ llr} {rll = lll ∂ llr} (∂→ s) ↓
    hitsAtLeastOnce∂→∂→  : ∀{ll rll s q ind}    → hitsAtLeastOnce s ind  → hitsAtLeastOnce {ll = q ∂ ll} {rll = rll} (∂→ s) (∂→ ind) 
    hitsAtLeastOnce←∂→↓  : ∀{lll llr s s₁}                               → hitsAtLeastOnce {ll = lll ∂ llr} {rll = lll ∂ llr} (s ←∂→ s₁) ↓
    hitsAtLeastOnce←∂→←∂ : ∀{ll rll s q s₁ ind} → hitsAtLeastOnce s ind  → hitsAtLeastOnce {ll = ll ∂ q} {rll = rll} (s ←∂→ s₁) (ind ←∂)
    hitsAtLeastOnce←∂→∂→ : ∀{ll rll q s s₁ ind} → hitsAtLeastOnce s₁ ind → hitsAtLeastOnce {ll = q ∂ ll} {rll = rll} (s ←∂→ s₁) (∂→ ind) 

  hitsAtLeastOnceUnique : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → (a : hitsAtLeastOnce s ind) → (b : hitsAtLeastOnce s ind) → a ≡ b
  hitsAtLeastOnceUnique ↓ ind hitsAtLeastOnce↓ hitsAtLeastOnce↓ = refl
  hitsAtLeastOnceUnique (s ←∧) ↓ hitsAtLeastOnce←∧↓ hitsAtLeastOnce←∧↓ = refl
  hitsAtLeastOnceUnique (s ←∧) (ind ←∧) (hitsAtLeastOnce←∧←∧ a) (hitsAtLeastOnce←∧←∧ b) with (hitsAtLeastOnceUnique s ind a b)
  hitsAtLeastOnceUnique (s ←∧) (ind ←∧) (hitsAtLeastOnce←∧←∧ a) (hitsAtLeastOnce←∧←∧ .a) | refl = refl
  hitsAtLeastOnceUnique (s ←∧) (∧→ ind) () b
  hitsAtLeastOnceUnique (∧→ s) ↓ hitsAtLeastOnce∧→↓ hitsAtLeastOnce∧→↓ = refl
  hitsAtLeastOnceUnique (∧→ s) (ind ←∧) () b
  hitsAtLeastOnceUnique (∧→ s) (∧→ ind) (hitsAtLeastOnce∧→∧→ a) (hitsAtLeastOnce∧→∧→ b) with (hitsAtLeastOnceUnique s ind a b)
  hitsAtLeastOnceUnique (∧→ s) (∧→ ind) (hitsAtLeastOnce∧→∧→ a) (hitsAtLeastOnce∧→∧→ .a) | refl = refl
  hitsAtLeastOnceUnique (s ←∧→ s₁) ↓ hitsAtLeastOnce←∧→↓ hitsAtLeastOnce←∧→↓ = refl
  hitsAtLeastOnceUnique (s ←∧→ s₁) (ind ←∧) (hitsAtLeastOnce←∧→←∧ a) (hitsAtLeastOnce←∧→←∧ b) with (hitsAtLeastOnceUnique s ind a b)
  hitsAtLeastOnceUnique (s ←∧→ s₁) (ind ←∧) (hitsAtLeastOnce←∧→←∧ a) (hitsAtLeastOnce←∧→←∧ .a) | refl = refl
  hitsAtLeastOnceUnique (s ←∧→ s₁) (∧→ ind) (hitsAtLeastOnce←∧→∧→ a) (hitsAtLeastOnce←∧→∧→ b) with (hitsAtLeastOnceUnique s₁ ind a b)
  hitsAtLeastOnceUnique (s ←∧→ s₁) (∧→ ind) (hitsAtLeastOnce←∧→∧→ a) (hitsAtLeastOnce←∧→∧→ .a) | refl = refl
  hitsAtLeastOnceUnique (s ←∨) ↓ hitsAtLeastOnce←∨↓ hitsAtLeastOnce←∨↓ = refl
  hitsAtLeastOnceUnique (s ←∨) (ind ←∨) (hitsAtLeastOnce←∨←∨ a) (hitsAtLeastOnce←∨←∨ b) with (hitsAtLeastOnceUnique s ind a b)
  hitsAtLeastOnceUnique (s ←∨) (ind ←∨) (hitsAtLeastOnce←∨←∨ a) (hitsAtLeastOnce←∨←∨ .a) | refl = refl
  hitsAtLeastOnceUnique (s ←∨) (∨→ ind) () b
  hitsAtLeastOnceUnique (∨→ s) ↓ hitsAtLeastOnce∨→↓ hitsAtLeastOnce∨→↓ = refl
  hitsAtLeastOnceUnique (∨→ s) (ind ←∨) () b
  hitsAtLeastOnceUnique (∨→ s) (∨→ ind) (hitsAtLeastOnce∨→∨→ a) (hitsAtLeastOnce∨→∨→ b) with (hitsAtLeastOnceUnique s ind a b)
  hitsAtLeastOnceUnique (∨→ s) (∨→ ind) (hitsAtLeastOnce∨→∨→ a) (hitsAtLeastOnce∨→∨→ .a) | refl = refl
  hitsAtLeastOnceUnique (s ←∨→ s₁) ↓ hitsAtLeastOnce←∨→↓ hitsAtLeastOnce←∨→↓ = refl
  hitsAtLeastOnceUnique (s ←∨→ s₁) (ind ←∨) (hitsAtLeastOnce←∨→←∨ a) (hitsAtLeastOnce←∨→←∨ b) with (hitsAtLeastOnceUnique s ind a b)
  hitsAtLeastOnceUnique (s ←∨→ s₁) (ind ←∨) (hitsAtLeastOnce←∨→←∨ a) (hitsAtLeastOnce←∨→←∨ .a) | refl = refl
  hitsAtLeastOnceUnique (s ←∨→ s₁) (∨→ ind) (hitsAtLeastOnce←∨→∨→ a) (hitsAtLeastOnce←∨→∨→ b) with (hitsAtLeastOnceUnique s₁ ind a b)
  hitsAtLeastOnceUnique (s ←∨→ s₁) (∨→ ind) (hitsAtLeastOnce←∨→∨→ a) (hitsAtLeastOnce←∨→∨→ .a) | refl = refl
  hitsAtLeastOnceUnique (s ←∂) ↓ hitsAtLeastOnce←∂↓ hitsAtLeastOnce←∂↓ = refl
  hitsAtLeastOnceUnique (s ←∂) (ind ←∂) (hitsAtLeastOnce←∂←∂ a) (hitsAtLeastOnce←∂←∂ b) with (hitsAtLeastOnceUnique s ind a b)
  hitsAtLeastOnceUnique (s ←∂) (ind ←∂) (hitsAtLeastOnce←∂←∂ a) (hitsAtLeastOnce←∂←∂ .a) | refl = refl
  hitsAtLeastOnceUnique (s ←∂) (∂→ ind) () b
  hitsAtLeastOnceUnique (∂→ s) ↓ hitsAtLeastOnce∂→↓ hitsAtLeastOnce∂→↓ = refl
  hitsAtLeastOnceUnique (∂→ s) (ind ←∂) () b
  hitsAtLeastOnceUnique (∂→ s) (∂→ ind) (hitsAtLeastOnce∂→∂→ a) (hitsAtLeastOnce∂→∂→ b) with (hitsAtLeastOnceUnique s ind a b)
  hitsAtLeastOnceUnique (∂→ s) (∂→ ind) (hitsAtLeastOnce∂→∂→ a) (hitsAtLeastOnce∂→∂→ .a) | refl = refl
  hitsAtLeastOnceUnique (s ←∂→ s₁) ↓ hitsAtLeastOnce←∂→↓ hitsAtLeastOnce←∂→↓ = refl
  hitsAtLeastOnceUnique (s ←∂→ s₁) (ind ←∂) (hitsAtLeastOnce←∂→←∂ a) (hitsAtLeastOnce←∂→←∂ b) with (hitsAtLeastOnceUnique s ind a b)
  hitsAtLeastOnceUnique (s ←∂→ s₁) (ind ←∂) (hitsAtLeastOnce←∂→←∂ a) (hitsAtLeastOnce←∂→←∂ .a) | refl = refl
  hitsAtLeastOnceUnique (s ←∂→ s₁) (∂→ ind) (hitsAtLeastOnce←∂→∂→ a) (hitsAtLeastOnce←∂→∂→ b) with (hitsAtLeastOnceUnique s₁ ind a b)
  hitsAtLeastOnceUnique (s ←∂→ s₁) (∂→ ind) (hitsAtLeastOnce←∂→∂→ a) (hitsAtLeastOnce←∂→∂→ .a) | refl = refl


  onlyInside¬hitsAtLeastOnce→⊥ : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → onlyInside s ind → ¬ (hitsAtLeastOnce s ind) → ⊥
  onlyInside¬hitsAtLeastOnce→⊥ ↓ ↓ ex ¬ho = ¬ho hitsAtLeastOnce↓
  onlyInside¬hitsAtLeastOnce→⊥ ↓ (ind ←∧) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ ↓ (∧→ ind) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ ↓ (ind ←∨) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ ↓ (∨→ ind) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ ↓ (ind ←∂) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ ↓ (∂→ ind) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∧) ↓ ex ¬ho = ¬ho hitsAtLeastOnce←∧↓
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∧) (ind ←∧) (onlyInsideC←∧←∧ ex) ¬ho with (onlyInside¬hitsAtLeastOnce→⊥ s ind ex (λ x → ¬ho (hitsAtLeastOnce←∧←∧ x)))
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∧) (ind ←∧) (onlyInsideC←∧←∧ ex) ¬ho | ()
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∧) (∧→ ind) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (∧→ s) ↓ ex ¬ho = ¬ho hitsAtLeastOnce∧→↓
  onlyInside¬hitsAtLeastOnce→⊥ (∧→ s) (ind ←∧) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (∧→ s) (∧→ ind) (onlyInsideC∧→∧→ ex) ¬ho with (onlyInside¬hitsAtLeastOnce→⊥ s ind ex (λ x → ¬ho (hitsAtLeastOnce∧→∧→ x)))
  onlyInside¬hitsAtLeastOnce→⊥ (∧→ s) (∧→ ind) (onlyInsideC∧→∧→ ex) ¬ho | ()
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∧→ s₁) ↓ ex ¬ho = ¬ho hitsAtLeastOnce←∧→↓
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∧→ s₁) (ind ←∧) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∧→ s₁) (∧→ ind) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∨) ↓ ex ¬ho = ¬ho hitsAtLeastOnce←∨↓
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∨) (ind ←∨) (onlyInsideC←∨←∨ ex) ¬ho with (onlyInside¬hitsAtLeastOnce→⊥ s ind ex (λ x → ¬ho (hitsAtLeastOnce←∨←∨ x)))
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∨) (ind ←∨) (onlyInsideC←∨←∨ ex) ¬ho | ()
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∨) (∨→ ind) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (∨→ s) ↓ ex ¬ho = ¬ho hitsAtLeastOnce∨→↓
  onlyInside¬hitsAtLeastOnce→⊥ (∨→ s) (ind ←∨) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (∨→ s) (∨→ ind) (onlyInsideC∨→∨→ ex) ¬ho with (onlyInside¬hitsAtLeastOnce→⊥ s ind ex (λ x → ¬ho (hitsAtLeastOnce∨→∨→ x)))
  onlyInside¬hitsAtLeastOnce→⊥ (∨→ s) (∨→ ind) (onlyInsideC∨→∨→ ex) ¬ho | ()
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∨→ s₁) ↓ ex ¬ho = ¬ho hitsAtLeastOnce←∨→↓
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∨→ s₁) (ind ←∨) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∨→ s₁) (∨→ ind) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∂) ↓ ex ¬ho = ¬ho hitsAtLeastOnce←∂↓
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∂) (ind ←∂) (onlyInsideC←∂←∂ ex) ¬ho with (onlyInside¬hitsAtLeastOnce→⊥ s ind ex (λ x → ¬ho (hitsAtLeastOnce←∂←∂ x)))
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∂) (ind ←∂) (onlyInsideC←∂←∂ ex) ¬ho | ()
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∂) (∂→ ind) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (∂→ s) ↓ ex ¬ho = ¬ho hitsAtLeastOnce∂→↓
  onlyInside¬hitsAtLeastOnce→⊥ (∂→ s) (ind ←∂) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (∂→ s) (∂→ ind) (onlyInsideC∂→∂→ ex) ¬ho with (onlyInside¬hitsAtLeastOnce→⊥ s ind ex (λ x → ¬ho (hitsAtLeastOnce∂→∂→ x)))
  onlyInside¬hitsAtLeastOnce→⊥ (∂→ s) (∂→ ind) (onlyInsideC∂→∂→ ex) ¬ho | ()
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∂→ s₁) ↓ ex ¬ho = ¬ho hitsAtLeastOnce←∂→↓
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∂→ s₁) (ind ←∂) () ¬ho
  onlyInside¬hitsAtLeastOnce→⊥ (s ←∂→ s₁) (∂→ ind) () ¬ho






  doesItHitAtLeastOnce : ∀{i u ll q} → (s : SetLL ll) → (ind : IndexLL {i} {u} q ll) → Dec (hitsAtLeastOnce s ind)
  doesItHitAtLeastOnce ↓ ind = yes hitsAtLeastOnce↓
  doesItHitAtLeastOnce (s ←∧) ↓ = yes hitsAtLeastOnce←∧↓
  doesItHitAtLeastOnce (s ←∧) (ind ←∧) with (doesItHitAtLeastOnce s ind)
  doesItHitAtLeastOnce (s ←∧) (ind ←∧) | yes p = yes (hitsAtLeastOnce←∧←∧ p)
  doesItHitAtLeastOnce (s ←∧) (ind ←∧) | no ¬p = no (λ {(hitsAtLeastOnce←∧←∧ x) → ¬p x})
  doesItHitAtLeastOnce (s ←∧) (∧→ ind) = no (λ ())
  doesItHitAtLeastOnce (∧→ s) ↓ = yes hitsAtLeastOnce∧→↓
  doesItHitAtLeastOnce (∧→ s) (ind ←∧) = no (λ ())
  doesItHitAtLeastOnce (∧→ s) (∧→ ind) with (doesItHitAtLeastOnce s ind)
  doesItHitAtLeastOnce (∧→ s) (∧→ ind) | yes p = yes (hitsAtLeastOnce∧→∧→ p)
  doesItHitAtLeastOnce (∧→ s) (∧→ ind) | no ¬p = no (λ {(hitsAtLeastOnce∧→∧→ x) → ¬p x})
  doesItHitAtLeastOnce (s ←∧→ s₁) ↓ = yes hitsAtLeastOnce←∧→↓
  doesItHitAtLeastOnce (s ←∧→ s₁) (ind ←∧) with (doesItHitAtLeastOnce s ind)
  doesItHitAtLeastOnce (s ←∧→ s₁) (ind ←∧) | yes p = yes (hitsAtLeastOnce←∧→←∧ p)
  doesItHitAtLeastOnce (s ←∧→ s₁) (ind ←∧) | no ¬p = no (λ {(hitsAtLeastOnce←∧→←∧ x) → ¬p x})
  doesItHitAtLeastOnce (s ←∧→ s₁) (∧→ ind) with (doesItHitAtLeastOnce s₁ ind)
  doesItHitAtLeastOnce (s ←∧→ s₁) (∧→ ind) | yes p = yes (hitsAtLeastOnce←∧→∧→ p) 
  doesItHitAtLeastOnce (s ←∧→ s₁) (∧→ ind) | no ¬p = no (λ {(hitsAtLeastOnce←∧→∧→ x) → ¬p x})
  doesItHitAtLeastOnce (s ←∨) ↓ = yes hitsAtLeastOnce←∨↓
  doesItHitAtLeastOnce (s ←∨) (ind ←∨) with (doesItHitAtLeastOnce s ind)
  doesItHitAtLeastOnce (s ←∨) (ind ←∨) | yes p = yes (hitsAtLeastOnce←∨←∨ p) 
  doesItHitAtLeastOnce (s ←∨) (ind ←∨) | no ¬p = no (λ {(hitsAtLeastOnce←∨←∨ x) → ¬p x})
  doesItHitAtLeastOnce (s ←∨) (∨→ ind) = no (λ ())
  doesItHitAtLeastOnce (∨→ s) ↓ = yes hitsAtLeastOnce∨→↓
  doesItHitAtLeastOnce (∨→ s) (ind ←∨) = no (λ ())
  doesItHitAtLeastOnce (∨→ s) (∨→ ind) with (doesItHitAtLeastOnce s ind)
  doesItHitAtLeastOnce (∨→ s) (∨→ ind) | yes p = yes (hitsAtLeastOnce∨→∨→ p) 
  doesItHitAtLeastOnce (∨→ s) (∨→ ind) | no ¬p = no (λ {(hitsAtLeastOnce∨→∨→ x) → ¬p x})
  doesItHitAtLeastOnce (s ←∨→ s₁) ↓ = yes hitsAtLeastOnce←∨→↓
  doesItHitAtLeastOnce (s ←∨→ s₁) (ind ←∨) with (doesItHitAtLeastOnce s ind)
  doesItHitAtLeastOnce (s ←∨→ s₁) (ind ←∨) | yes p = yes (hitsAtLeastOnce←∨→←∨ p) 
  doesItHitAtLeastOnce (s ←∨→ s₁) (ind ←∨) | no ¬p = no (λ {(hitsAtLeastOnce←∨→←∨ x) → ¬p x})
  doesItHitAtLeastOnce (s ←∨→ s₁) (∨→ ind) with (doesItHitAtLeastOnce s₁ ind)
  doesItHitAtLeastOnce (s ←∨→ s₁) (∨→ ind) | yes p = yes (hitsAtLeastOnce←∨→∨→ p)
  doesItHitAtLeastOnce (s ←∨→ s₁) (∨→ ind) | no ¬p = no (λ {(hitsAtLeastOnce←∨→∨→ x) → ¬p x})
  doesItHitAtLeastOnce (s ←∂) ↓ = yes hitsAtLeastOnce←∂↓
  doesItHitAtLeastOnce (s ←∂) (ind ←∂) with (doesItHitAtLeastOnce s ind)
  doesItHitAtLeastOnce (s ←∂) (ind ←∂) | yes p = yes (hitsAtLeastOnce←∂←∂ p) 
  doesItHitAtLeastOnce (s ←∂) (ind ←∂) | no ¬p = no (λ {(hitsAtLeastOnce←∂←∂ x) → ¬p x})
  doesItHitAtLeastOnce (s ←∂) (∂→ ind) = no (λ ())
  doesItHitAtLeastOnce (∂→ s) ↓ = yes hitsAtLeastOnce∂→↓
  doesItHitAtLeastOnce (∂→ s) (ind ←∂) = no (λ ())
  doesItHitAtLeastOnce (∂→ s) (∂→ ind) with (doesItHitAtLeastOnce s ind)
  doesItHitAtLeastOnce (∂→ s) (∂→ ind) | yes p = yes (hitsAtLeastOnce∂→∂→ p) 
  doesItHitAtLeastOnce (∂→ s) (∂→ ind) | no ¬p = no (λ {(hitsAtLeastOnce∂→∂→ x) → ¬p x})
  doesItHitAtLeastOnce (s ←∂→ s₁) ↓ = yes hitsAtLeastOnce←∂→↓
  doesItHitAtLeastOnce (s ←∂→ s₁) (ind ←∂) with (doesItHitAtLeastOnce s ind)
  doesItHitAtLeastOnce (s ←∂→ s₁) (ind ←∂) | yes p = yes (hitsAtLeastOnce←∂→←∂ p)
  doesItHitAtLeastOnce (s ←∂→ s₁) (ind ←∂) | no ¬p = no (λ {(hitsAtLeastOnce←∂→←∂ x) → ¬p x})
  doesItHitAtLeastOnce (s ←∂→ s₁) (∂→ ind) with (doesItHitAtLeastOnce s₁ ind)
  doesItHitAtLeastOnce (s ←∂→ s₁) (∂→ ind) | yes p = yes (hitsAtLeastOnce←∂→∂→ p)
  doesItHitAtLeastOnce (s ←∂→ s₁) (∂→ ind) | no ¬p = no (λ {(hitsAtLeastOnce←∂→∂→ x) → ¬p x})


module _ where


-- Replace the linear logic sub-tree.
  replSetLL : ∀{i u ll q} → (s : SetLL ll) → (ind : IndexLL {i} {u} q ll)
              → .{{ prf : ¬ (hitsAtLeastOnce s ind) }} → (rll : LinLogic i)
              → (SetLL (replLL ll ind rll))
  replSetLL ↓ ↓ {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce↓)
  replSetLL ↓ (ind ←∧) {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce↓)
  replSetLL ↓ (∧→ ind) {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce↓)
  replSetLL ↓ (ind ←∨) {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce↓)
  replSetLL ↓ (∨→ ind) {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce↓)
  replSetLL ↓ (ind ←∂) {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce↓)
  replSetLL ↓ (∂→ ind) {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce↓)
  replSetLL (s ←∧) ↓ {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce←∧↓)
  replSetLL (s ←∧) (ind ←∧) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsAtLeastOnce←∧←∧ x)}} rll) ←∧
  replSetLL (s ←∧) (∧→ ind) {{prf}} rll = s ←∧
  replSetLL (∧→ s) ↓ {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce∧→↓)
  replSetLL (∧→ s) (ind ←∧) {{prf}} rll = ∧→ s
  replSetLL (∧→ s) (∧→ ind) {{prf}} rll = ∧→ (replSetLL s ind {{prf = λ x → prf (hitsAtLeastOnce∧→∧→ x)}} rll)
  replSetLL (s ←∧→ s₁) ↓ {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce←∧→↓)
  replSetLL (s ←∧→ s₁) (ind ←∧) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsAtLeastOnce←∧→←∧ x)}} rll) ←∧
  replSetLL (s ←∧→ s₁) (∧→ ind) {{prf}} rll = ∧→ (replSetLL s₁ ind {{prf = λ x → prf (hitsAtLeastOnce←∧→∧→ x)}} rll)
  replSetLL (s ←∨) ↓ {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce←∨↓)
  replSetLL (s ←∨) (ind ←∨) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsAtLeastOnce←∨←∨ x)}} rll) ←∨
  replSetLL (s ←∨) (∨→ ind) {{prf}} rll = s ←∨
  replSetLL (∨→ s) ↓ {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce∨→↓)
  replSetLL (∨→ s) (ind ←∨) {{prf}} rll = ∨→ s
  replSetLL (∨→ s) (∨→ ind) {{prf}} rll = ∨→ (replSetLL s ind {{prf = λ x → prf (hitsAtLeastOnce∨→∨→ x)}} rll)
  replSetLL (s ←∨→ s₁) ↓ {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce←∨→↓)
  replSetLL (s ←∨→ s₁) (ind ←∨) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsAtLeastOnce←∨→←∨ x)}} rll) ←∨
  replSetLL (s ←∨→ s₁) (∨→ ind) {{prf}} rll = ∨→ (replSetLL s₁ ind {{prf = λ x → prf (hitsAtLeastOnce←∨→∨→ x)}} rll)
  replSetLL (s ←∂) ↓ {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce←∂↓)
  replSetLL (s ←∂) (ind ←∂) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsAtLeastOnce←∂←∂ x)}} rll) ←∂
  replSetLL (s ←∂) (∂→ ind) {{prf}} rll = s ←∂
  replSetLL (∂→ s) ↓ {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce∂→↓)
  replSetLL (∂→ s) (ind ←∂) {{prf}} rll = ∂→ s
  replSetLL (∂→ s) (∂→ ind) {{prf}} rll = ∂→ (replSetLL s ind {{prf = λ x → prf (hitsAtLeastOnce∂→∂→ x)}} rll)
  replSetLL (s ←∂→ s₁) ↓ {{prf}} rll = ⊥-elim (prf hitsAtLeastOnce←∂→↓)
  replSetLL (s ←∂→ s₁) (ind ←∂) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsAtLeastOnce←∂→←∂ x)}} rll) ←∂
  replSetLL (s ←∂→ s₁) (∂→ ind) {{prf}} rll = ∂→ (replSetLL s₁ ind {{prf = λ x → prf (hitsAtLeastOnce←∂→∂→ x)}} rll)


  truncOISetLL : ∀ {i u ll pll} → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
               → ⦃ prf : onlyInside s ind ⦄ → SetLL pll
  truncOISetLL s ↓ {{prf}} = s
  truncOISetLL ↓ (ind ←∧) {{()}}
  truncOISetLL (s ←∧) (ind ←∧) {{onlyInsideC←∧←∧ prf}} = truncOISetLL s ind {{prf}}
  truncOISetLL (∧→ s) (ind ←∧) {{()}}
  truncOISetLL (s ←∧→ s₁) (ind ←∧) {{()}}
  truncOISetLL ↓ (∧→ ind) {{()}}
  truncOISetLL (s ←∧) (∧→ ind) {{()}}
  truncOISetLL (∧→ s) (∧→ ind) {{onlyInsideC∧→∧→ prf}} = truncOISetLL s ind {{prf}}
  truncOISetLL (s ←∧→ s₁) (∧→ ind) {{()}}
  truncOISetLL ↓ (ind ←∨) {{()}}
  truncOISetLL (s ←∨) (ind ←∨) {{onlyInsideC←∨←∨ prf}} = truncOISetLL s ind {{prf}}
  truncOISetLL (∨→ s) (ind ←∨) {{()}}
  truncOISetLL (s ←∨→ s₁) (ind ←∨) {{()}}
  truncOISetLL ↓ (∨→ ind) {{()}}
  truncOISetLL (s ←∨) (∨→ ind) {{()}}
  truncOISetLL (∨→ s) (∨→ ind) {{onlyInsideC∨→∨→ prf}} = truncOISetLL s ind {{prf}}
  truncOISetLL (s ←∨→ s₁) (∨→ ind) {{()}}
  truncOISetLL ↓ (ind ←∂) {{()}}
  truncOISetLL (s ←∂) (ind ←∂) {{onlyInsideC←∂←∂ prf}} = truncOISetLL s ind {{prf}}
  truncOISetLL (∂→ s) (ind ←∂) {{()}}
  truncOISetLL (s ←∂→ s₁) (ind ←∂) {{()}}
  truncOISetLL ↓ (∂→ ind) {{()}}
  truncOISetLL (s ←∂) (∂→ ind) {{()}}
  truncOISetLL (∂→ s) (∂→ ind) {{onlyInsideC∂→∂→ prf}} = truncOISetLL s ind {{prf}}
  truncOISetLL (s ←∂→ s₁) (∂→ ind) {{()}}


≤s-extr : ∀{i u ll pll}→ (ind : IndexLL {i} {u} pll ll) → (s : SetLL ll) → ⦃ prf : onlyInside s ind ⦄ → (extend ind (truncOISetLL s ind) ≤s s)
≤s-extr ↓ s = ≤id
≤s-extr (ind ←∧) ↓ {{()}}
≤s-extr (ind ←∧) (s ←∧) {{onlyInsideC←∧←∧ prf}} = ≤←∧ (≤s-extr ind s {{prf}})
≤s-extr (ind ←∧) (∧→ s) {{()}}
≤s-extr (ind ←∧) (s ←∧→ s₁) {{()}}
≤s-extr (∧→ ind) ↓ {{()}}
≤s-extr (∧→ ind) (s ←∧) {{()}}
≤s-extr (∧→ ind) (∧→ s) {{onlyInsideC∧→∧→ prf}} = ≤∧→ (≤s-extr ind s {{prf}})
≤s-extr (∧→ ind) (s ←∧→ s₁) {{()}}
≤s-extr (ind ←∨) ↓ {{()}}
≤s-extr (ind ←∨) (s ←∨) {{onlyInsideC←∨←∨ prf}} = ≤←∨ (≤s-extr ind s {{prf}})
≤s-extr (ind ←∨) (∨→ s) {{()}}
≤s-extr (ind ←∨) (s ←∨→ s₁) {{()}}
≤s-extr (∨→ ind) ↓ {{()}}
≤s-extr (∨→ ind) (s ←∨) {{()}}
≤s-extr (∨→ ind) (∨→ s) {{onlyInsideC∨→∨→ prf}} = ≤∨→ (≤s-extr ind s {{prf}})
≤s-extr (∨→ ind) (s ←∨→ s₁) {{()}}
≤s-extr (ind ←∂) ↓ {{()}}
≤s-extr (ind ←∂) (s ←∂) {{onlyInsideC←∂←∂ prf}} = ≤←∂ (≤s-extr ind s {{prf}})
≤s-extr (ind ←∂) (∂→ s) {{()}}
≤s-extr (ind ←∂) (s ←∂→ s₁) {{()}}
≤s-extr (∂→ ind) ↓ {{()}}
≤s-extr (∂→ ind) (s ←∂) {{()}}
≤s-extr (∂→ ind) (∂→ s) {{onlyInsideC∂→∂→ prf}} = ≤∂→ (≤s-extr ind s {{prf}})
≤s-extr (∂→ ind) (s ←∂→ s₁) {{()}}

oi⇒ext-truncoi : ∀{i u pll ll ss s} → (ind : IndexLL {i} {u} pll ll) → {{oi : onlyInside s ind}} → ss ≤s (truncOISetLL s ind {{prf = oi}}) → onlyInside (extend ind ss) ind
oi⇒ext-truncoi {s = _} ↓ {{oi}} x = onlyInsideCs↓
oi⇒ext-truncoi {s = ↓} (ind ←∧) {{()}} x
oi⇒ext-truncoi {s = _ ←∧} (ind ←∧) {{onlyInsideC←∧←∧ oi}} x = onlyInsideC←∧←∧ (oi⇒ext-truncoi ind {{oi = oi}} x)
oi⇒ext-truncoi {s = ∧→ _} (ind ←∧) {{()}} x
oi⇒ext-truncoi {s = _ ←∧→ _} (ind ←∧) {{()}} x
oi⇒ext-truncoi {s = .(∧→ _)} (∧→ ind) {{onlyInsideC∧→∧→ oi}} x = onlyInsideC∧→∧→ (oi⇒ext-truncoi ind {{oi = oi}} x)
oi⇒ext-truncoi {s = ↓} (ind ←∨) {{()}} x
oi⇒ext-truncoi {s = _ ←∨} (ind ←∨) {{onlyInsideC←∨←∨ oi}} x = onlyInsideC←∨←∨ (oi⇒ext-truncoi ind {{oi = oi}} x)
oi⇒ext-truncoi {s = ∨→ _} (ind ←∨) {{()}} x
oi⇒ext-truncoi {s = _ ←∨→ _} (ind ←∨) {{()}} x
oi⇒ext-truncoi {s = .(∨→ _)} (∨→ ind) {{onlyInsideC∨→∨→ oi}} x = onlyInsideC∨→∨→ (oi⇒ext-truncoi ind {{oi = oi}} x)
oi⇒ext-truncoi {s = ↓} (ind ←∂) {{()}} x
oi⇒ext-truncoi {s = _ ←∂} (ind ←∂) {{onlyInsideC←∂←∂ oi}} x = onlyInsideC←∂←∂ (oi⇒ext-truncoi ind {{oi = oi}} x)
oi⇒ext-truncoi {s = ∂→ _} (ind ←∂) {{()}} x
oi⇒ext-truncoi {s = _ ←∂→ _} (ind ←∂) {{()}} x
oi⇒ext-truncoi {s = .(∂→ _)} (∂→ ind) {{onlyInsideC∂→∂→ oi}} x = onlyInsideC∂→∂→ (oi⇒ext-truncoi ind {{oi = oi}} x)


tr-ext⇒id : ∀{i u pll ll s} → (ind : IndexLL {i} {u} pll ll) → {{oi : onlyInside (extend ind s) ind}} →  truncOISetLL (extend ind s) ind ≡ s
tr-ext⇒id ↓ {{onlyInsideCs↓}} = refl
tr-ext⇒id (ind ←∧) {{onlyInsideC←∧←∧ oi}} = tr-ext⇒id ind
tr-ext⇒id (∧→ ind) {{onlyInsideC∧→∧→ oi}} = tr-ext⇒id ind
tr-ext⇒id (ind ←∨) {{onlyInsideC←∨←∨ oi}} = tr-ext⇒id ind
tr-ext⇒id (∨→ ind) {{onlyInsideC∨→∨→ oi}} = tr-ext⇒id ind
tr-ext⇒id (ind ←∂) {{onlyInsideC←∂←∂ oi}} = tr-ext⇒id ind
tr-ext⇒id (∂→ ind) {{onlyInsideC∂→∂→ oi}} = tr-ext⇒id ind

≤⇒tr≤ : ∀{i u pll ll ss s} → (ind : IndexLL {i} {u} pll ll) → ss ≤s s → {{ loi : onlyInside ss ind}} → {{oi : onlyInside s ind}} → truncOISetLL ss ind ≤s truncOISetLL s ind
≤⇒tr≤ ↓ x = x
≤⇒tr≤ (ind ←∧) ≤id {{onlyInsideC←∧←∧ loi}} {{onlyInsideC←∧←∧ oi}} = ≤⇒tr≤ ind ≤id
≤⇒tr≤ (ind ←∧) (≤←∧ x) {{onlyInsideC←∧←∧ loi}} {{onlyInsideC←∧←∧ oi}} = ≤⇒tr≤ ind x
≤⇒tr≤ (∧→ ind) ≤id {{onlyInsideC∧→∧→ loi}} {{onlyInsideC∧→∧→ oi}} = ≤⇒tr≤ ind ≤id
≤⇒tr≤ (∧→ ind) (≤←∧ x) {{loi}} {{()}}
≤⇒tr≤ (∧→ ind) (≤∧→ x) {{onlyInsideC∧→∧→ loi}} {{onlyInsideC∧→∧→ oi}} = ≤⇒tr≤ ind x
≤⇒tr≤ (∧→ ind) (≤←∧→ x x₁) {{loi}} {{()}}
≤⇒tr≤ (∧→ ind) (≤d←∧ x) {{loi}} {{()}}
≤⇒tr≤ (∧→ ind) (≤d∧→ x) {{loi}} {{()}}
≤⇒tr≤ (ind ←∨) ≤id {{onlyInsideC←∨←∨ loi}} {{onlyInsideC←∨←∨ oi}} = ≤⇒tr≤ ind ≤id
≤⇒tr≤ (ind ←∨) (≤←∨ x) {{onlyInsideC←∨←∨ loi}} {{onlyInsideC←∨←∨ oi}} = ≤⇒tr≤ ind x
≤⇒tr≤ (∨→ ind) ≤id {{onlyInsideC∨→∨→ loi}} {{onlyInsideC∨→∨→ oi}} = ≤⇒tr≤ ind ≤id
≤⇒tr≤ (∨→ ind) (≤←∨ x) {{loi}} {{()}}
≤⇒tr≤ (∨→ ind) (≤∨→ x) {{onlyInsideC∨→∨→ loi}} {{onlyInsideC∨→∨→ oi}} = ≤⇒tr≤ ind x
≤⇒tr≤ (∨→ ind) (≤←∨→ x x₁) {{loi}} {{()}}
≤⇒tr≤ (∨→ ind) (≤d←∨ x) {{loi}} {{()}}
≤⇒tr≤ (∨→ ind) (≤d∨→ x) {{loi}} {{()}}
≤⇒tr≤ (ind ←∂) ≤id {{onlyInsideC←∂←∂ loi}} {{onlyInsideC←∂←∂ oi}} = ≤⇒tr≤ ind ≤id
≤⇒tr≤ (ind ←∂) (≤←∂ x) {{onlyInsideC←∂←∂ loi}} {{onlyInsideC←∂←∂ oi}} = ≤⇒tr≤ ind x
≤⇒tr≤ (∂→ ind) ≤id {{onlyInsideC∂→∂→ loi}} {{onlyInsideC∂→∂→ oi}} = ≤⇒tr≤ ind ≤id
≤⇒tr≤ (∂→ ind) (≤←∂ x) {{loi}} {{()}}
≤⇒tr≤ (∂→ ind) (≤∂→ x) {{onlyInsideC∂→∂→ loi}} {{onlyInsideC∂→∂→ oi}} = ≤⇒tr≤ ind x
≤⇒tr≤ (∂→ ind) (≤←∂→ x x₁) {{loi}} {{()}}
≤⇒tr≤ (∂→ ind) (≤d←∂ x) {{loi}} {{()}}
≤⇒tr≤ (∂→ ind) (≤d∂→ x) {{loi}} {{()}}
