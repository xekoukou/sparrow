-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS --show-irrelevant #-}

module LinFunContruct where

open import Common
open import LinLogic
import IndexLLProp
open import SetLL
open import SetLLProp

open import Relation.Binary.PropositionalEquality
open import Data.Product

module _ where

  open IndexLLProp hiding (tran)
  open import Data.Sum

  shrink : ∀{i u} → ∀ ll → (cms : SetLL {i} {u} ll) → LinLogic i {u}
  shrink ∅ cms = ∅
  shrink (τ x) cms = τ x
  shrink (ll ∧ rl) ↓ = ll ∧ rl
  shrink (ll ∧ rl) (cms ←∧) = shrink ll cms
  shrink (ll ∧ rl) (∧→ cms) = shrink rl cms
  shrink (ll ∧ rl) (cms ←∧→ cms₁) = shrink ll cms ∧ shrink rl cms₁
  shrink (ll ∨ rl) ↓ = ll ∨ rl
  shrink (ll ∨ rl) (cms ←∨) = shrink ll cms
  shrink (ll ∨ rl) (∨→ cms) = shrink rl cms
  shrink (ll ∨ rl) (cms ←∨→ cms₁) = shrink ll cms ∨ shrink rl cms₁
  shrink (ll ∂ rl) ↓ = ll ∂ rl
  shrink (ll ∂ rl) (cms ←∂) = shrink ll cms
  shrink (ll ∂ rl) (∂→ cms) = shrink rl cms
  shrink (ll ∂ rl) (cms ←∂→ cms₁) = shrink ll cms ∂ shrink rl cms₁
  shrink (call x) cms = call x
  
  
  shrinkcms : ∀{i u} → ∀ ll → (s cms : SetLL {i} {u} ll) → complLₛ s ≡ ¬∅ cms → LinLogic i {u}
  shrinkcms ll s cms ceq = shrink ll cms
  
  
  mshrink : ∀{i u} → ∀ ll → MSetLL {i} {u} ll → LinLogic i {u}
  mshrink ll ∅ = ll
  mshrink ll (¬∅ x) = shrink ll x
  
  
  
  shr-↓-id : ∀{i u} → ∀ ll → shrink {i} {u} ll ↓ ≡ ll
  shr-↓-id ∅ = refl
  shr-↓-id (τ x) = refl
  shr-↓-id (ll ∧ ll₁) = refl
  shr-↓-id (ll ∨ ll₁) = refl
  shr-↓-id (ll ∂ ll₁) = refl
  shr-↓-id (call x) = refl
  
  
  
  shr-fAL-id : ∀{i u} → ∀ ll → ll ≡ shrink {i} {u} ll (fillAllLower ll)
  shr-fAL-id ∅ = refl
  shr-fAL-id (τ x) = refl
  shr-fAL-id (ll ∧ lr) = cong₂ (λ x y → x ∧ y) (shr-fAL-id ll) (shr-fAL-id lr)
  shr-fAL-id (ll ∨ lr) = cong₂ (λ x y → x ∨ y) (shr-fAL-id ll) (shr-fAL-id lr)
  shr-fAL-id (ll ∂ lr) = cong₂ (λ x y → x ∂ y) (shr-fAL-id ll) (shr-fAL-id lr)
  shr-fAL-id (call x) = refl
  
  
  -- This is a generalization of ¬ord-morph
  -- TODO Maybe with some small changes, we can reduce the size of the code in this function.
  
  ¬ho-shr-morph : ∀{i u rll ll cs} → (s : SetLL {i} {u} ll) → (ceq : complLₛ s ≡ ¬∅ cs)
                  → (ind : IndexLL rll ll) → (¬ho : ¬ (hitsAtLeastOnce s ind))
                  → IndexLL rll (shrinkcms ll s cs ceq)
  ¬ho-shr-morph {cs = cs} ↓ () ind ¬ho
  ¬ho-shr-morph {cs = cs} (s ←∧) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce←∧↓)
  ¬ho-shr-morph {cs = cs} (s ←∧) ceq (ind ←∧) ¬ho with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph {cs = cs} (s ←∧) ceq (ind ←∧) ¬ho | ∅ | [ eq ]
                                          =  ⊥-elim (¬nho (compl≡∅⇒ho s eq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∧←∧ x)
  ¬ho-shr-morph {cs = cs} (s ←∧) refl (ind ←∧) ¬ho | ¬∅ x | [ eq ] = r ←∧ where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∧←∧ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {rll = rll} {_ ∧ rs} {cs = cs} (s ←∧) ceq (∧→ ind) ¬ho with complLₛ s
  ¬ho-shr-morph {rll = rll} {_ ∧ rs} (s ←∧) refl (∧→ ind) ¬ho | ∅
                           = subst (λ x → IndexLL rll x) (shr-fAL-id rs) ind
  ¬ho-shr-morph {rll = rll} {_ ∧ rs} {.(x₁ ←∧→ fillAllLower rs)} (s ←∧) refl (∧→ ind) ¬ho | ¬∅ x₁
       = ∧→ (subst (λ x → IndexLL rll x) (shr-fAL-id rs) ind)
  ¬ho-shr-morph {cs = cs} (∧→ s) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce∧→↓)
  ¬ho-shr-morph {rll = rll} {ls ∧ _} {cs = cs} (∧→ s) ceq (ind ←∧) ¬ho with complLₛ s
  ¬ho-shr-morph {rll = rll} {ls ∧ _} {.(fillAllLower ls ←∧)} (∧→ s) refl (ind ←∧) ¬ho | ∅
                           = subst (λ x → IndexLL rll x) (shr-fAL-id ls) ind
  ¬ho-shr-morph {rll = rll} {ls ∧ _} {.(fillAllLower ls ←∧→ x₁)} (∧→ s) refl (ind ←∧) ¬ho | ¬∅ x₁
                           = (subst (λ x → IndexLL rll x) (shr-fAL-id ls) ind) ←∧
  ¬ho-shr-morph {cs = cs} (∧→ s) ceq (∧→ ind) ¬ho with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph {cs = cs} (∧→ s) ceq (∧→ ind) ¬ho | ∅ | [ eq ]
                                               = ⊥-elim (¬nho (compl≡∅⇒ho s eq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce∧→∧→ x)
  ¬ho-shr-morph {cs = cs} (∧→ s) refl (∧→ ind) ¬ho | ¬∅ x | [ eq ] = ∧→ r where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce∧→∧→ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce←∧→↓)
  ¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (ind ←∧) ¬ho with complLₛ s | inspect complLₛ s | complLₛ s₁
  ¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (ind ←∧) ¬ho | ∅ | [ eq ] | e
               =  ⊥-elim (¬nho (compl≡∅⇒ho s eq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  ¬ho-shr-morph {cs = cs} (s ←∧→ s₁) refl (ind ←∧) ¬ho | ¬∅ x | [ eq ] | ∅ = r where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∧→←∧ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∧→ s₁) refl (ind ←∧) ¬ho | ¬∅ x | [ eq ] | ¬∅ x₁ = r ←∧ where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∧→←∧ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (∧→ ind) ¬ho with complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  ¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (∧→ ind) ¬ho | r | ∅ | [ eq ]  
               =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ eq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  ¬ho-shr-morph {cs = cs} (s ←∧→ s₁) refl (∧→ ind) ¬ho | ∅ | ¬∅ x | [ eq ] = r where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ x)
    r = ¬ho-shr-morph s₁ eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∧→ s₁) refl (∧→ ind) ¬ho | ¬∅ x | ¬∅ x₁ | [ eq ] = ∧→ r where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ x)
    r = ¬ho-shr-morph s₁ eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∨) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce←∨↓)
  ¬ho-shr-morph {cs = cs} (s ←∨) ceq (ind ←∨) ¬ho with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph {cs = cs} (s ←∨) ceq (ind ←∨) ¬ho | ∅ | [ eq ]
                                          =  ⊥-elim (¬nho (compl≡∅⇒ho s eq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∨←∨ x)
  ¬ho-shr-morph {cs = cs} (s ←∨) refl (ind ←∨) ¬ho | ¬∅ x | [ eq ] = r ←∨ where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∨←∨ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {rll = rll} {_ ∨ rs} {cs = cs} (s ←∨) ceq (∨→ ind) ¬ho with complLₛ s
  ¬ho-shr-morph {rll = rll} {_ ∨ rs} (s ←∨) refl (∨→ ind) ¬ho | ∅
                           = subst (λ x → IndexLL rll x) (shr-fAL-id rs) ind
  ¬ho-shr-morph {rll = rll} {_ ∨ rs} {.(x₁ ←∨→ fillAllLower rs)} (s ←∨) refl (∨→ ind) ¬ho | ¬∅ x₁
       = ∨→ (subst (λ x → IndexLL rll x) (shr-fAL-id rs) ind)
  ¬ho-shr-morph {cs = cs} (∨→ s) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce∨→↓)
  ¬ho-shr-morph {rll = rll} {ls ∨ _} {cs = cs} (∨→ s) ceq (ind ←∨) ¬ho with complLₛ s
  ¬ho-shr-morph {rll = rll} {ls ∨ _} {.(fillAllLower ls ←∨)} (∨→ s) refl (ind ←∨) ¬ho | ∅
                           = subst (λ x → IndexLL rll x) (shr-fAL-id ls) ind
  ¬ho-shr-morph {rll = rll} {ls ∨ _} {.(fillAllLower ls ←∨→ x₁)} (∨→ s) refl (ind ←∨) ¬ho | ¬∅ x₁
                           = (subst (λ x → IndexLL rll x) (shr-fAL-id ls) ind) ←∨
  ¬ho-shr-morph {cs = cs} (∨→ s) ceq (∨→ ind) ¬ho with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph {cs = cs} (∨→ s) ceq (∨→ ind) ¬ho | ∅ | [ eq ]
                                               = ⊥-elim (¬nho (compl≡∅⇒ho s eq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce∨→∨→ x)
  ¬ho-shr-morph {cs = cs} (∨→ s) refl (∨→ ind) ¬ho | ¬∅ x | [ eq ] = ∨→ r where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce∨→∨→ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce←∨→↓)
  ¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (ind ←∨) ¬ho with complLₛ s | inspect complLₛ s | complLₛ s₁
  ¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (ind ←∨) ¬ho | ∅ | [ eq ] | e
               =  ⊥-elim (¬nho (compl≡∅⇒ho s eq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  ¬ho-shr-morph {cs = cs} (s ←∨→ s₁) refl (ind ←∨) ¬ho | ¬∅ x | [ eq ] | ∅ = r where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∨→←∨ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∨→ s₁) refl (ind ←∨) ¬ho | ¬∅ x | [ eq ] | ¬∅ x₁ = r ←∨ where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∨→←∨ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (∨→ ind) ¬ho with complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  ¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (∨→ ind) ¬ho | r | ∅ | [ eq ]  
               =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ eq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  ¬ho-shr-morph {cs = cs} (s ←∨→ s₁) refl (∨→ ind) ¬ho | ∅ | ¬∅ x | [ eq ] = r where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ x)
    r = ¬ho-shr-morph s₁ eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∨→ s₁) refl (∨→ ind) ¬ho | ¬∅ x | ¬∅ x₁ | [ eq ] = ∨→ r where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ x)
    r = ¬ho-shr-morph s₁ eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∂) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce←∂↓)
  ¬ho-shr-morph {cs = cs} (s ←∂) ceq (ind ←∂) ¬ho with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph {cs = cs} (s ←∂) ceq (ind ←∂) ¬ho | ∅ | [ eq ]
                                          =  ⊥-elim (¬nho (compl≡∅⇒ho s eq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∂←∂ x)
  ¬ho-shr-morph {cs = cs} (s ←∂) refl (ind ←∂) ¬ho | ¬∅ x | [ eq ] = r ←∂ where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∂←∂ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {rll = rll} {_ ∂ rs} {cs = cs} (s ←∂) ceq (∂→ ind) ¬ho with complLₛ s
  ¬ho-shr-morph {rll = rll} {_ ∂ rs} (s ←∂) refl (∂→ ind) ¬ho | ∅
                           = subst (λ x → IndexLL rll x) (shr-fAL-id rs) ind
  ¬ho-shr-morph {rll = rll} {_ ∂ rs} {.(x₁ ←∂→ fillAllLower rs)} (s ←∂) refl (∂→ ind) ¬ho | ¬∅ x₁
       = ∂→ (subst (λ x → IndexLL rll x) (shr-fAL-id rs) ind)
  ¬ho-shr-morph {cs = cs} (∂→ s) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce∂→↓)
  ¬ho-shr-morph {rll = rll} {ls ∂ _} {cs = cs} (∂→ s) ceq (ind ←∂) ¬ho with complLₛ s
  ¬ho-shr-morph {rll = rll} {ls ∂ _} {.(fillAllLower ls ←∂)} (∂→ s) refl (ind ←∂) ¬ho | ∅
                           = subst (λ x → IndexLL rll x) (shr-fAL-id ls) ind
  ¬ho-shr-morph {rll = rll} {ls ∂ _} {.(fillAllLower ls ←∂→ x₁)} (∂→ s) refl (ind ←∂) ¬ho | ¬∅ x₁
                           = (subst (λ x → IndexLL rll x) (shr-fAL-id ls) ind) ←∂
  ¬ho-shr-morph {cs = cs} (∂→ s) ceq (∂→ ind) ¬ho with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph {cs = cs} (∂→ s) ceq (∂→ ind) ¬ho | ∅ | [ eq ]
                                               = ⊥-elim (¬nho (compl≡∅⇒ho s eq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce∂→∂→ x)
  ¬ho-shr-morph {cs = cs} (∂→ s) refl (∂→ ind) ¬ho | ¬∅ x | [ eq ] = ∂→ r where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce∂→∂→ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce←∂→↓)
  ¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (ind ←∂) ¬ho with complLₛ s | inspect complLₛ s | complLₛ s₁
  ¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (ind ←∂) ¬ho | ∅ | [ eq ] | e
               =  ⊥-elim (¬nho (compl≡∅⇒ho s eq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  ¬ho-shr-morph {cs = cs} (s ←∂→ s₁) refl (ind ←∂) ¬ho | ¬∅ x | [ eq ] | ∅ = r where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∂→←∂ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∂→ s₁) refl (ind ←∂) ¬ho | ¬∅ x | [ eq ] | ¬∅ x₁ = r ←∂ where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∂→←∂ x)
    r = ¬ho-shr-morph s eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (∂→ ind) ¬ho with complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  ¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (∂→ ind) ¬ho | r | ∅ | [ eq ]  
               =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ eq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  ¬ho-shr-morph {cs = cs} (s ←∂→ s₁) refl (∂→ ind) ¬ho | ∅ | ¬∅ x | [ eq ] = r where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ x)
    r = ¬ho-shr-morph s₁ eq ind ¬nho
  ¬ho-shr-morph {cs = cs} (s ←∂→ s₁) refl (∂→ ind) ¬ho | ¬∅ x | ¬∅ x₁ | [ eq ] = ∂→ r where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ x)
    r = ¬ho-shr-morph s₁ eq ind ¬nho
  
  ¬ho-shr-morph-pres-¬ord : ∀{ i u ll pll ell cs} → ∀ s → (eq : complLₛ s ≡ ¬∅ cs) → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL ell ll) → ∀ ¬hob ¬hoh
        → let bind = ¬ho-shr-morph s eq ind ¬hob in
          let hind = ¬ho-shr-morph s eq lind ¬hoh in
          Orderedᵢ bind hind → Orderedᵢ ind lind
  ¬ho-shr-morph-pres-¬ord ↓ () ind lind ¬hob ¬hoh ord
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq ↓ lind ¬hob ¬hoh ord = ⊥-elim (¬hob hitsAtLeastOnce←∧↓)
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∧↓)
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce←∧←∧ z)) (λ z → ¬hoh (hitsAtLeastOnce←∧←∧ z)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ←∧ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ←∧ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce←∧←∧ z)) (λ z → ¬hoh (hitsAtLeastOnce←∧←∧ z)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ←∧ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ←∧ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (ind ←∧) (∧→ lind) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (ind ←∧) (∧→ lind) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (∧→ ind) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∧↓) 
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∧←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (∧→ ind) (lind ←∧) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (∧→ ind) (lind ←∧) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (s ←∧) eq (∧→ ind) (∧→ lind) ¬hob ¬hoh ord with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (s ←∧) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh ord | ∅ with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (s ←∧) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (a≤ᵢb x) | ∅ | .rll | refl = a≤ᵢb (≤ᵢ∧→ x)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (s ←∧) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (b≤ᵢa x) | ∅ | .rll | refl = b≤ᵢa (≤ᵢ∧→ x)
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (s ←∧) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh ord | ¬∅ x with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (s ←∧) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∧→ y)) | ¬∅ x | .rll | refl = a≤ᵢb (≤ᵢ∧→ y)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (s ←∧) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∧→ y)) | ¬∅ x | .rll | refl = b≤ᵢa (≤ᵢ∧→ y)
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq ↓ lind ¬hob ¬hoh ord = ⊥-elim (¬hob hitsAtLeastOnce∧→↓)
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (∧→ ind) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce∧→↓)
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (∧→ ind) (∧→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (∧→ ind) (∧→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce∧→∧→ x)
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce∧→∧→ z)) (λ z → ¬hoh (hitsAtLeastOnce∧→∧→ z)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ∧→ x₁)
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ∧→ x₁)
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce∧→∧→ z)) (λ z → ¬hoh (hitsAtLeastOnce∧→∧→ z)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ∧→ x₁)
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ∧→ x₁)
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce∧→∧→ x)
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (∧→ ind) (lind ←∧) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (∧→ ind) (lind ←∧) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (ind ←∧) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce∧→↓) 
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce∧→∧→ x)
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (ind ←∧) (∧→ lind) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (ind ←∧) (∧→ lind) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (∧→ s) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh ord with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (∧→ s) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh ord | ∅ with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (∧→ s) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (a≤ᵢb x) | ∅ | .lll | refl = a≤ᵢb (≤ᵢ←∧ x)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (∧→ s) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (b≤ᵢa x) | ∅ | .lll | refl = b≤ᵢa (≤ᵢ←∧ x)
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (∧→ s) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh ord | ¬∅ x with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (∧→ s) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∧ y)) | ¬∅ x | .lll | refl = a≤ᵢb (≤ᵢ←∧ y)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (∧→ s) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∧ y)) | ¬∅ x | .lll | refl = b≤ᵢa (≤ᵢ←∧ y)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq ↓ lind ¬hob ¬hoh ord = ⊥-elim (¬hob hitsAtLeastOnce←∧→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∧→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s | complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh ord | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧→←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ with ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∧→←∧ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∧→←∧ x₁)) ord
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | a≤ᵢb y = a≤ᵢb (≤ᵢ←∧ y)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | b≤ᵢa y = b≤ᵢa (≤ᵢ←∧ y)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∧→←∧ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∧→←∧ x₁)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ←∧ z)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ←∧ z)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∧→←∧ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∧→←∧ x₁)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ←∧ z)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∧ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ←∧ z)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧→←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∧→∧→ x) 
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (∧→ lind) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (∧→ lind) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∧→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) (∧→ lind) ¬hob ¬hoh ord with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) (∧→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧→∧→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ with ¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∧→∧→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∧→∧→ x₁)) ord
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | a≤ᵢb y = a≤ᵢb (≤ᵢ∧→ y)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | b≤ᵢa y = b≤ᵢa (≤ᵢ∧→ y)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∧→∧→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∧→∧→ x₁)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ∧→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ∧→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∧→∧→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∧→∧→ x₁)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ∧→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∧→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ∧→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh ord with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh ord | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧→∧→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∧→←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (lind ←∧) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (lind ←∧) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq ↓ lind ¬hob ¬hoh ord = ⊥-elim (¬hob hitsAtLeastOnce←∨↓)
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (ind ←∨) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∨↓)
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (ind ←∨) (lind ←∨) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (ind ←∨) (lind ←∨) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce←∨←∨ z)) (λ z → ¬hoh (hitsAtLeastOnce←∨←∨ z)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ←∨ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ←∨ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce←∨←∨ z)) (λ z → ¬hoh (hitsAtLeastOnce←∨←∨ z)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ←∨ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ←∨ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (ind ←∨) (∨→ lind) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (ind ←∨) (∨→ lind) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (∨→ ind) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∨↓) 
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∨←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (∨→ ind) (lind ←∨) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (∨→ ind) (lind ←∨) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (s ←∨) eq (∨→ ind) (∨→ lind) ¬hob ¬hoh ord with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (s ←∨) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh ord | ∅ with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (s ←∨) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (a≤ᵢb x) | ∅ | .rll | refl = a≤ᵢb (≤ᵢ∨→ x)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (s ←∨) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (b≤ᵢa x) | ∅ | .rll | refl = b≤ᵢa (≤ᵢ∨→ x)
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (s ←∨) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh ord | ¬∅ x with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (s ←∨) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∨→ y)) | ¬∅ x | .rll | refl = a≤ᵢb (≤ᵢ∨→ y)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (s ←∨) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∨→ y)) | ¬∅ x | .rll | refl = b≤ᵢa (≤ᵢ∨→ y)
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq ↓ lind ¬hob ¬hoh ord = ⊥-elim (¬hob hitsAtLeastOnce∨→↓)
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (∨→ ind) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce∨→↓)
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (∨→ ind) (∨→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (∨→ ind) (∨→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce∨→∨→ x)
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce∨→∨→ z)) (λ z → ¬hoh (hitsAtLeastOnce∨→∨→ z)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ∨→ x₁)
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ∨→ x₁)
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce∨→∨→ z)) (λ z → ¬hoh (hitsAtLeastOnce∨→∨→ z)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ∨→ x₁)
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ∨→ x₁)
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce∨→∨→ x)
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (∨→ ind) (lind ←∨) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (∨→ ind) (lind ←∨) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (ind ←∨) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce∨→↓) 
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce∨→∨→ x)
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (ind ←∨) (∨→ lind) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (ind ←∨) (∨→ lind) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (∨→ s) eq (ind ←∨) (lind ←∨) ¬hob ¬hoh ord with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (∨→ s) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh ord | ∅ with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (∨→ s) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (a≤ᵢb x) | ∅ | .lll | refl = a≤ᵢb (≤ᵢ←∨ x)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (∨→ s) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (b≤ᵢa x) | ∅ | .lll | refl = b≤ᵢa (≤ᵢ←∨ x)
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (∨→ s) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh ord | ¬∅ x with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (∨→ s) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∨ y)) | ¬∅ x | .lll | refl = a≤ᵢb (≤ᵢ←∨ y)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (∨→ s) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∨ y)) | ¬∅ x | .lll | refl = b≤ᵢa (≤ᵢ←∨ y)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq ↓ lind ¬hob ¬hoh ord = ⊥-elim (¬hob hitsAtLeastOnce←∨→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∨→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) (lind ←∨) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s | complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) (lind ←∨) ¬hob ¬hoh ord | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨→←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ with ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∨→←∨ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∨→←∨ x₁)) ord
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | a≤ᵢb y = a≤ᵢb (≤ᵢ←∨ y)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | b≤ᵢa y = b≤ᵢa (≤ᵢ←∨ y)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∨→←∨ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∨→←∨ x₁)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ←∨ z)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ←∨ z)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∨→←∨ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∨→←∨ x₁)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ←∨ z)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∨ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ←∨ z)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨→←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∨→∨→ x) 
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (∨→ lind) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (∨→ lind) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∨→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) (∨→ lind) ¬hob ¬hoh ord with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) (∨→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨→∨→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ with ¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∨→∨→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∨→∨→ x₁)) ord
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | a≤ᵢb y = a≤ᵢb (≤ᵢ∨→ y)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | b≤ᵢa y = b≤ᵢa (≤ᵢ∨→ y)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∨→∨→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∨→∨→ x₁)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ∨→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ∨→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∨→∨→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∨→∨→ x₁)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ∨→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∨→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ∨→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh ord with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh ord | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨→∨→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∨→←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (lind ←∨) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (lind ←∨) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq ↓ lind ¬hob ¬hoh ord = ⊥-elim (¬hob hitsAtLeastOnce←∂↓)
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (ind ←∂) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∂↓)
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (ind ←∂) (lind ←∂) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (ind ←∂) (lind ←∂) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce←∂←∂ z)) (λ z → ¬hoh (hitsAtLeastOnce←∂←∂ z)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ←∂ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ←∂ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce←∂←∂ z)) (λ z → ¬hoh (hitsAtLeastOnce←∂←∂ z)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ←∂ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ←∂ x₁)
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (ind ←∂) (∂→ lind) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (ind ←∂) (∂→ lind) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (∂→ ind) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∂↓) 
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∂←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (∂→ ind) (lind ←∂) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (∂→ ind) (lind ←∂) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (s ←∂) eq (∂→ ind) (∂→ lind) ¬hob ¬hoh ord with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (s ←∂) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh ord | ∅ with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (s ←∂) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (a≤ᵢb x) | ∅ | .rll | refl = a≤ᵢb (≤ᵢ∂→ x)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (s ←∂) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (b≤ᵢa x) | ∅ | .rll | refl = b≤ᵢa (≤ᵢ∂→ x)
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (s ←∂) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh ord | ¬∅ x with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (s ←∂) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∂→ y)) | ¬∅ x | .rll | refl = a≤ᵢb (≤ᵢ∂→ y)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (s ←∂) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∂→ y)) | ¬∅ x | .rll | refl = b≤ᵢa (≤ᵢ∂→ y)
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq ↓ lind ¬hob ¬hoh ord = ⊥-elim (¬hob hitsAtLeastOnce∂→↓)
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (∂→ ind) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce∂→↓)
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (∂→ ind) (∂→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (∂→ ind) (∂→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce∂→∂→ x)
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce∂→∂→ z)) (λ z → ¬hoh (hitsAtLeastOnce∂→∂→ z)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ∂→ x₁)
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ∂→ x₁)
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] with r where
   r = ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce∂→∂→ z)) (λ z → ¬hoh (hitsAtLeastOnce∂→∂→ z)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] | a≤ᵢb x₁ = a≤ᵢb (≤ᵢ∂→ x₁)
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] | b≤ᵢa x₁ = b≤ᵢa (≤ᵢ∂→ x₁)
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce∂→∂→ x)
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (∂→ ind) (lind ←∂) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (∂→ ind) (lind ←∂) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (ind ←∂) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce∂→↓) 
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce∂→∂→ x)
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (ind ←∂) (∂→ lind) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (ind ←∂) (∂→ lind) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ]
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (∂→ s) eq (ind ←∂) (lind ←∂) ¬hob ¬hoh ord with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (∂→ s) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh ord | ∅ with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (∂→ s) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (a≤ᵢb x) | ∅ | .lll | refl = a≤ᵢb (≤ᵢ←∂ x)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (∂→ s) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (b≤ᵢa x) | ∅ | .lll | refl = b≤ᵢa (≤ᵢ←∂ x)
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (∂→ s) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh ord | ¬∅ x with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (∂→ s) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∂ y)) | ¬∅ x | .lll | refl = a≤ᵢb (≤ᵢ←∂ y)
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (∂→ s) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∂ y)) | ¬∅ x | .lll | refl = b≤ᵢa (≤ᵢ←∂ y)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq ↓ lind ¬hob ¬hoh ord = ⊥-elim (¬hob hitsAtLeastOnce←∂→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∂→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) (lind ←∂) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s | complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) (lind ←∂) ¬hob ¬hoh ord | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂→←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ with ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∂→←∂ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∂→←∂ x₁)) ord
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | a≤ᵢb y = a≤ᵢb (≤ᵢ←∂ y)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | b≤ᵢa y = b≤ᵢa (≤ᵢ←∂ y)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∂→←∂ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∂→←∂ x₁)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ←∂ z)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (a≤ᵢb (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ←∂ z)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∂→←∂ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∂→←∂ x₁)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ←∂ z)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh (b≤ᵢa (≤ᵢ←∂ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ←∂ z)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh ord with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂→←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∂→∂→ x) 
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (∂→ lind) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (∂→ lind) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) ↓ ¬hob ¬hoh ord = ⊥-elim (¬hoh hitsAtLeastOnce←∂→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) (∂→ lind) ¬hob ¬hoh ord with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) (∂→ lind) ¬hob ¬hoh ord | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂→∂→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ with ¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∂→∂→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∂→∂→ x₁)) ord
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | a≤ᵢb y = a≤ᵢb (≤ᵢ∂→ y)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | b≤ᵢa y = b≤ᵢa (≤ᵢ∂→ y)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∂→∂→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∂→∂→ x₁)) (a≤ᵢb y)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ∂→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (a≤ᵢb (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ∂→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ with ¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∂→∂→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∂→∂→ x₁)) (b≤ᵢa y)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | a≤ᵢb z = a≤ᵢb (≤ᵢ∂→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh (b≤ᵢa (≤ᵢ∂→ y)) | ¬∅ x | [ ieq ] | ¬∅ x₁ | b≤ᵢa z = b≤ᵢa (≤ᵢ∂→ z)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh ord with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh ord | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂→∂→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh ord | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∂→←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (lind ←∂) ¬hob ¬hoh (a≤ᵢb ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (lind ←∂) ¬hob ¬hoh (b≤ᵢa ()) | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ]

 
