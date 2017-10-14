-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS --show-irrelevant #-}

module LinFunContruct where

open import Common
open import LinLogic
import IndexLLProp
open import LinFun
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
  ¬ho-shr-morph-pres-¬ord ↓ () ind lind ¬hob ¬hoh
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq ↓ lind ¬hob ¬hoh = ⊥-elim (¬hob hitsAtLeastOnce←∧↓)
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∧↓)
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh | ¬∅ x | [ ieq ] = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce←∧←∧ z)) (λ z → ¬hoh (hitsAtLeastOnce←∧←∧ z)) (ord-spec {ic = ic←∧} ord))
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (ind ←∧) (∧→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (∧→ ind) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∧↓) 
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∧) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∧←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧) refl (∧→ ind) (lind ←∧) ¬hob ¬hoh | ¬∅ x | [ ieq ] =  λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (s ←∧) eq (∧→ ind) (∧→ lind) ¬hob ¬hoh with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (s ←∧) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh | ∅ with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (s ←∧) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh | ∅ | .rll | refl = ord-ext
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (s ←∧) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh | ¬∅ x with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (s ←∧) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh | ¬∅ x | .rll | refl = λ { (a≤ᵢb (≤ᵢ∧→ x₁)) → a≤ᵢb (≤ᵢ∧→ x₁) ; (b≤ᵢa (≤ᵢ∧→ x₁)) → b≤ᵢa (≤ᵢ∧→ x₁)}
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq ↓ lind ¬hob ¬hoh = ⊥-elim (¬hob hitsAtLeastOnce∧→↓)
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (∧→ ind) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce∧→↓)
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (∧→ ind) (∧→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (∧→ ind) (∧→ lind) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce∧→∧→ x)
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] = r where
   r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce∧→∧→ z)) (λ z → ¬hoh (hitsAtLeastOnce∧→∧→ z)) (ord-spec ord))
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce∧→∧→ x)
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (∧→ ind) (lind ←∧) ¬hob ¬hoh | ¬∅ x | [ ieq ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (ind ←∧) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce∧→↓) 
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∧→ s) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce∧→∧→ x)
  ¬ho-shr-morph-pres-¬ord (∧→ s) refl (ind ←∧) (∧→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] =  λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (∧→ s) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (∧→ s) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh | ∅ with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (∧→ s) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh | ∅ | .lll | refl
    = λ { (a≤ᵢb x) → a≤ᵢb (≤ᵢ←∧ x) ; (b≤ᵢa x) → b≤ᵢa (≤ᵢ←∧ x) }
  ¬ho-shr-morph-pres-¬ord {ll = lll ∧ rll} (∧→ s) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh | ¬∅ x with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∧ rll} (∧→ s) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh | ¬∅ x | .lll | refl
    = λ { (a≤ᵢb (≤ᵢ←∧ x₁)) → a≤ᵢb (≤ᵢ←∧ x₁) ; (b≤ᵢa (≤ᵢ←∧ x₁)) → b≤ᵢa (≤ᵢ←∧ x₁) } 
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq ↓ lind ¬hob ¬hoh = ⊥-elim (¬hob hitsAtLeastOnce←∧→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∧→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh with complLₛ s | inspect complLₛ s | complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧→←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∧→←∧ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∧→←∧ x₁)) ord)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (lind ←∧) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∧→←∧ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∧→←∧ x₁)) (ord-spec ord))
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧→←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∧→∧→ x) 
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (ind ←∧) (∧→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∧→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) (∧→ lind) ¬hob ¬hoh with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) (∧→ lind) ¬hob ¬hoh | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧→∧→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∧→∧→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∧→∧→ x₁)) ord)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (∧→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∧→∧→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∧→∧→ x₁)) (ord-spec ord))
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∧→∧→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∧→←∧ x)
  ¬ho-shr-morph-pres-¬ord (s ←∧→ s₁) refl (∧→ ind) (lind ←∧) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq ↓ lind ¬hob ¬hoh = ⊥-elim (¬hob hitsAtLeastOnce←∨↓)
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (ind ←∨) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∨↓)
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (ind ←∨) (lind ←∨) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (ind ←∨) (lind ←∨) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh | ¬∅ x | [ ieq ] = r where
   r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce←∨←∨ z)) (λ z → ¬hoh (hitsAtLeastOnce←∨←∨ z)) (ord-spec ord))
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (ind ←∨) (∨→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (∨→ ind) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∨↓) 
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∨) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∨←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨) refl (∨→ ind) (lind ←∨) ¬hob ¬hoh | ¬∅ x | [ ieq ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (s ←∨) eq (∨→ ind) (∨→ lind) ¬hob ¬hoh with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (s ←∨) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh | ∅ with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (s ←∨) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh | ∅ | .rll | refl = ord-ext
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (s ←∨) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh | ¬∅ x with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (s ←∨) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh | ¬∅ x | .rll | refl = λ { (a≤ᵢb (≤ᵢ∨→ x₁)) → a≤ᵢb (≤ᵢ∨→ x₁) ; (b≤ᵢa (≤ᵢ∨→ x₁)) → b≤ᵢa (≤ᵢ∨→ x₁)}
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq ↓ lind ¬hob ¬hoh = ⊥-elim (¬hob hitsAtLeastOnce∨→↓)
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (∨→ ind) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce∨→↓)
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (∨→ ind) (∨→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (∨→ ind) (∨→ lind) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce∨→∨→ x)
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] = r where
   r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce∨→∨→ z)) (λ z → ¬hoh (hitsAtLeastOnce∨→∨→ z)) (ord-spec ord))
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬ho-spec ¬hob (compl≡∅⇒ho s ieq ind))
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (∨→ ind) (lind ←∨) ¬hob ¬hoh | ¬∅ x | [ ieq ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (ind ←∨) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce∨→↓) 
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∨→ s) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce∨→∨→ x)
  ¬ho-shr-morph-pres-¬ord (∨→ s) refl (ind ←∨) (∨→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (∨→ s) eq (ind ←∨) (lind ←∨) ¬hob ¬hoh with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (∨→ s) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh | ∅ with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (∨→ s) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh | ∅ | .lll | refl = ord-ext
  ¬ho-shr-morph-pres-¬ord {ll = lll ∨ rll} (∨→ s) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh | ¬∅ x with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∨ rll} (∨→ s) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh | ¬∅ x | .lll | refl = λ { (a≤ᵢb (≤ᵢ←∨ x₁)) → a≤ᵢb (≤ᵢ←∨ x₁) ; (b≤ᵢa (≤ᵢ←∨ x₁)) → b≤ᵢa (≤ᵢ←∨ x₁)}
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq ↓ lind ¬hob ¬hoh = ⊥-elim (¬hob hitsAtLeastOnce←∨→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∨→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) (lind ←∨) ¬hob ¬hoh with complLₛ s | inspect complLₛ s | complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) (lind ←∨) ¬hob ¬hoh | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨→←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∨→←∨ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∨→←∨ x₁)) ord)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (lind ←∨) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∨→←∨ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∨→←∨ x₁)) (ord-spec ord))
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨→←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (ind ←∨) (∨→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∨→∨→ x) 
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (ind ←∨) (∨→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∨→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) (∨→ lind) ¬hob ¬hoh with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) (∨→ lind) ¬hob ¬hoh | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨→∨→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∨→∨→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∨→∨→ x₁)) ord)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (∨→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∨→∨→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∨→∨→ x₁)) (ord-spec ord))
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∨→∨→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) eq (∨→ ind) (lind ←∨) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∨→←∨ x)
  ¬ho-shr-morph-pres-¬ord (s ←∨→ s₁) refl (∨→ ind) (lind ←∨) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq ↓ lind ¬hob ¬hoh = ⊥-elim (¬hob hitsAtLeastOnce←∂↓)
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (ind ←∂) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∂↓)
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (ind ←∂) (lind ←∂) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (ind ←∂) (lind ←∂) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh | ¬∅ x | [ ieq ] = r where
   r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce←∂←∂ z)) (λ z → ¬hoh (hitsAtLeastOnce←∂←∂ z)) (ord-spec ord))
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (ind ←∂) (∂→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (∂→ ind) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∂↓) 
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∂) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∂←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂) refl (∂→ ind) (lind ←∂) ¬hob ¬hoh | ¬∅ x | [ ieq ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (s ←∂) eq (∂→ ind) (∂→ lind) ¬hob ¬hoh with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (s ←∂) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh | ∅ with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (s ←∂) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh | ∅ | .rll | refl = ord-ext
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (s ←∂) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh | ¬∅ x with shrink rll (fillAllLower rll) | shr-fAL-id rll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (s ←∂) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh | ¬∅ x | .rll | refl = λ { (a≤ᵢb (≤ᵢ∂→ x₁)) → a≤ᵢb (≤ᵢ∂→ x₁) ; (b≤ᵢa (≤ᵢ∂→ x₁)) → b≤ᵢa (≤ᵢ∂→ x₁)}
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq ↓ lind ¬hob ¬hoh = ⊥-elim (¬hob hitsAtLeastOnce∂→↓)
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (∂→ ind) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce∂→↓)
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (∂→ ind) (∂→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (∂→ ind) (∂→ lind) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce∂→∂→ x)
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] = r where
   r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ z → ¬hob (hitsAtLeastOnce∂→∂→ z)) (λ z → ¬hoh (hitsAtLeastOnce∂→∂→ z)) (ord-spec ord))
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind))  where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce∂→∂→ x)
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (∂→ ind) (lind ←∂) ¬hob ¬hoh | ¬∅ x | [ ieq ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (ind ←∂) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce∂→↓) 
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (∂→ s) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh | ∅ | [ ieq ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq lind))  where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce∂→∂→ x)
  ¬ho-shr-morph-pres-¬ord (∂→ s) refl (ind ←∂) (∂→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (∂→ s) eq (ind ←∂) (lind ←∂) ¬hob ¬hoh with complLₛ s 
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (∂→ s) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh | ∅ with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (∂→ s) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh | ∅ | .lll | refl = ord-ext
  ¬ho-shr-morph-pres-¬ord {ll = lll ∂ rll} (∂→ s) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh | ¬∅ x with shrink lll (fillAllLower lll) | shr-fAL-id lll
  ¬ho-shr-morph-pres-¬ord {u = _} {lll ∂ rll} (∂→ s) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh | ¬∅ x | .lll | refl = λ { (a≤ᵢb (≤ᵢ←∂ x₁)) → a≤ᵢb (≤ᵢ←∂ x₁) ; (b≤ᵢa (≤ᵢ←∂ x₁)) → b≤ᵢa (≤ᵢ←∂ x₁)}
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq ↓ lind ¬hob ¬hoh = ⊥-elim (¬hob hitsAtLeastOnce←∂→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∂→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) (lind ←∂) ¬hob ¬hoh with complLₛ s | inspect complLₛ s | complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) (lind ←∂) ¬hob ¬hoh | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂→←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∂→←∂ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∂→←∂ x₁)) ord)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (lind ←∂) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∂→←∂ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∂→←∂ x₁)) (ord-spec ord))
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂→←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (ind ←∂) (∂→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∂→∂→ x) 
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (ind ←∂) (∂→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) ↓ ¬hob ¬hoh = ⊥-elim (¬hoh hitsAtLeastOnce←∂→↓)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) (∂→ lind) ¬hob ¬hoh with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) (∂→ lind) ¬hob ¬hoh | ∅ | [ ieq ] | e = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂→∂→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∂→∂→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∂→∂→ x₁)) ord)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (∂→ lind) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ = r where
    r = λ ord → ord-ext (¬ho-shr-morph-pres-¬ord s₁ ieq ind lind (λ x₁ → ¬hob (hitsAtLeastOnce←∂→∂→ x₁)) (λ x₁ → ¬hoh (hitsAtLeastOnce←∂→∂→ x₁)) (ord-spec ord))
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh | ∅ | [ ieq ] | e | r = ⊥-elim (¬nho (compl≡∅⇒ho s₁ ieq ind)) where
    ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
    ¬nho x = ¬hob (hitsAtLeastOnce←∂→∂→ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) eq (∂→ ind) (lind ←∂) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ∅ | [ ieq1 ] = ⊥-elim (¬nho (compl≡∅⇒ho s ieq1 lind)) where
    ¬nho : ¬ (hitsAtLeastOnce s lind)
    ¬nho x = ¬hoh (hitsAtLeastOnce←∂→←∂ x)
  ¬ho-shr-morph-pres-¬ord (s ←∂→ s₁) refl (∂→ ind) (lind ←∂) ¬hob ¬hoh | ¬∅ x | [ ieq ] | ¬∅ x₁ | [ ieq1 ] = λ { (a≤ᵢb ()) ; (b≤ᵢa ())}

    
   
  ho-shr-morph : ∀{i u rll ll cs trs ctrs} → (s : SetLL {i} {u} ll) → (ceq : complLₛ s ≡ ¬∅ cs)
                 → (ind : IndexLL rll ll)
                 → ¬∅ trs ≡ truncSetLL s ind
                 → (ceqt : complLₛ trs ≡ ¬∅ ctrs)
                 → IndexLL (shrinkcms rll trs ctrs ceqt) (shrinkcms ll s cs ceq)
  ho-shr-morph ↓ () ind teq ceqt
  ho-shr-morph q@(s ←∧) ceq ↓ refl ceqt with complLₛ q
  ho-shr-morph (s ←∧) refl ↓ refl refl | .(¬∅ _) = ↓
  ho-shr-morph {trs = trs} (s ←∧) ceq (ind ←∧) teq ceqt with complLₛ s | inspect complLₛ s
  ... | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eq ind teq
  ho-shr-morph {trs = trs} (s ←∧) ceq (ind ←∧) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (s ←∧) refl (ind ←∧) teq ceqt | ¬∅ x | [ eq ] = is ←∧ where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph (s ←∧) ceq (∧→ ind) () ceqt
  ho-shr-morph q@(∧→ s) ceq ↓ refl ceqt with complLₛ q
  ho-shr-morph (∧→ s) refl ↓ refl refl | .(¬∅ _) = ↓
  ho-shr-morph (∧→ s) ceq (ind ←∧) () ceqt
  ho-shr-morph (∧→ s) ceq (∧→ ind) teq ceqt with complLₛ s | inspect complLₛ s
  ho-shr-morph {trs = trs} (∧→ s) ceq (∧→ ind) teq ceqt | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eq ind teq
  ho-shr-morph {trs = trs} (∧→ s) ceq (∧→ ind) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (∧→ s) refl (∧→ ind) teq ceqt | ¬∅ x | [ eq ] = ∧→ is where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph q@(s ←∧→ s₁) ceq ↓ refl ceqt with complLₛ q
  ho-shr-morph (s ←∧→ s₁) refl ↓ refl refl | .(¬∅ _) = ↓
  ho-shr-morph (s ←∧→ s₁) ceq (ind ←∧) teq ceqt with complLₛ s | inspect complLₛ s
  ho-shr-morph {trs = trs} (s ←∧→ s₁) ceq (ind ←∧) teq ceqt | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eq ind teq
  ho-shr-morph {trs = trs} (s ←∧→ s₁) ceq (ind ←∧) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (s ←∧→ s₁) ceq (ind ←∧) teq ceqt | ¬∅ x | e with complLₛ s₁
  ho-shr-morph (s ←∧→ s₁) refl (ind ←∧) teq ceqt | ¬∅ x | [ eq ] | ∅ = is where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph (s ←∧→ s₁) refl (ind ←∧) teq ceqt | ¬∅ x₁ | [ eq ] | ¬∅ x = is ←∧ where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph (s ←∧→ s₁) ceq (∧→ ind) teq ceqt with complLₛ s₁ | inspect complLₛ s₁
  ho-shr-morph {trs = trs} (s ←∧→ s₁) ceq (∧→ ind) teq ceqt | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s₁ eq ind teq
  ho-shr-morph {trs = trs} (s ←∧→ s₁) ceq (∧→ ind) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (s ←∧→ s₁) ceq (∧→ ind) teq ceqt | ¬∅ x | [ eq ] with complLₛ s
  ho-shr-morph (s ←∧→ s₁) refl (∧→ ind) teq ceqt | ¬∅ x | [ eq ] | ∅ = is where
    is = ho-shr-morph s₁ eq ind teq ceqt
  ho-shr-morph (s ←∧→ s₁) refl (∧→ ind) teq ceqt | ¬∅ x₁ | [ eq ] | ¬∅ x = ∧→ is where
    is = ho-shr-morph s₁ eq ind teq ceqt
  ho-shr-morph q@(s ←∨) ceq ↓ refl ceqt with complLₛ q
  ho-shr-morph (s ←∨) refl ↓ refl refl | .(¬∅ _) = ↓
  ho-shr-morph {trs = trs} (s ←∨) ceq (ind ←∨) teq ceqt with complLₛ s | inspect complLₛ s
  ... | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eq ind teq
  ho-shr-morph {trs = trs} (s ←∨) ceq (ind ←∨) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (s ←∨) refl (ind ←∨) teq ceqt | ¬∅ x | [ eq ] = is ←∨ where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph (s ←∨) ceq (∨→ ind) () ceqt
  ho-shr-morph q@(∨→ s) ceq ↓ refl ceqt with complLₛ q
  ho-shr-morph (∨→ s) refl ↓ refl refl | .(¬∅ _) = ↓
  ho-shr-morph (∨→ s) ceq (ind ←∨) () ceqt
  ho-shr-morph (∨→ s) ceq (∨→ ind) teq ceqt with complLₛ s | inspect complLₛ s
  ho-shr-morph {trs = trs} (∨→ s) ceq (∨→ ind) teq ceqt | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eq ind teq
  ho-shr-morph {trs = trs} (∨→ s) ceq (∨→ ind) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (∨→ s) refl (∨→ ind) teq ceqt | ¬∅ x | [ eq ] = ∨→ is where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph q@(s ←∨→ s₁) ceq ↓ refl ceqt with complLₛ q
  ho-shr-morph (s ←∨→ s₁) refl ↓ refl refl | .(¬∅ _) = ↓
  ho-shr-morph (s ←∨→ s₁) ceq (ind ←∨) teq ceqt with complLₛ s | inspect complLₛ s
  ho-shr-morph {trs = trs} (s ←∨→ s₁) ceq (ind ←∨) teq ceqt | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eq ind teq
  ho-shr-morph {trs = trs} (s ←∨→ s₁) ceq (ind ←∨) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (s ←∨→ s₁) ceq (ind ←∨) teq ceqt | ¬∅ x | e with complLₛ s₁
  ho-shr-morph (s ←∨→ s₁) refl (ind ←∨) teq ceqt | ¬∅ x | [ eq ] | ∅ = is where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph (s ←∨→ s₁) refl (ind ←∨) teq ceqt | ¬∅ x₁ | [ eq ] | ¬∅ x = is ←∨ where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph (s ←∨→ s₁) ceq (∨→ ind) teq ceqt with complLₛ s₁ | inspect complLₛ s₁
  ho-shr-morph {trs = trs} (s ←∨→ s₁) ceq (∨→ ind) teq ceqt | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s₁ eq ind teq
  ho-shr-morph {trs = trs} (s ←∨→ s₁) ceq (∨→ ind) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (s ←∨→ s₁) ceq (∨→ ind) teq ceqt | ¬∅ x | [ eq ] with complLₛ s
  ho-shr-morph (s ←∨→ s₁) refl (∨→ ind) teq ceqt | ¬∅ x | [ eq ] | ∅ = is where
    is = ho-shr-morph s₁ eq ind teq ceqt
  ho-shr-morph (s ←∨→ s₁) refl (∨→ ind) teq ceqt | ¬∅ x₁ | [ eq ] | ¬∅ x = ∨→ is where
    is = ho-shr-morph s₁ eq ind teq ceqt
  ho-shr-morph q@(s ←∂) ceq ↓ refl ceqt with complLₛ q
  ho-shr-morph (s ←∂) refl ↓ refl refl | .(¬∅ _) = ↓
  ho-shr-morph {trs = trs} (s ←∂) ceq (ind ←∂) teq ceqt with complLₛ s | inspect complLₛ s
  ... | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eq ind teq
  ho-shr-morph {trs = trs} (s ←∂) ceq (ind ←∂) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (s ←∂) refl (ind ←∂) teq ceqt | ¬∅ x | [ eq ] = is ←∂ where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph (s ←∂) ceq (∂→ ind) () ceqt
  ho-shr-morph q@(∂→ s) ceq ↓ refl ceqt with complLₛ q
  ho-shr-morph (∂→ s) refl ↓ refl refl | .(¬∅ _) = ↓
  ho-shr-morph (∂→ s) ceq (ind ←∂) () ceqt
  ho-shr-morph (∂→ s) ceq (∂→ ind) teq ceqt with complLₛ s | inspect complLₛ s
  ho-shr-morph {trs = trs} (∂→ s) ceq (∂→ ind) teq ceqt | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eq ind teq
  ho-shr-morph {trs = trs} (∂→ s) ceq (∂→ ind) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (∂→ s) refl (∂→ ind) teq ceqt | ¬∅ x | [ eq ] = ∂→ is where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph q@(s ←∂→ s₁) ceq ↓ refl ceqt with complLₛ q
  ho-shr-morph (s ←∂→ s₁) refl ↓ refl refl | .(¬∅ _) = ↓
  ho-shr-morph (s ←∂→ s₁) ceq (ind ←∂) teq ceqt with complLₛ s | inspect complLₛ s
  ho-shr-morph {trs = trs} (s ←∂→ s₁) ceq (ind ←∂) teq ceqt | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eq ind teq
  ho-shr-morph {trs = trs} (s ←∂→ s₁) ceq (ind ←∂) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (s ←∂→ s₁) ceq (ind ←∂) teq ceqt | ¬∅ x | e with complLₛ s₁
  ho-shr-morph (s ←∂→ s₁) refl (ind ←∂) teq ceqt | ¬∅ x | [ eq ] | ∅ = is where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph (s ←∂→ s₁) refl (ind ←∂) teq ceqt | ¬∅ x₁ | [ eq ] | ¬∅ x = is ←∂ where
    is = ho-shr-morph s eq ind teq ceqt
  ho-shr-morph (s ←∂→ s₁) ceq (∂→ ind) teq ceqt with complLₛ s₁ | inspect complLₛ s₁
  ho-shr-morph {trs = trs} (s ←∂→ s₁) ceq (∂→ ind) teq ceqt | ∅ | [ eq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s₁ eq ind teq
  ho-shr-morph {trs = trs} (s ←∂→ s₁) ceq (∂→ ind) teq () | ∅ | [ eq ] | .∅ | refl
  ho-shr-morph (s ←∂→ s₁) ceq (∂→ ind) teq ceqt | ¬∅ x | [ eq ] with complLₛ s
  ho-shr-morph (s ←∂→ s₁) refl (∂→ ind) teq ceqt | ¬∅ x | [ eq ] | ∅ = is where
    is = ho-shr-morph s₁ eq ind teq ceqt
  ho-shr-morph (s ←∂→ s₁) refl (∂→ ind) teq ceqt | ¬∅ x₁ | [ eq ] | ¬∅ x = ∂→ is where
    is = ho-shr-morph s₁ eq ind teq ceqt





  shrink-repl-comm : ∀{i u ll ell pll x} → (s : SetLL ll) → (lind : IndexLL {i} {u} pll ll)
        → (eq : complLₛ s ≡ ¬∅ x)
        → (teq : truncSetLL s lind ≡ ∅)
        → ∀{mx}
        → del s lind ell ≡ ¬∅ mx
        → ∀{cs}
        → complLₛ mx ≡ ¬∅ cs
        → (shrink (replLL ll lind ell) cs) ≡ replLL (shrink ll x) (¬ho-shr-morph s eq lind (trunc≡∅⇒¬ho s lind teq)) ell
  shrink-repl-comm ↓ lind () teq meq ceq
  shrink-repl-comm (s ←∧) ↓ eq teq meq ceq = ⊥-elim (¬ho hitsAtLeastOnce←∧↓) where
    ¬ho = trunc≡∅⇒¬ho (s ←∧) ↓ teq
  shrink-repl-comm {ll = _ ∧ rs} {ell = ell} (s ←∧) (lind ←∧) eq teq {mx} meq ceq with complLₛ s | inspect complLₛ s | del s lind ell | inspect (del s lind) ell
  ... | ∅ | [ qeq ] | w | t = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {ell = ell} (s ←∧) (lind ←∧) eq teq () ceq | ¬∅ q | [ qeq ] | ∅ | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∧) (lind ←∧) eq teq {↓} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∧) (lind ←∧) eq teq {.nmx ←∧} refl ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  ... | ∅ | [ nceq ] = ⊥-elim (del⇒¬ho s lind (sym deq) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  shrink-repl-comm {ll = _ ∧ rs} {ell = ell} (s ←∧) (lind ←∧) refl teq {.nmx ←∧} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] = cong (λ z → z ∧ (shrink rs (fillAllLower rs))) r where
    r = shrink-repl-comm s lind qeq teq deq nceq 
  shrink-repl-comm {ell = ell} (s ←∧) (lind ←∧) eq teq {∧→ mx} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∧) (lind ←∧) eq teq {mx ←∧→ mx₁} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ll = _ ∧ rs} {ell} (s ←∧) (∧→ lind) eq teq refl ceq with complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {_ ∧ rs} {ell} (s ←∧) (∧→ lind) refl teq refl refl | ¬∅ q | [ qeq ] with shrink rs (fillAllLower rs) | shr-fAL-id rs | shrink (replLL rs lind ell) (fillAllLower (replLL rs lind ell)) | shr-fAL-id (replLL rs lind ell)
  shrink-repl-comm {u = _} {_ ∧ rs} {ell} (s ←∧) (∧→ lind) refl teq refl refl | ¬∅ q | [ qeq ] | .rs | refl | .(replLL rs lind ell) | refl = refl
  shrink-repl-comm {ll = _ ∧ rs} {ell} (s ←∧) (∧→ lind) refl teq refl refl | ∅ | [ qeq ] with shrink rs (fillAllLower rs) | shr-fAL-id rs | shrink (replLL rs lind ell) (fillAllLower (replLL rs lind ell)) | shr-fAL-id (replLL rs lind ell)
  shrink-repl-comm {u = _} {_ ∧ rs} {ell} (s ←∧) (∧→ lind) refl teq refl refl | ∅ | [ qeq ] | .rs | refl | .(replLL rs lind ell) | refl = refl
  shrink-repl-comm {ll = ls ∧ _} {ell} (∧→ s) ↓ eq teq meq ceq =  ⊥-elim (¬ho hitsAtLeastOnce∧→↓) where
    ¬ho = trunc≡∅⇒¬ho (∧→ s) ↓ teq
  shrink-repl-comm {ll = ls ∧ _} {ell} (∧→ s) (lind ←∧) eq teq refl ceq with complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {ls ∧ _} {ell} (∧→ s) (lind ←∧) refl teq refl refl | ¬∅ q | [ qeq ] with shrink ls (fillAllLower ls) | shr-fAL-id ls | shrink (replLL ls lind ell) (fillAllLower (replLL ls lind ell)) | shr-fAL-id (replLL ls lind ell)
  ... | .ls | refl | .(replLL ls lind ell) | refl = refl
  shrink-repl-comm {u = _} {ls ∧ _} {ell} (∧→ s) (lind ←∧) refl teq refl refl | ∅ | [ qeq ] with shrink ls (fillAllLower ls) | shr-fAL-id ls | shrink (replLL ls lind ell) (fillAllLower (replLL ls lind ell)) | shr-fAL-id (replLL ls lind ell)
  ... | .ls | refl | .(replLL ls lind ell) | refl = refl
  shrink-repl-comm {ll = ls ∧ _} {ell} (∧→ s) (∧→ lind) eq teq {mx} meq ceq with complLₛ s | inspect complLₛ s | del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∧ _} {ell} (∧→ s) (∧→ lind) eq teq {mx} meq ceq | ∅ | [ qeq ] | w | t = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {u = _} {ls ∧ _} {ell} (∧→ s) (∧→ lind) eq teq {mx} () ceq | ¬∅ q | [ qeq ] | ∅ | [ deq ]
  shrink-repl-comm {u = _} {ls ∧ _} {ell} (∧→ s) (∧→ lind) eq teq {↓} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {u = _} {ls ∧ _} {ell} (∧→ s) (∧→ lind) eq teq {mx ←∧} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {u = _} {ls ∧ _} {ell} (∧→ s) (∧→ lind) eq teq {∧→ .nmx} refl ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  ... | ∅ | [ nceq ] = ⊥-elim (del⇒¬ho s lind (sym deq) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  shrink-repl-comm {u = _} {ls ∧ _} {ell} (∧→ s) (∧→ lind) refl teq {∧→ .nmx} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] = cong (λ z → (shrink ls (fillAllLower ls)) ∧ z) r where
    r = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∧ _} {ell} (∧→ s) (∧→ lind) eq teq {mx ←∧→ mx₁} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ll = ls ∧ rs} {ell} (s ←∧→ s₁) ↓ eq teq meq ceq = ⊥-elim (¬ho hitsAtLeastOnce←∧→↓) where
    ¬ho = trunc≡∅⇒¬ho (s ←∧→ s₁) ↓ teq
  shrink-repl-comm {ll = ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) eq teq meq ceq  with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) eq teq meq ceq | ∅ | [ qeq ] | e | _ = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
    hf : (complLₛ (nmx ←∧→ s₁) ≡ ¬∅ cs) → (complLₛ s₁ ≡ ¬∅ e) → shrink (replLL ls lind ell ∧ rs) cs ≡ (replLL (shrink ls q) (¬ho-shr-morph s qeq lind (trunc≡∅⇒¬ho s lind teq)) ell ∧ shrink rs e)
    hf ceq eeq with complLₛ nmx | inspect complLₛ nmx | complLₛ s₁
    hf ceq eeq | ∅ | [ nceq ] | c =  ⊥-elim ((del⇒¬ho s lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
    hf ceq () | ¬∅ ncs | [ nceq ] | ∅
    hf refl refl | ¬∅ ncs | [ nceq ] | ¬∅ e = cong (λ z → z ∧ (shrink rs e)) r where
      r = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | eeq with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
    hf : (complLₛ (nmx ←∧→ s₁) ≡ ¬∅ cs) → (complLₛ s₁ ≡ ∅) → shrink (replLL ls lind ell ∧ rs) cs ≡
                                                               replLL (shrink ls q)
                                                               (¬ho-shr-morph s qeq lind (trunc≡∅⇒¬ho s lind teq)) ell
    hf ceq eeq with complLₛ nmx | inspect complLₛ nmx
    hf ceq eeq | ∅ | [ nceq ] with complLₛ s₁
    hf () eeq | ∅ | [ nceq ] | ∅
    hf ceq () | ∅ | [ nceq ] | ¬∅ x
    hf ceq eeq | ¬∅ x | [ nceq ] with complLₛ s₁
    hf refl eeq | ¬∅ x | [ nceq ] | ∅ = shrink-repl-comm s lind qeq teq deq nceq
    hf ceq () | ¬∅ x | [ nceq ] | ¬∅ x₁
  shrink-repl-comm {ll = ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) eq teq meq ceq with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) eq teq meq ceq | ∅ | [ qeq ] | e | [ eeq ] =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s₁ lind teq
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
     hf : (complLₛ (s ←∧→ nmx) ≡ ¬∅ cs) → (complLₛ s ≡ ¬∅ e) → shrink (ls ∧ replLL rs lind ell) cs ≡
                                                                 (shrink ls e ∧
                                                                  replLL (shrink rs q)
                                                                  (¬ho-shr-morph s₁ qeq lind (trunc≡∅⇒¬ho s₁ lind teq)) ell)
     hf ceq eeq with complLₛ nmx | inspect complLₛ nmx
     hf ceq eeq | ∅ | [ nceq ] with complLₛ s
     hf ceq () | ∅ | [ nceq ] | ∅
     hf refl refl | ∅ | [ nceq ] | ¬∅ x = ⊥-elim ((del⇒¬ho s₁ lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
     hf ceq eeq | ¬∅ ncs | [ nceq ] with complLₛ s
     hf ceq () | ¬∅ ncs | [ nceq ] | ∅
     hf refl refl | ¬∅ ncs | [ nceq ] | ¬∅ x = cong (λ z → (shrink ls x) ∧ z) r where
       r = shrink-repl-comm s₁ lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
    hf : (complLₛ (s ←∧→ nmx) ≡ ¬∅ cs) → (complLₛ s ≡ ∅) → shrink (ls ∧ replLL rs lind ell) cs ≡
                                                             replLL (shrink rs q)
                                                             (¬ho-shr-morph s₁ qeq lind (trunc≡∅⇒¬ho s₁ lind teq)) ell
    hf ceq eeq with complLₛ nmx | inspect complLₛ nmx | complLₛ s
    hf () refl | ∅ | [ nceq ] | ∅
    hf refl refl | ¬∅ ncs | [ nceq ] | ∅ = shrink-repl-comm s₁ lind qeq teq deq nceq
    hf ceq () | ncs | [ nceq ] | ¬∅ x
  shrink-repl-comm (s ←∨) ↓ eq teq meq ceq = ⊥-elim (¬ho hitsAtLeastOnce←∨↓) where
    ¬ho = trunc≡∅⇒¬ho (s ←∨) ↓ teq
  shrink-repl-comm {ll = _ ∨ rs} {ell = ell} (s ←∨) (lind ←∨) eq teq {mx} meq ceq with complLₛ s | inspect complLₛ s | del s lind ell | inspect (del s lind) ell
  ... | ∅ | [ qeq ] | w | t = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {ell = ell} (s ←∨) (lind ←∨) eq teq () ceq | ¬∅ q | [ qeq ] | ∅ | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∨) (lind ←∨) eq teq {↓} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∨) (lind ←∨) eq teq {.nmx ←∨} refl ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  ... | ∅ | [ nceq ] = ⊥-elim (del⇒¬ho s lind (sym deq) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  shrink-repl-comm {ll = _ ∨ rs} {ell = ell} (s ←∨) (lind ←∨) refl teq {.nmx ←∨} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] = cong (λ z → z ∨ (shrink rs (fillAllLower rs))) r where
    r = shrink-repl-comm s lind qeq teq deq nceq 
  shrink-repl-comm {ell = ell} (s ←∨) (lind ←∨) eq teq {∨→ mx} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∨) (lind ←∨) eq teq {mx ←∨→ mx₁} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ll = _ ∨ rs} {ell} (s ←∨) (∨→ lind) eq teq refl ceq with complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {_ ∨ rs} {ell} (s ←∨) (∨→ lind) refl teq refl refl | ¬∅ q | [ qeq ] with shrink rs (fillAllLower rs) | shr-fAL-id rs | shrink (replLL rs lind ell) (fillAllLower (replLL rs lind ell)) | shr-fAL-id (replLL rs lind ell)
  shrink-repl-comm {u = _} {_ ∨ rs} {ell} (s ←∨) (∨→ lind) refl teq refl refl | ¬∅ q | [ qeq ] | .rs | refl | .(replLL rs lind ell) | refl = refl
  shrink-repl-comm {ll = _ ∨ rs} {ell} (s ←∨) (∨→ lind) refl teq refl refl | ∅ | [ qeq ] with shrink rs (fillAllLower rs) | shr-fAL-id rs | shrink (replLL rs lind ell) (fillAllLower (replLL rs lind ell)) | shr-fAL-id (replLL rs lind ell)
  shrink-repl-comm {u = _} {_ ∨ rs} {ell} (s ←∨) (∨→ lind) refl teq refl refl | ∅ | [ qeq ] | .rs | refl | .(replLL rs lind ell) | refl = refl
  shrink-repl-comm {ll = ls ∨ _} {ell} (∨→ s) ↓ eq teq meq ceq =  ⊥-elim (¬ho hitsAtLeastOnce∨→↓) where
    ¬ho = trunc≡∅⇒¬ho (∨→ s) ↓ teq
  shrink-repl-comm {ll = ls ∨ _} {ell} (∨→ s) (lind ←∨) eq teq refl ceq with complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {ls ∨ _} {ell} (∨→ s) (lind ←∨) refl teq refl refl | ¬∅ q | [ qeq ] with shrink ls (fillAllLower ls) | shr-fAL-id ls | shrink (replLL ls lind ell) (fillAllLower (replLL ls lind ell)) | shr-fAL-id (replLL ls lind ell)
  ... | .ls | refl | .(replLL ls lind ell) | refl = refl
  shrink-repl-comm {u = _} {ls ∨ _} {ell} (∨→ s) (lind ←∨) refl teq refl refl | ∅ | [ qeq ] with shrink ls (fillAllLower ls) | shr-fAL-id ls | shrink (replLL ls lind ell) (fillAllLower (replLL ls lind ell)) | shr-fAL-id (replLL ls lind ell)
  ... | .ls | refl | .(replLL ls lind ell) | refl = refl
  shrink-repl-comm {ll = ls ∨ _} {ell} (∨→ s) (∨→ lind) eq teq {mx} meq ceq with complLₛ s | inspect complLₛ s | del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∨ _} {ell} (∨→ s) (∨→ lind) eq teq {mx} meq ceq | ∅ | [ qeq ] | w | t = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {u = _} {ls ∨ _} {ell} (∨→ s) (∨→ lind) eq teq {mx} () ceq | ¬∅ q | [ qeq ] | ∅ | [ deq ]
  shrink-repl-comm {u = _} {ls ∨ _} {ell} (∨→ s) (∨→ lind) eq teq {↓} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {u = _} {ls ∨ _} {ell} (∨→ s) (∨→ lind) eq teq {mx ←∨} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {u = _} {ls ∨ _} {ell} (∨→ s) (∨→ lind) eq teq {∨→ .nmx} refl ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  ... | ∅ | [ nceq ] = ⊥-elim (del⇒¬ho s lind (sym deq) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  shrink-repl-comm {u = _} {ls ∨ _} {ell} (∨→ s) (∨→ lind) refl teq {∨→ .nmx} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] = cong (λ z → (shrink ls (fillAllLower ls)) ∨ z) r where
    r = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∨ _} {ell} (∨→ s) (∨→ lind) eq teq {mx ←∨→ mx₁} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ll = ls ∨ rs} {ell} (s ←∨→ s₁) ↓ eq teq meq ceq = ⊥-elim (¬ho hitsAtLeastOnce←∨→↓) where
    ¬ho = trunc≡∅⇒¬ho (s ←∨→ s₁) ↓ teq
  shrink-repl-comm {ll = ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) eq teq meq ceq  with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) eq teq meq ceq | ∅ | [ qeq ] | e | _ = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
    hf : (complLₛ (nmx ←∨→ s₁) ≡ ¬∅ cs) → (complLₛ s₁ ≡ ¬∅ e) → shrink (replLL ls lind ell ∨ rs) cs ≡ (replLL (shrink ls q) (¬ho-shr-morph s qeq lind (trunc≡∅⇒¬ho s lind teq)) ell ∨ shrink rs e)
    hf ceq eeq with complLₛ nmx | inspect complLₛ nmx | complLₛ s₁
    hf ceq eeq | ∅ | [ nceq ] | c =  ⊥-elim ((del⇒¬ho s lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
    hf ceq () | ¬∅ ncs | [ nceq ] | ∅
    hf refl refl | ¬∅ ncs | [ nceq ] | ¬∅ e = cong (λ z → z ∨ (shrink rs e)) r where
      r = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | eeq with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
    hf : (complLₛ (nmx ←∨→ s₁) ≡ ¬∅ cs) → (complLₛ s₁ ≡ ∅) → shrink (replLL ls lind ell ∨ rs) cs ≡
                                                               replLL (shrink ls q)
                                                               (¬ho-shr-morph s qeq lind (trunc≡∅⇒¬ho s lind teq)) ell
    hf ceq eeq with complLₛ nmx | inspect complLₛ nmx
    hf ceq eeq | ∅ | [ nceq ] with complLₛ s₁
    hf () eeq | ∅ | [ nceq ] | ∅
    hf ceq () | ∅ | [ nceq ] | ¬∅ x
    hf ceq eeq | ¬∅ x | [ nceq ] with complLₛ s₁
    hf refl eeq | ¬∅ x | [ nceq ] | ∅ = shrink-repl-comm s lind qeq teq deq nceq
    hf ceq () | ¬∅ x | [ nceq ] | ¬∅ x₁
  shrink-repl-comm {ll = ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) eq teq meq ceq with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) eq teq meq ceq | ∅ | [ qeq ] | e | [ eeq ] =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s₁ lind teq
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
     hf : (complLₛ (s ←∨→ nmx) ≡ ¬∅ cs) → (complLₛ s ≡ ¬∅ e) → shrink (ls ∨ replLL rs lind ell) cs ≡
                                                                 (shrink ls e ∨
                                                                  replLL (shrink rs q)
                                                                  (¬ho-shr-morph s₁ qeq lind (trunc≡∅⇒¬ho s₁ lind teq)) ell)
     hf ceq eeq with complLₛ nmx | inspect complLₛ nmx
     hf ceq eeq | ∅ | [ nceq ] with complLₛ s
     hf ceq () | ∅ | [ nceq ] | ∅
     hf refl refl | ∅ | [ nceq ] | ¬∅ x = ⊥-elim ((del⇒¬ho s₁ lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
     hf ceq eeq | ¬∅ ncs | [ nceq ] with complLₛ s
     hf ceq () | ¬∅ ncs | [ nceq ] | ∅
     hf refl refl | ¬∅ ncs | [ nceq ] | ¬∅ x = cong (λ z → (shrink ls x) ∨ z) r where
       r = shrink-repl-comm s₁ lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
    hf : (complLₛ (s ←∨→ nmx) ≡ ¬∅ cs) → (complLₛ s ≡ ∅) → shrink (ls ∨ replLL rs lind ell) cs ≡
                                                             replLL (shrink rs q)
                                                             (¬ho-shr-morph s₁ qeq lind (trunc≡∅⇒¬ho s₁ lind teq)) ell
    hf ceq eeq with complLₛ nmx | inspect complLₛ nmx | complLₛ s
    hf () refl | ∅ | [ nceq ] | ∅
    hf refl refl | ¬∅ ncs | [ nceq ] | ∅ = shrink-repl-comm s₁ lind qeq teq deq nceq
    hf ceq () | ncs | [ nceq ] | ¬∅ x
  shrink-repl-comm (s ←∂) ↓ eq teq meq ceq = ⊥-elim (¬ho hitsAtLeastOnce←∂↓) where
    ¬ho = trunc≡∅⇒¬ho (s ←∂) ↓ teq
  shrink-repl-comm {ll = _ ∂ rs} {ell = ell} (s ←∂) (lind ←∂) eq teq {mx} meq ceq with complLₛ s | inspect complLₛ s | del s lind ell | inspect (del s lind) ell
  ... | ∅ | [ qeq ] | w | t = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {ell = ell} (s ←∂) (lind ←∂) eq teq () ceq | ¬∅ q | [ qeq ] | ∅ | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∂) (lind ←∂) eq teq {↓} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∂) (lind ←∂) eq teq {.nmx ←∂} refl ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  ... | ∅ | [ nceq ] = ⊥-elim (del⇒¬ho s lind (sym deq) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  shrink-repl-comm {ll = _ ∂ rs} {ell = ell} (s ←∂) (lind ←∂) refl teq {.nmx ←∂} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] = cong (λ z → z ∂ (shrink rs (fillAllLower rs))) r where
    r = shrink-repl-comm s lind qeq teq deq nceq 
  shrink-repl-comm {ell = ell} (s ←∂) (lind ←∂) eq teq {∂→ mx} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∂) (lind ←∂) eq teq {mx ←∂→ mx₁} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ll = _ ∂ rs} {ell} (s ←∂) (∂→ lind) eq teq refl ceq with complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {_ ∂ rs} {ell} (s ←∂) (∂→ lind) refl teq refl refl | ¬∅ q | [ qeq ] with shrink rs (fillAllLower rs) | shr-fAL-id rs | shrink (replLL rs lind ell) (fillAllLower (replLL rs lind ell)) | shr-fAL-id (replLL rs lind ell)
  shrink-repl-comm {u = _} {_ ∂ rs} {ell} (s ←∂) (∂→ lind) refl teq refl refl | ¬∅ q | [ qeq ] | .rs | refl | .(replLL rs lind ell) | refl = refl
  shrink-repl-comm {ll = _ ∂ rs} {ell} (s ←∂) (∂→ lind) refl teq refl refl | ∅ | [ qeq ] with shrink rs (fillAllLower rs) | shr-fAL-id rs | shrink (replLL rs lind ell) (fillAllLower (replLL rs lind ell)) | shr-fAL-id (replLL rs lind ell)
  shrink-repl-comm {u = _} {_ ∂ rs} {ell} (s ←∂) (∂→ lind) refl teq refl refl | ∅ | [ qeq ] | .rs | refl | .(replLL rs lind ell) | refl = refl
  shrink-repl-comm {ll = ls ∂ _} {ell} (∂→ s) ↓ eq teq meq ceq =  ⊥-elim (¬ho hitsAtLeastOnce∂→↓) where
    ¬ho = trunc≡∅⇒¬ho (∂→ s) ↓ teq
  shrink-repl-comm {ll = ls ∂ _} {ell} (∂→ s) (lind ←∂) eq teq refl ceq with complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {ls ∂ _} {ell} (∂→ s) (lind ←∂) refl teq refl refl | ¬∅ q | [ qeq ] with shrink ls (fillAllLower ls) | shr-fAL-id ls | shrink (replLL ls lind ell) (fillAllLower (replLL ls lind ell)) | shr-fAL-id (replLL ls lind ell)
  ... | .ls | refl | .(replLL ls lind ell) | refl = refl
  shrink-repl-comm {u = _} {ls ∂ _} {ell} (∂→ s) (lind ←∂) refl teq refl refl | ∅ | [ qeq ] with shrink ls (fillAllLower ls) | shr-fAL-id ls | shrink (replLL ls lind ell) (fillAllLower (replLL ls lind ell)) | shr-fAL-id (replLL ls lind ell)
  ... | .ls | refl | .(replLL ls lind ell) | refl = refl
  shrink-repl-comm {ll = ls ∂ _} {ell} (∂→ s) (∂→ lind) eq teq {mx} meq ceq with complLₛ s | inspect complLₛ s | del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∂ _} {ell} (∂→ s) (∂→ lind) eq teq {mx} meq ceq | ∅ | [ qeq ] | w | t = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {u = _} {ls ∂ _} {ell} (∂→ s) (∂→ lind) eq teq {mx} () ceq | ¬∅ q | [ qeq ] | ∅ | [ deq ]
  shrink-repl-comm {u = _} {ls ∂ _} {ell} (∂→ s) (∂→ lind) eq teq {↓} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {u = _} {ls ∂ _} {ell} (∂→ s) (∂→ lind) eq teq {mx ←∂} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {u = _} {ls ∂ _} {ell} (∂→ s) (∂→ lind) eq teq {∂→ .nmx} refl ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  ... | ∅ | [ nceq ] = ⊥-elim (del⇒¬ho s lind (sym deq) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  shrink-repl-comm {u = _} {ls ∂ _} {ell} (∂→ s) (∂→ lind) refl teq {∂→ .nmx} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] = cong (λ z → (shrink ls (fillAllLower ls)) ∂ z) r where
    r = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∂ _} {ell} (∂→ s) (∂→ lind) eq teq {mx ←∂→ mx₁} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ll = ls ∂ rs} {ell} (s ←∂→ s₁) ↓ eq teq meq ceq = ⊥-elim (¬ho hitsAtLeastOnce←∂→↓) where
    ¬ho = trunc≡∅⇒¬ho (s ←∂→ s₁) ↓ teq
  shrink-repl-comm {ll = ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) eq teq meq ceq  with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) eq teq meq ceq | ∅ | [ qeq ] | e | _ = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
    hf : (complLₛ (nmx ←∂→ s₁) ≡ ¬∅ cs) → (complLₛ s₁ ≡ ¬∅ e) → shrink (replLL ls lind ell ∂ rs) cs ≡ (replLL (shrink ls q) (¬ho-shr-morph s qeq lind (trunc≡∅⇒¬ho s lind teq)) ell ∂ shrink rs e)
    hf ceq eeq with complLₛ nmx | inspect complLₛ nmx | complLₛ s₁
    hf ceq eeq | ∅ | [ nceq ] | c =  ⊥-elim ((del⇒¬ho s lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
    hf ceq () | ¬∅ ncs | [ nceq ] | ∅
    hf refl refl | ¬∅ ncs | [ nceq ] | ¬∅ e = cong (λ z → z ∂ (shrink rs e)) r where
      r = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | eeq with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
    hf : (complLₛ (nmx ←∂→ s₁) ≡ ¬∅ cs) → (complLₛ s₁ ≡ ∅) → shrink (replLL ls lind ell ∂ rs) cs ≡
                                                               replLL (shrink ls q)
                                                               (¬ho-shr-morph s qeq lind (trunc≡∅⇒¬ho s lind teq)) ell
    hf ceq eeq with complLₛ nmx | inspect complLₛ nmx
    hf ceq eeq | ∅ | [ nceq ] with complLₛ s₁
    hf () eeq | ∅ | [ nceq ] | ∅
    hf ceq () | ∅ | [ nceq ] | ¬∅ x
    hf ceq eeq | ¬∅ x | [ nceq ] with complLₛ s₁
    hf refl eeq | ¬∅ x | [ nceq ] | ∅ = shrink-repl-comm s lind qeq teq deq nceq
    hf ceq () | ¬∅ x | [ nceq ] | ¬∅ x₁
  shrink-repl-comm {ll = ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) eq teq meq ceq with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) eq teq meq ceq | ∅ | [ qeq ] | e | [ eeq ] =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s₁ lind teq
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
     hf : (complLₛ (s ←∂→ nmx) ≡ ¬∅ cs) → (complLₛ s ≡ ¬∅ e) → shrink (ls ∂ replLL rs lind ell) cs ≡
                                                                 (shrink ls e ∂
                                                                  replLL (shrink rs q)
                                                                  (¬ho-shr-morph s₁ qeq lind (trunc≡∅⇒¬ho s₁ lind teq)) ell)
     hf ceq eeq with complLₛ nmx | inspect complLₛ nmx
     hf ceq eeq | ∅ | [ nceq ] with complLₛ s
     hf ceq () | ∅ | [ nceq ] | ∅
     hf refl refl | ∅ | [ nceq ] | ¬∅ x = ⊥-elim ((del⇒¬ho s₁ lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
     hf ceq eeq | ¬∅ ncs | [ nceq ] with complLₛ s
     hf ceq () | ¬∅ ncs | [ nceq ] | ∅
     hf refl refl | ¬∅ ncs | [ nceq ] | ¬∅ x = cong (λ z → (shrink ls x) ∂ z) r where
       r = shrink-repl-comm s₁ lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl {cs} ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] = hf ceq eeq where
    hf : (complLₛ (s ←∂→ nmx) ≡ ¬∅ cs) → (complLₛ s ≡ ∅) → shrink (ls ∂ replLL rs lind ell) cs ≡
                                                             replLL (shrink rs q)
                                                             (¬ho-shr-morph s₁ qeq lind (trunc≡∅⇒¬ho s₁ lind teq)) ell
    hf ceq eeq with complLₛ nmx | inspect complLₛ nmx | complLₛ s
    hf () refl | ∅ | [ nceq ] | ∅
    hf refl refl | ¬∅ ncs | [ nceq ] | ∅ = shrink-repl-comm s₁ lind qeq teq deq nceq
    hf ceq () | ncs | [ nceq ] | ¬∅ x

 
  
  
  shrink-repl≡∅ : ∀{i u ll ell pll x trs} → (s : SetLL ll) → (lind : IndexLL {i} {u} pll ll)
          → (eq : complLₛ s ≡ ¬∅ x)
          → (teq : truncSetLL s lind ≡ ¬∅ trs)
          → complLₛ trs ≡ ∅
          → ∀ vs → complLₛ vs ≡ ∅      -- contruct trs ≡ contruct vs ≡ ↓
          → ∀{cs}
          → let mx = replacePartOf s to vs at lind in
          complLₛ mx ≡ ¬∅ cs
          → (shrink (replLL ll lind ell) cs) ≡ shrink ll x
  shrink-repl≡∅ ↓ lind () teq cteq vs cveq cmeq
  shrink-repl≡∅ (s ←∧) ↓ eq teq cteq vs cveq cmeq with complLₛ mx where
    mx = replacePartOf s to vs at ↓
  shrink-repl≡∅ (s ←∧) ↓ eq teq cteq vs refl () | .∅
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s | inspect complLₛ s where
    mx = replacePartOf s to vs at lind
  shrink-repl≡∅ (s ←∧) (lind ←∧) refl teq cteq vs cveq refl | ∅ | [ icmeq ] | ∅ | [ ieq ] = refl
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s lind ieq teq cteq vs
  shrink-repl≡∅ (s ←∧) (lind ←∧) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj3 , proj4 with complLₛ (replacePartOf s to vs at lind)
  shrink-repl≡∅ (s ←∧) (lind ←∧) eq teq cteq vs cveq cmeq | ∅ | [ refl ] | ¬∅ x | [ ieq ] | proj3 , () | .∅
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | proj₃ , proj4 with complLₛ s
  shrink-repl≡∅ (s ←∧) (lind ←∧) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ refl ] | proj₃ , () | .∅
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ ics | [ ieq ] = cong (λ z → z ∧  shrink rll (fillAllLower rll)) is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ (s ←∧) (∧→ lind) eq () cteq vs cveq cmeq
  shrink-repl≡∅ (∧→ s) ↓ eq teq cteq vs cveq cmeq with complLₛ mx where
    mx = replacePartOf s to vs at ↓
  shrink-repl≡∅ (∧→ s) ↓ eq teq cteq vs () refl | .(¬∅ _)
  shrink-repl≡∅ (∧→ s) (lind ←∧) eq () cteq vs cveq cmeq
  shrink-repl≡∅ {ll = lll ∧ rll} (∧→ s) (∧→ lind) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s | inspect complLₛ s where
    mx = replacePartOf s to vs at lind
  shrink-repl≡∅ {ll = lll ∧ rll} (∧→ s) (∧→ lind) refl teq cteq vs cveq refl | ∅ | e | ∅ | w = refl
  shrink-repl≡∅ {ll = lll ∧ rll} (∧→ s) (∧→ lind) eq teq cteq vs cveq refl | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s lind ieq teq cteq vs
  shrink-repl≡∅ {ll = lll ∧ rll} (∧→ s) (∧→ lind) eq teq cteq vs cveq refl | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj₃ , proj4 with complLₛ (replacePartOf s to vs at lind)
  shrink-repl≡∅ {ll = lll ∧ rll} (∧→ s) (∧→ lind) eq teq cteq vs cveq refl | ∅ | [ () ] | ¬∅ x | [ ieq ] | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∧ rll} (∧→ s) (∧→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∧ rll} (∧→ s) (∧→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | proj₃ , proj4 with complLₛ s
  shrink-repl≡∅ {ll = lll ∧ rll} (∧→ s) (∧→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ () ] | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∧ rll} (∧→ s) (∧→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] = cong (λ z → (shrink lll (fillAllLower lll)) ∧ z) is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ (s ←∧→ s₁) ↓ eq teq cteq vs cveq cmeq with complLₛ vs
  shrink-repl≡∅ (s ←∧→ s₁) ↓ eq teq cteq vs () refl | .(¬∅ _)
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s | inspect complLₛ s where
    mx = replacePartOf s to vs at lind
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ∅ | [ ieq ] with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) eq teq cteq vs cveq () | ∅ | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) refl teq cteq vs cveq refl | ∅ | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x = refl
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s lind ieq teq cteq vs
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj₃ , proj4 with complLₛ (replacePartOf s to vs at lind)
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) eq teq cteq vs cveq cmeq | ∅ | [ refl ] | ¬∅ x | [ ieq ] | proj₃ , () | .∅
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) () teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x | proj₃ , proj4 with complLₛ s
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ () ] | ¬∅ x | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] | ∅ = is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ {u = _} {lll ∧ rll} (s ←∧→ s₁) (lind ←∧) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x₁ | [ ieq ] | ¬∅ x = cong (λ z → z ∧  shrink rll x) is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s₁ | inspect complLₛ s₁ where
    mx = replacePartOf s₁ to vs at lind
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ∅ | [ ieq ] with complLₛ s
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) eq teq cteq vs cveq () | ∅ | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) refl teq cteq vs cveq refl | ∅ | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x = refl
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s₁ lind ieq teq cteq vs
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj₃ , proj4 with complLₛ (replacePartOf s₁ to vs at lind)
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) eq teq cteq vs cveq cmeq | ∅ | [ refl ] | ¬∅ x | [ ieq ] | proj₃ , () | .∅
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with complLₛ s
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) () teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s₁ lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x | proj₃ , proj4 with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ () ] | ¬∅ x | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] with complLₛ s
  shrink-repl≡∅ {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] | ∅ = is where
    is = shrink-repl≡∅ s₁ lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ {u = _} {lll ∧ rll} (s ←∧→ s₁) (∧→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x₁ | [ ieq ] | ¬∅ x = cong (λ z → (shrink lll x) ∧ z) is where
    is = shrink-repl≡∅ s₁ lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ (s ←∨) ↓ eq teq cteq vs cveq cmeq with complLₛ mx where
    mx = replacePartOf s to vs at ↓
  shrink-repl≡∅ (s ←∨) ↓ eq teq cteq vs refl () | .∅
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s | inspect complLₛ s where
    mx = replacePartOf s to vs at lind
  shrink-repl≡∅ (s ←∨) (lind ←∨) refl teq cteq vs cveq refl | ∅ | [ icmeq ] | ∅ | [ ieq ] = refl
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s lind ieq teq cteq vs
  shrink-repl≡∅ (s ←∨) (lind ←∨) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj3 , proj4 with complLₛ (replacePartOf s to vs at lind)
  shrink-repl≡∅ (s ←∨) (lind ←∨) eq teq cteq vs cveq cmeq | ∅ | [ refl ] | ¬∅ x | [ ieq ] | proj3 , () | .∅
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | proj₃ , proj4 with complLₛ s
  shrink-repl≡∅ (s ←∨) (lind ←∨) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ refl ] | proj₃ , () | .∅
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ ics | [ ieq ] = cong (λ z → z ∨  shrink rll (fillAllLower rll)) is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ (s ←∨) (∨→ lind) eq () cteq vs cveq cmeq
  shrink-repl≡∅ (∨→ s) ↓ eq teq cteq vs cveq cmeq with complLₛ mx where
    mx = replacePartOf s to vs at ↓
  shrink-repl≡∅ (∨→ s) ↓ eq teq cteq vs () refl | .(¬∅ _)
  shrink-repl≡∅ (∨→ s) (lind ←∨) eq () cteq vs cveq cmeq
  shrink-repl≡∅ {ll = lll ∨ rll} (∨→ s) (∨→ lind) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s | inspect complLₛ s where
    mx = replacePartOf s to vs at lind
  shrink-repl≡∅ {ll = lll ∨ rll} (∨→ s) (∨→ lind) refl teq cteq vs cveq refl | ∅ | e | ∅ | w = refl
  shrink-repl≡∅ {ll = lll ∨ rll} (∨→ s) (∨→ lind) eq teq cteq vs cveq refl | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s lind ieq teq cteq vs
  shrink-repl≡∅ {ll = lll ∨ rll} (∨→ s) (∨→ lind) eq teq cteq vs cveq refl | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj₃ , proj4 with complLₛ (replacePartOf s to vs at lind)
  shrink-repl≡∅ {ll = lll ∨ rll} (∨→ s) (∨→ lind) eq teq cteq vs cveq refl | ∅ | [ () ] | ¬∅ x | [ ieq ] | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∨ rll} (∨→ s) (∨→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∨ rll} (∨→ s) (∨→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | proj₃ , proj4 with complLₛ s
  shrink-repl≡∅ {ll = lll ∨ rll} (∨→ s) (∨→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ () ] | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∨ rll} (∨→ s) (∨→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] = cong (λ z → (shrink lll (fillAllLower lll)) ∨ z) is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ (s ←∨→ s₁) ↓ eq teq cteq vs cveq cmeq with complLₛ vs
  shrink-repl≡∅ (s ←∨→ s₁) ↓ eq teq cteq vs () refl | .(¬∅ _)
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s | inspect complLₛ s where
    mx = replacePartOf s to vs at lind
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ∅ | [ ieq ] with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) eq teq cteq vs cveq () | ∅ | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) refl teq cteq vs cveq refl | ∅ | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x = refl
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s lind ieq teq cteq vs
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj₃ , proj4 with complLₛ (replacePartOf s to vs at lind)
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) eq teq cteq vs cveq cmeq | ∅ | [ refl ] | ¬∅ x | [ ieq ] | proj₃ , () | .∅
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) () teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x | proj₃ , proj4 with complLₛ s
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ () ] | ¬∅ x | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] | ∅ = is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ {u = _} {lll ∨ rll} (s ←∨→ s₁) (lind ←∨) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x₁ | [ ieq ] | ¬∅ x = cong (λ z → z ∨  shrink rll x) is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s₁ | inspect complLₛ s₁ where
    mx = replacePartOf s₁ to vs at lind
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ∅ | [ ieq ] with complLₛ s
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) eq teq cteq vs cveq () | ∅ | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) refl teq cteq vs cveq refl | ∅ | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x = refl
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s₁ lind ieq teq cteq vs
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj₃ , proj4 with complLₛ (replacePartOf s₁ to vs at lind)
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) eq teq cteq vs cveq cmeq | ∅ | [ refl ] | ¬∅ x | [ ieq ] | proj₃ , () | .∅
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with complLₛ s
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) () teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s₁ lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x | proj₃ , proj4 with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ () ] | ¬∅ x | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] with complLₛ s
  shrink-repl≡∅ {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] | ∅ = is where
    is = shrink-repl≡∅ s₁ lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ {u = _} {lll ∨ rll} (s ←∨→ s₁) (∨→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x₁ | [ ieq ] | ¬∅ x = cong (λ z → (shrink lll x) ∨ z) is where
    is = shrink-repl≡∅ s₁ lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ (s ←∂) ↓ eq teq cteq vs cveq cmeq with complLₛ mx where
    mx = replacePartOf s to vs at ↓
  shrink-repl≡∅ (s ←∂) ↓ eq teq cteq vs refl () | .∅
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s | inspect complLₛ s where
    mx = replacePartOf s to vs at lind
  shrink-repl≡∅ (s ←∂) (lind ←∂) refl teq cteq vs cveq refl | ∅ | [ icmeq ] | ∅ | [ ieq ] = refl
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s lind ieq teq cteq vs
  shrink-repl≡∅ (s ←∂) (lind ←∂) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj3 , proj4 with complLₛ (replacePartOf s to vs at lind)
  shrink-repl≡∅ (s ←∂) (lind ←∂) eq teq cteq vs cveq cmeq | ∅ | [ refl ] | ¬∅ x | [ ieq ] | proj3 , () | .∅
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | proj₃ , proj4 with complLₛ s
  shrink-repl≡∅ (s ←∂) (lind ←∂) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ refl ] | proj₃ , () | .∅
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ ics | [ ieq ] = cong (λ z → z ∂  shrink rll (fillAllLower rll)) is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ (s ←∂) (∂→ lind) eq () cteq vs cveq cmeq
  shrink-repl≡∅ (∂→ s) ↓ eq teq cteq vs cveq cmeq with complLₛ mx where
    mx = replacePartOf s to vs at ↓
  shrink-repl≡∅ (∂→ s) ↓ eq teq cteq vs () refl | .(¬∅ _)
  shrink-repl≡∅ (∂→ s) (lind ←∂) eq () cteq vs cveq cmeq
  shrink-repl≡∅ {ll = lll ∂ rll} (∂→ s) (∂→ lind) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s | inspect complLₛ s where
    mx = replacePartOf s to vs at lind
  shrink-repl≡∅ {ll = lll ∂ rll} (∂→ s) (∂→ lind) refl teq cteq vs cveq refl | ∅ | e | ∅ | w = refl
  shrink-repl≡∅ {ll = lll ∂ rll} (∂→ s) (∂→ lind) eq teq cteq vs cveq refl | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s lind ieq teq cteq vs
  shrink-repl≡∅ {ll = lll ∂ rll} (∂→ s) (∂→ lind) eq teq cteq vs cveq refl | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj₃ , proj4 with complLₛ (replacePartOf s to vs at lind)
  shrink-repl≡∅ {ll = lll ∂ rll} (∂→ s) (∂→ lind) eq teq cteq vs cveq refl | ∅ | [ () ] | ¬∅ x | [ ieq ] | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∂ rll} (∂→ s) (∂→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∂ rll} (∂→ s) (∂→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | proj₃ , proj4 with complLₛ s
  shrink-repl≡∅ {ll = lll ∂ rll} (∂→ s) (∂→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ () ] | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∂ rll} (∂→ s) (∂→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] = cong (λ z → (shrink lll (fillAllLower lll)) ∂ z) is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ (s ←∂→ s₁) ↓ eq teq cteq vs cveq cmeq with complLₛ vs
  shrink-repl≡∅ (s ←∂→ s₁) ↓ eq teq cteq vs () refl | .(¬∅ _)
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s | inspect complLₛ s where
    mx = replacePartOf s to vs at lind
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ∅ | [ ieq ] with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) eq teq cteq vs cveq () | ∅ | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) refl teq cteq vs cveq refl | ∅ | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x = refl
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s lind ieq teq cteq vs
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj₃ , proj4 with complLₛ (replacePartOf s to vs at lind)
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) eq teq cteq vs cveq cmeq | ∅ | [ refl ] | ¬∅ x | [ ieq ] | proj₃ , () | .∅
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) () teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x | proj₃ , proj4 with complLₛ s
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ () ] | ¬∅ x | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] | ∅ = is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ {u = _} {lll ∂ rll} (s ←∂→ s₁) (lind ←∂) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x₁ | [ ieq ] | ¬∅ x = cong (λ z → z ∂  shrink rll x) is where
    is = shrink-repl≡∅ s lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) eq teq cteq vs cveq cmeq with complLₛ mx | inspect complLₛ mx | complLₛ s₁ | inspect complLₛ s₁ where
    mx = replacePartOf s₁ to vs at lind
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ∅ | [ ieq ] with complLₛ s
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) eq teq cteq vs cveq () | ∅ | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) refl teq cteq vs cveq refl | ∅ | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x = refl
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] with compl≡¬∅⇒replace-compl≡¬∅ s₁ lind ieq teq cteq vs
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) eq teq cteq vs cveq cmeq | ∅ | [ icmeq ] | ¬∅ x | [ ieq ] | proj₃ , proj4 with complLₛ (replacePartOf s₁ to vs at lind)
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) eq teq cteq vs cveq cmeq | ∅ | [ refl ] | ¬∅ x | [ ieq ] | proj₃ , () | .∅
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] with complLₛ s
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) () teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ∅
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x with vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s₁ lind vs cveq icmeq
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ ieq ] | ¬∅ x | proj₃ , proj4 with complLₛ s₁
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ∅ | [ () ] | ¬∅ x | proj₃ , refl | .(¬∅ proj₃)
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) eq teq cteq vs cveq cmeq | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] with complLₛ s
  shrink-repl≡∅ {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x | [ ieq ] | ∅ = is where
    is = shrink-repl≡∅ s₁ lind ieq teq cteq vs cveq icmeq
  shrink-repl≡∅ {u = _} {lll ∂ rll} (s ←∂→ s₁) (∂→ lind) refl teq cteq vs cveq refl | ¬∅ icms | [ icmeq ] | ¬∅ x₁ | [ ieq ] | ¬∅ x = cong (λ z → (shrink lll x) ∂ z) is where
    is = shrink-repl≡∅ s₁ lind ieq teq cteq vs cveq icmeq
  
  
  
   
  ho-shrink-repl-comm : ∀{i u ll ell pll x trs cs1 cts1} → (s : SetLL ll) → (lind : IndexLL {i} {u} pll ll)
        → (eq : complLₛ s ≡ ¬∅ x)
        → (teq : truncSetLL s lind ≡ ¬∅ trs)
        → (ceqi : complLₛ trs ≡ ¬∅ cs1)
        → ∀{ts1}
        → (ceqo  : complLₛ ts1 ≡ ¬∅ cts1)
        → ∀{mx cs}
        → (mreplacePartOf ¬∅ s to (¬∅ ts1) at lind) ≡ ¬∅ mx
        → (ceqi1 : complLₛ mx ≡ ¬∅ cs)
        → (replLL (shrink ll x) (ho-shr-morph s eq lind (sym teq) ceqi) (shrink ell cts1)) ≡ (shrink (replLL ll lind ell) cs)
  ho-shrink-repl-comm ↓ lind () teq ceqi ceqo meq ceqi1
  ho-shrink-repl-comm q@(s ←∧) ↓ eq refl ceqi ceqo refl ceqi1 with complLₛ q
  ho-shrink-repl-comm (s ←∧) ↓ refl refl refl {ts1} ceqo refl ceqi1 | .(¬∅ _) with complLₛ ts1
  ho-shrink-repl-comm (s ←∧) ↓ refl refl refl {ts1} refl refl refl | .(¬∅ _) | .(¬∅ _) = refl
  ho-shrink-repl-comm {ll = lll ∧ rll} (s ←∧) (lind ←∧) eq teq ceqi ceqo meq ceqi1 with complLₛ s | inspect complLₛ s
  ho-shrink-repl-comm {ll = lll ∧ rll} {trs = trs} (s ←∧) (lind ←∧) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eqq lind (sym teq)
  ho-shrink-repl-comm {trs = trs} (s ←∧) (lind ←∧) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∧ rll} (s ←∧) (lind ←∧) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s to ts1 at lind
  ho-shrink-repl-comm {ll = lll ∧ rll} {ell} (s ←∧) (lind ←∧) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL lll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∧ rll} {ell} (s ←∧) (lind ←∧) refl teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∧ rll} (s ←∧) (lind ←∧) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] = cong (λ z → z ∧ _) is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm (s ←∧) (∧→ lind) eq () ceqi ceqo meq ceqi1
  ho-shrink-repl-comm q@(∧→ s) ↓ eq refl ceqi ceqo refl ceqi1 with complLₛ q
  ho-shrink-repl-comm (∧→ s) ↓ refl refl refl {ts1} ceqo refl ceqi1 | .(¬∅ _) with complLₛ ts1
  ho-shrink-repl-comm (∧→ s) ↓ refl refl refl {ts1} refl refl refl | .(¬∅ _) | .(¬∅ _) = refl
  ho-shrink-repl-comm (∧→ s) (lind ←∧) eq () ceqi ceqo meq ceqi1
  ho-shrink-repl-comm {ll = lll ∧ rll} (∧→ s) (∧→ lind) eq teq ceqi ceqo meq ceqi1 with complLₛ s | inspect complLₛ s
  ho-shrink-repl-comm {ll = lll ∧ rll} {trs = trs} (∧→ s) (∧→ lind) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eqq lind (sym teq)
  ho-shrink-repl-comm {u = _} {lll ∧ rll} {trs = trs} (∧→ s) (∧→ lind) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∧ rll} (∧→ s) (∧→ lind) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s to ts1 at lind
  ho-shrink-repl-comm {u = _} {lll ∧ rll} {ell} (∧→ s) (∧→ lind) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL rll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∧ rll} {ell} (∧→ s) (∧→ lind) refl teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∧ rll} (∧→ s) (∧→ lind) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] = cong (λ z → _ ∧ z) is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm (s ←∧→ s₁) ↓ eq refl ceqi ceqo refl ceqi1 with complLₛ (s ←∧→ s₁)
  ho-shrink-repl-comm (s ←∧→ s₁) ↓ refl refl refl {ts1} ceqo refl ceqi1 | .(¬∅ _) with complLₛ ts1
  ho-shrink-repl-comm (s ←∧→ s₁) ↓ refl refl refl {ts1} refl refl refl | .(¬∅ _) | .(¬∅ _) = refl
  ho-shrink-repl-comm {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) eq teq ceqi ceqo meq ceqi1 with complLₛ s | inspect complLₛ s
  ho-shrink-repl-comm {ll = lll ∧ rll} {trs = trs} (s ←∧→ s₁) (lind ←∧) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eqq lind (sym teq)
  ho-shrink-repl-comm {u = _} {lll ∧ rll} {trs = trs} (s ←∧→ s₁) (lind ←∧) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∧ rll} (s ←∧→ s₁) (lind ←∧) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s to ts1 at lind
  ho-shrink-repl-comm {u = _} {lll ∧ rll} {ell = ell} (s ←∧→ s₁) (lind ←∧) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL lll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∧ rll} {ell} (s ←∧→ s₁) (lind ←∧) eq teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∧ rll} (s ←∧→ s₁) (lind ←∧) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] with complLₛ s₁
  ho-shrink-repl-comm {u = _} {lll ∧ rll} (s ←∧→ s₁) (lind ←∧) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] | ∅ = is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm {u = _} {lll ∧ rll} (s ←∧→ s₁) (lind ←∧) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₂ | [ eqq ] | ¬∅ x₁ | [ nmeq ] | ¬∅ x = cong (λ z → z ∧ _) is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) eq teq ceqi ceqo meq ceqi1 with complLₛ s₁ | inspect complLₛ s₁
  ho-shrink-repl-comm {ll = lll ∧ rll} {trs = trs} (s ←∧→ s₁) (∧→ lind) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s₁ eqq lind (sym teq)
  ho-shrink-repl-comm {u = _} {lll ∧ rll} {trs = trs} (s ←∧→ s₁) (∧→ lind) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∧ rll} (s ←∧→ s₁) (∧→ lind) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s₁ to ts1 at lind
  ho-shrink-repl-comm {u = _} {lll ∧ rll} {ell = ell} (s ←∧→ s₁) (∧→ lind) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s₁ to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL rll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s₁ lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∧ rll} {ell} (s ←∧→ s₁) (∧→ lind) eq teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∧ rll} (s ←∧→ s₁) (∧→ lind) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] with complLₛ s
  ho-shrink-repl-comm {u = _} {lll ∧ rll} (s ←∧→ s₁) (∧→ lind) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] | ∅ = is where
    is = ho-shrink-repl-comm s₁ lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm {u = _} {lll ∧ rll} (s ←∧→ s₁) (∧→ lind) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₂ | [ eqq ] | ¬∅ x₁ | [ nmeq ] | ¬∅ x = cong (λ z → _ ∧ z) is where
    is = ho-shrink-repl-comm s₁ lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm q@(s ←∨) ↓ eq refl ceqi ceqo refl ceqi1 with complLₛ q
  ho-shrink-repl-comm (s ←∨) ↓ refl refl refl {ts1} ceqo refl ceqi1 | .(¬∅ _) with complLₛ ts1
  ho-shrink-repl-comm (s ←∨) ↓ refl refl refl {ts1} refl refl refl | .(¬∅ _) | .(¬∅ _) = refl
  ho-shrink-repl-comm {ll = lll ∨ rll} (s ←∨) (lind ←∨) eq teq ceqi ceqo meq ceqi1 with complLₛ s | inspect complLₛ s
  ho-shrink-repl-comm {ll = lll ∨ rll} {trs = trs} (s ←∨) (lind ←∨) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eqq lind (sym teq)
  ho-shrink-repl-comm {trs = trs} (s ←∨) (lind ←∨) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∨ rll} (s ←∨) (lind ←∨) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s to ts1 at lind
  ho-shrink-repl-comm {ll = lll ∨ rll} {ell} (s ←∨) (lind ←∨) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL lll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∨ rll} {ell} (s ←∨) (lind ←∨) refl teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∨ rll} (s ←∨) (lind ←∨) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] = cong (λ z → z ∨ _) is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm (s ←∨) (∨→ lind) eq () ceqi ceqo meq ceqi1
  ho-shrink-repl-comm q@(∨→ s) ↓ eq refl ceqi ceqo refl ceqi1 with complLₛ q
  ho-shrink-repl-comm (∨→ s) ↓ refl refl refl {ts1} ceqo refl ceqi1 | .(¬∅ _) with complLₛ ts1
  ho-shrink-repl-comm (∨→ s) ↓ refl refl refl {ts1} refl refl refl | .(¬∅ _) | .(¬∅ _) = refl
  ho-shrink-repl-comm (∨→ s) (lind ←∨) eq () ceqi ceqo meq ceqi1
  ho-shrink-repl-comm {ll = lll ∨ rll} (∨→ s) (∨→ lind) eq teq ceqi ceqo meq ceqi1 with complLₛ s | inspect complLₛ s
  ho-shrink-repl-comm {ll = lll ∨ rll} {trs = trs} (∨→ s) (∨→ lind) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eqq lind (sym teq)
  ho-shrink-repl-comm {u = _} {lll ∨ rll} {trs = trs} (∨→ s) (∨→ lind) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∨ rll} (∨→ s) (∨→ lind) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s to ts1 at lind
  ho-shrink-repl-comm {u = _} {lll ∨ rll} {ell} (∨→ s) (∨→ lind) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL rll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∨ rll} {ell} (∨→ s) (∨→ lind) refl teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∨ rll} (∨→ s) (∨→ lind) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] = cong (λ z → _ ∨ z) is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm (s ←∨→ s₁) ↓ eq refl ceqi ceqo refl ceqi1 with complLₛ (s ←∨→ s₁)
  ho-shrink-repl-comm (s ←∨→ s₁) ↓ refl refl refl {ts1} ceqo refl ceqi1 | .(¬∅ _) with complLₛ ts1
  ho-shrink-repl-comm (s ←∨→ s₁) ↓ refl refl refl {ts1} refl refl refl | .(¬∅ _) | .(¬∅ _) = refl
  ho-shrink-repl-comm {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) eq teq ceqi ceqo meq ceqi1 with complLₛ s | inspect complLₛ s
  ho-shrink-repl-comm {ll = lll ∨ rll} {trs = trs} (s ←∨→ s₁) (lind ←∨) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eqq lind (sym teq)
  ho-shrink-repl-comm {u = _} {lll ∨ rll} {trs = trs} (s ←∨→ s₁) (lind ←∨) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∨ rll} (s ←∨→ s₁) (lind ←∨) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s to ts1 at lind
  ho-shrink-repl-comm {u = _} {lll ∨ rll} {ell = ell} (s ←∨→ s₁) (lind ←∨) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL lll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∨ rll} {ell} (s ←∨→ s₁) (lind ←∨) eq teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∨ rll} (s ←∨→ s₁) (lind ←∨) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] with complLₛ s₁
  ho-shrink-repl-comm {u = _} {lll ∨ rll} (s ←∨→ s₁) (lind ←∨) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] | ∅ = is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm {u = _} {lll ∨ rll} (s ←∨→ s₁) (lind ←∨) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₂ | [ eqq ] | ¬∅ x₁ | [ nmeq ] | ¬∅ x = cong (λ z → z ∨ _) is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) eq teq ceqi ceqo meq ceqi1 with complLₛ s₁ | inspect complLₛ s₁
  ho-shrink-repl-comm {ll = lll ∨ rll} {trs = trs} (s ←∨→ s₁) (∨→ lind) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s₁ eqq lind (sym teq)
  ho-shrink-repl-comm {u = _} {lll ∨ rll} {trs = trs} (s ←∨→ s₁) (∨→ lind) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∨ rll} (s ←∨→ s₁) (∨→ lind) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s₁ to ts1 at lind
  ho-shrink-repl-comm {u = _} {lll ∨ rll} {ell = ell} (s ←∨→ s₁) (∨→ lind) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s₁ to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL rll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s₁ lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∨ rll} {ell} (s ←∨→ s₁) (∨→ lind) eq teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∨ rll} (s ←∨→ s₁) (∨→ lind) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] with complLₛ s
  ho-shrink-repl-comm {u = _} {lll ∨ rll} (s ←∨→ s₁) (∨→ lind) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] | ∅ = is where
    is = ho-shrink-repl-comm s₁ lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm {u = _} {lll ∨ rll} (s ←∨→ s₁) (∨→ lind) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₂ | [ eqq ] | ¬∅ x₁ | [ nmeq ] | ¬∅ x = cong (λ z → _ ∨ z) is where
    is = ho-shrink-repl-comm s₁ lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm q@(s ←∂) ↓ eq refl ceqi ceqo refl ceqi1 with complLₛ q
  ho-shrink-repl-comm (s ←∂) ↓ refl refl refl {ts1} ceqo refl ceqi1 | .(¬∅ _) with complLₛ ts1
  ho-shrink-repl-comm (s ←∂) ↓ refl refl refl {ts1} refl refl refl | .(¬∅ _) | .(¬∅ _) = refl
  ho-shrink-repl-comm {ll = lll ∂ rll} (s ←∂) (lind ←∂) eq teq ceqi ceqo meq ceqi1 with complLₛ s | inspect complLₛ s
  ho-shrink-repl-comm {ll = lll ∂ rll} {trs = trs} (s ←∂) (lind ←∂) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eqq lind (sym teq)
  ho-shrink-repl-comm {trs = trs} (s ←∂) (lind ←∂) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∂ rll} (s ←∂) (lind ←∂) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s to ts1 at lind
  ho-shrink-repl-comm {ll = lll ∂ rll} {ell} (s ←∂) (lind ←∂) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL lll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∂ rll} {ell} (s ←∂) (lind ←∂) refl teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∂ rll} (s ←∂) (lind ←∂) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] = cong (λ z → z ∂ _) is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm (s ←∂) (∂→ lind) eq () ceqi ceqo meq ceqi1
  ho-shrink-repl-comm q@(∂→ s) ↓ eq refl ceqi ceqo refl ceqi1 with complLₛ q
  ho-shrink-repl-comm (∂→ s) ↓ refl refl refl {ts1} ceqo refl ceqi1 | .(¬∅ _) with complLₛ ts1
  ho-shrink-repl-comm (∂→ s) ↓ refl refl refl {ts1} refl refl refl | .(¬∅ _) | .(¬∅ _) = refl
  ho-shrink-repl-comm (∂→ s) (lind ←∂) eq () ceqi ceqo meq ceqi1
  ho-shrink-repl-comm {ll = lll ∂ rll} (∂→ s) (∂→ lind) eq teq ceqi ceqo meq ceqi1 with complLₛ s | inspect complLₛ s
  ho-shrink-repl-comm {ll = lll ∂ rll} {trs = trs} (∂→ s) (∂→ lind) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eqq lind (sym teq)
  ho-shrink-repl-comm {u = _} {lll ∂ rll} {trs = trs} (∂→ s) (∂→ lind) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∂ rll} (∂→ s) (∂→ lind) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s to ts1 at lind
  ho-shrink-repl-comm {u = _} {lll ∂ rll} {ell} (∂→ s) (∂→ lind) refl teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL rll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∂ rll} {ell} (∂→ s) (∂→ lind) refl teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∂ rll} (∂→ s) (∂→ lind) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] = cong (λ z → _ ∂ z) is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm (s ←∂→ s₁) ↓ eq refl ceqi ceqo refl ceqi1 with complLₛ (s ←∂→ s₁)
  ho-shrink-repl-comm (s ←∂→ s₁) ↓ refl refl refl {ts1} ceqo refl ceqi1 | .(¬∅ _) with complLₛ ts1
  ho-shrink-repl-comm (s ←∂→ s₁) ↓ refl refl refl {ts1} refl refl refl | .(¬∅ _) | .(¬∅ _) = refl
  ho-shrink-repl-comm {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) eq teq ceqi ceqo meq ceqi1 with complLₛ s | inspect complLₛ s
  ho-shrink-repl-comm {ll = lll ∂ rll} {trs = trs} (s ←∂→ s₁) (lind ←∂) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s eqq lind (sym teq)
  ho-shrink-repl-comm {u = _} {lll ∂ rll} {trs = trs} (s ←∂→ s₁) (lind ←∂) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∂ rll} (s ←∂→ s₁) (lind ←∂) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s to ts1 at lind
  ho-shrink-repl-comm {u = _} {lll ∂ rll} {ell = ell} (s ←∂→ s₁) (lind ←∂) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL lll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∂ rll} {ell} (s ←∂→ s₁) (lind ←∂) eq teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∂ rll} (s ←∂→ s₁) (lind ←∂) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] with complLₛ s₁
  ho-shrink-repl-comm {u = _} {lll ∂ rll} (s ←∂→ s₁) (lind ←∂) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] | ∅ = is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm {u = _} {lll ∂ rll} (s ←∂→ s₁) (lind ←∂) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₂ | [ eqq ] | ¬∅ x₁ | [ nmeq ] | ¬∅ x = cong (λ z → z ∂ _) is where
    is = ho-shrink-repl-comm s lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) eq teq ceqi ceqo meq ceqi1 with complLₛ s₁ | inspect complLₛ s₁
  ho-shrink-repl-comm {ll = lll ∂ rll} {trs = trs} (s ←∂→ s₁) (∂→ lind) eq teq ceqi ceqo meq ceqi1 | ∅ | [ eqq ] with complLₛ trs | r where
    r = compl≡∅⇒compltr≡∅ s₁ eqq lind (sym teq)
  ho-shrink-repl-comm {u = _} {lll ∂ rll} {trs = trs} (s ←∂→ s₁) (∂→ lind) eq teq () ceqo meq ceqi1 | ∅ | [ eqq ] | .∅ | refl
  ho-shrink-repl-comm {ll = lll ∂ rll} (s ←∂→ s₁) (∂→ lind) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] with complLₛ nmx | inspect complLₛ nmx where
    nmx = replacePartOf s₁ to ts1 at lind
  ho-shrink-repl-comm {u = _} {lll ∂ rll} {ell = ell} (s ←∂→ s₁) (∂→ lind) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] with complLₛ ts1 | ct where
      m = replacePartOf s₁ to ts1 at lind
      mind = subst (λ z → IndexLL z (replLL rll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
      ct = compl≡∅⇒compltr≡∅ m nmeq mind (sym (tr-repl⇒id s₁ lind ts1))
  ho-shrink-repl-comm {u = _} {lll ∂ rll} {ell} (s ←∂→ s₁) (∂→ lind) eq teq ceqi {ts1} () refl ceqi1 | ¬∅ x | [ eqq ] | ∅ | [ nmeq ] | .∅ | refl
  ho-shrink-repl-comm {u = _} {lll ∂ rll} (s ←∂→ s₁) (∂→ lind) eq teq ceqi {ts1} ceqo refl ceqi1 | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] with complLₛ s
  ho-shrink-repl-comm {u = _} {lll ∂ rll} (s ←∂→ s₁) (∂→ lind) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₁ | [ eqq ] | ¬∅ x | [ nmeq ] | ∅ = is where
    is = ho-shrink-repl-comm s₁ lind eqq teq ceqi ceqo refl nmeq
  ho-shrink-repl-comm {u = _} {lll ∂ rll} (s ←∂→ s₁) (∂→ lind) refl teq ceqi {ts1} ceqo refl refl | ¬∅ x₂ | [ eqq ] | ¬∅ x₁ | [ nmeq ] | ¬∅ x = cong (λ z → _ ∂ z) is where
    is = ho-shrink-repl-comm s₁ lind eqq teq ceqi ceqo refl nmeq


 
  
  
  




  fltr : ∀{i u rll ll} → LLTr {i} {u} rll ll → Σ (LinLogic i) (λ z → LLTr z ll)
  fltr {ll = ll} I = ll , I
  fltr {ll = l ∂ r} (∂c ltr) = (r ∂ l) , ∂c I
  fltr {ll = l ∧ r} (∧c ltr) = (r ∧ l) , ∧c I
  fltr {ll = l ∨ r} (∨c ltr) = (r ∨ l) , ∨c I
  fltr {ll = ((l₁ ∧ l₂) ∧ r)} (∧∧d ltr) = (l₁ ∧ (l₂ ∧ r)) , ∧∧d I
  fltr {ll = l₁ ∧ (l₂ ∧ r)} (¬∧∧d ltr) = ((l₁ ∧ l₂) ∧ r) , ¬∧∧d I
  fltr {ll = (l₁ ∨ l₂) ∨ r} (∨∨d ltr) = (l₁ ∨ (l₂ ∨ r)) , ∨∨d I
  fltr {ll = l₁ ∨ ( l₂ ∨ r)} (¬∨∨d ltr) = ((l₁ ∨ l₂) ∨ r) , ¬∨∨d I
  fltr {ll = (l₁ ∂ l₂) ∂ r} (∂∂d ltr) = (l₁ ∂ (l₂ ∂ r)) , ∂∂d I
  fltr {ll = l₁ ∂ (l₂ ∂ r)} (¬∂∂d ltr) = ((l₁ ∂ l₂) ∂ r) , ¬∂∂d I

-- ( shrink tran Irrelevance)
  data STrIr {i u rll} : ∀ {ll} → (s : SetLL {i} {u} ll) → LLTr rll ll → Set (lsuc u) where
    sti∧c : ∀{ll rl s ltr} → (¬ hitsAtLeastOnce s (↓ ←∧)) ⊎ (¬ hitsAtLeastOnce s (∧→ ↓)) → STrIr {ll = ll ∧ rl} s (∧c ltr)
    sti∨c : ∀{ll rl s ltr} → (¬ hitsAtLeastOnce s (↓ ←∨)) ⊎ (¬ hitsAtLeastOnce s (∨→ ↓)) → STrIr {ll = ll ∨ rl} s (∨c ltr)
    sti∂c : ∀{ll rl s ltr} → (¬ hitsAtLeastOnce s (↓ ←∂)) ⊎ (¬ hitsAtLeastOnce s (∂→ ↓)) → STrIr {ll = ll ∂ rl} s (∂c ltr)
    sti∧∧d : ∀{lll lrl rl s ltr} → ¬ hitsAtLeastOnce s ((↓ ←∧) ←∧) ⊎ (¬ hitsAtLeastOnce s ((∧→ ↓) ←∧) ⊎ ¬ hitsAtLeastOnce s (∧→ ↓))
             → STrIr {ll = (lll ∧ lrl) ∧ rl} s (∧∧d ltr)
    sti∨∨d : ∀{lll lrl rl s ltr} → ¬ hitsAtLeastOnce s ((↓ ←∨) ←∨) ⊎ (¬ hitsAtLeastOnce s ((∨→ ↓) ←∨) ⊎ ¬ hitsAtLeastOnce s (∨→ ↓) )
             → STrIr {ll = (lll ∨ lrl) ∨ rl} s (∨∨d ltr)
    sti∂∂d : ∀{lll lrl rl s ltr} → ¬ hitsAtLeastOnce s ((↓ ←∂) ←∂) ⊎ (¬ hitsAtLeastOnce s ((∂→ ↓) ←∂) ⊎ ¬ hitsAtLeastOnce s (∂→ ↓))
             → STrIr {ll = (lll ∂ lrl) ∂ rl} s (∂∂d ltr)
    sti¬∧∧d : ∀{rll rrl ll s ltr} → ¬ hitsAtLeastOnce s (↓ ←∧) ⊎ (¬ hitsAtLeastOnce s (∧→ (∧→ ↓)) ⊎ ¬ hitsAtLeastOnce s (∧→ (↓ ←∧)))
             → STrIr {ll = ll ∧ (rll ∧ rrl)} s (¬∧∧d ltr)
    sti¬∨∨d : ∀{rll rrl ll s ltr} → ¬ hitsAtLeastOnce s (↓ ←∨) ⊎ (¬ hitsAtLeastOnce s (∨→ (∨→ ↓)) ⊎ ¬ hitsAtLeastOnce s (∨→ (↓ ←∨)))
             → STrIr {ll = ll ∨ (rll ∨ rrl)} s (¬∨∨d ltr)
    sti¬∂∂d : ∀{rll rrl ll s ltr} → ¬ hitsAtLeastOnce s (↓ ←∂) ⊎ (¬ hitsAtLeastOnce s (∂→ (∂→ ↓)) ⊎ ¬ hitsAtLeastOnce s (∂→ (↓ ←∂)))
             → STrIr {ll = ll ∂ (rll ∂ rrl)} s (¬∂∂d ltr)




---- As long as ltr contains a point that does not belong to s.
  shr-tr-theorem : ∀{i u rll} → ∀ ll → (s : SetLL ll) → (ltr : LLTr {i} {u} rll ll)
        → STrIr s ltr → let fl = fltr ltr in shrink ll s ≡ shrink (proj₁ fl) (tran s (proj₂ fl))
  shr-tr-theorem (ll ∧ rl) ↓ .(∧c _) (sti∧c (inj₁ x)) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∧ rl) ↓ .(∧c _) (sti∧c (inj₂ y)) = ⊥-elim (y hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∧ rl) (s ←∧) .(∧c _) (sti∧c x) = refl
  shr-tr-theorem (ll ∧ rl) (∧→ s) .(∧c _) (sti∧c x) = refl
  shr-tr-theorem (ll ∧ rl) (↓ ←∧→ s₁) .(∧c _) (sti∧c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓))
  shr-tr-theorem (.(_ ∧ _) ∧ rl) ((s ←∧) ←∧→ s₁) .(∧c _) (sti∧c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∧↓))
  shr-tr-theorem (.(_ ∧ _) ∧ rl) ((∧→ s) ←∧→ s₁) .(∧c _) (sti∧c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∧→↓))
  shr-tr-theorem (.(_ ∧ _) ∧ rl) ((s ←∧→ s₁) ←∧→ s₂) .(∧c _) (sti∧c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem (.(_ ∨ _) ∧ rl) ((s ←∨) ←∧→ s₁) .(∧c _) (sti∧c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∨↓))
  shr-tr-theorem (.(_ ∨ _) ∧ rl) ((∨→ s) ←∧→ s₁) .(∧c _) (sti∧c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∨→↓))
  shr-tr-theorem (.(_ ∨ _) ∧ rl) ((s ←∨→ s₁) ←∧→ s₂) .(∧c _) (sti∧c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem (.(_ ∂ _) ∧ rl) ((s ←∂) ←∧→ s₁) .(∧c _) (sti∧c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∂↓))
  shr-tr-theorem (.(_ ∂ _) ∧ rl) ((∂→ s) ←∧→ s₁) .(∧c _) (sti∧c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∂→↓))
  shr-tr-theorem (.(_ ∂ _) ∧ rl) ((s ←∂→ s₁) ←∧→ s₂) .(∧c _) (sti∧c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∂→↓))
  shr-tr-theorem (ll ∧ rl) (s ←∧→ ↓) .(∧c _) (sti∧c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓))
  shr-tr-theorem (ll ∧ .(_ ∧ _)) (s ←∧→ (s1 ←∧)) .(∧c _) (sti∧c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∧↓))
  shr-tr-theorem (ll ∧ .(_ ∧ _)) (s ←∧→ (∧→ s1)) .(∧c _) (sti∧c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∧→↓))
  shr-tr-theorem (ll ∧ .(_ ∧ _)) (s ←∧→ (s1 ←∧→ s2)) .(∧c _) (sti∧c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem (ll ∧ .(_ ∨ _)) (s ←∧→ (s1 ←∨)) .(∧c _) (sti∧c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∨↓))
  shr-tr-theorem (ll ∧ .(_ ∨ _)) (s ←∧→ (∨→ s1)) .(∧c _) (sti∧c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∨→↓))
  shr-tr-theorem (ll ∧ .(_ ∨ _)) (s ←∧→ (s1 ←∨→ s2)) .(∧c _) (sti∧c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem (ll ∧ .(_ ∂ _)) (s ←∧→ (s1 ←∂)) .(∧c _) (sti∧c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∂↓))
  shr-tr-theorem (ll ∧ .(_ ∂ _)) (s ←∧→ (∂→ s1)) .(∧c _) (sti∧c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∂→↓))
  shr-tr-theorem (ll ∧ .(_ ∂ _)) (s ←∧→ (s1 ←∂→ s2)) .(∧c _) (sti∧c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∂→↓))
  shr-tr-theorem (ll ∨ rl) ↓ .(∨c _) (sti∨c (inj₁ x)) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∨ rl) ↓ .(∨c _) (sti∨c (inj₂ y)) = ⊥-elim (y hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∨ rl) (s ←∨) .(∨c _) (sti∨c x) = refl
  shr-tr-theorem (ll ∨ rl) (∨→ s) .(∨c _) (sti∨c x) = refl
  shr-tr-theorem (ll ∨ rl) (↓ ←∨→ s₁) .(∨c _) (sti∨c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓))
  shr-tr-theorem (.(_ ∧ _) ∨ rl) ((s ←∧) ←∨→ s₁) .(∨c _) (sti∨c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∧↓))
  shr-tr-theorem (.(_ ∧ _) ∨ rl) ((∧→ s) ←∨→ s₁) .(∨c _) (sti∨c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∧→↓))
  shr-tr-theorem (.(_ ∧ _) ∨ rl) ((s ←∧→ s₁) ←∨→ s₂) .(∨c _) (sti∨c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem (.(_ ∨ _) ∨ rl) ((s ←∨) ←∨→ s₁) .(∨c _) (sti∨c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∨↓))
  shr-tr-theorem (.(_ ∨ _) ∨ rl) ((∨→ s) ←∨→ s₁) .(∨c _) (sti∨c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∨→↓))
  shr-tr-theorem (.(_ ∨ _) ∨ rl) ((s ←∨→ s₁) ←∨→ s₂) .(∨c _) (sti∨c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem (.(_ ∂ _) ∨ rl) ((s ←∂) ←∨→ s₁) .(∨c _) (sti∨c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∂↓))
  shr-tr-theorem (.(_ ∂ _) ∨ rl) ((∂→ s) ←∨→ s₁) .(∨c _) (sti∨c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∂→↓))
  shr-tr-theorem (.(_ ∂ _) ∨ rl) ((s ←∂→ s₁) ←∨→ s₂) .(∨c _) (sti∨c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∂→↓))
  shr-tr-theorem (ll ∨ rl) (s ←∨→ ↓) .(∨c _) (sti∨c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓))
  shr-tr-theorem (ll ∨ .(_ ∧ _)) (s ←∨→ (s1 ←∧)) .(∨c _) (sti∨c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∧↓))
  shr-tr-theorem (ll ∨ .(_ ∧ _)) (s ←∨→ (∧→ s1)) .(∨c _) (sti∨c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∧→↓))
  shr-tr-theorem (ll ∨ .(_ ∧ _)) (s ←∨→ (s1 ←∧→ s2)) .(∨c _) (sti∨c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem (ll ∨ .(_ ∨ _)) (s ←∨→ (s1 ←∨)) .(∨c _) (sti∨c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∨↓))
  shr-tr-theorem (ll ∨ .(_ ∨ _)) (s ←∨→ (∨→ s1)) .(∨c _) (sti∨c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∨→↓))
  shr-tr-theorem (ll ∨ .(_ ∨ _)) (s ←∨→ (s1 ←∨→ s2)) .(∨c _) (sti∨c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem (ll ∨ .(_ ∂ _)) (s ←∨→ (s1 ←∂)) .(∨c _) (sti∨c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∂↓))
  shr-tr-theorem (ll ∨ .(_ ∂ _)) (s ←∨→ (∂→ s1)) .(∨c _) (sti∨c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∂→↓))
  shr-tr-theorem (ll ∨ .(_ ∂ _)) (s ←∨→ (s1 ←∂→ s2)) .(∨c _) (sti∨c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∂→↓))
  shr-tr-theorem (ll ∂ rl) ↓ .(∂c _) (sti∂c (inj₁ x)) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∂ rl) ↓ .(∂c _) (sti∂c (inj₂ y)) = ⊥-elim (y hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∂ rl) (s ←∂) .(∂c _) (sti∂c x) = refl
  shr-tr-theorem (ll ∂ rl) (∂→ s) .(∂c _) (sti∂c x) = refl
  shr-tr-theorem (ll ∂ rl) (↓ ←∂→ s₁) .(∂c _) (sti∂c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓))
  shr-tr-theorem (.(_ ∧ _) ∂ rl) ((s ←∧) ←∂→ s₁) .(∂c _) (sti∂c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∧↓))
  shr-tr-theorem (.(_ ∧ _) ∂ rl) ((∧→ s) ←∂→ s₁) .(∂c _) (sti∂c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∧→↓))
  shr-tr-theorem (.(_ ∧ _) ∂ rl) ((s ←∧→ s₁) ←∂→ s₂) .(∂c _) (sti∂c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem (.(_ ∨ _) ∂ rl) ((s ←∨) ←∂→ s₁) .(∂c _) (sti∂c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∨↓))
  shr-tr-theorem (.(_ ∨ _) ∂ rl) ((∨→ s) ←∂→ s₁) .(∂c _) (sti∂c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∨→↓))
  shr-tr-theorem (.(_ ∨ _) ∂ rl) ((s ←∨→ s₁) ←∂→ s₂) .(∂c _) (sti∂c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem (.(_ ∂ _) ∂ rl) ((s ←∂) ←∂→ s₁) .(∂c _) (sti∂c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∂↓))
  shr-tr-theorem (.(_ ∂ _) ∂ rl) ((∂→ s) ←∂→ s₁) .(∂c _) (sti∂c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∂→↓))
  shr-tr-theorem (.(_ ∂ _) ∂ rl) ((s ←∂→ s₁) ←∂→ s₂) .(∂c _) (sti∂c (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∂→↓))
  shr-tr-theorem (ll ∂ rl) (s ←∂→ ↓) .(∂c _) (sti∂c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓))
  shr-tr-theorem (ll ∂ .(_ ∧ _)) (s ←∂→ (s1 ←∧)) .(∂c _) (sti∂c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∧↓))
  shr-tr-theorem (ll ∂ .(_ ∧ _)) (s ←∂→ (∧→ s1)) .(∂c _) (sti∂c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∧→↓))
  shr-tr-theorem (ll ∂ .(_ ∧ _)) (s ←∂→ (s1 ←∧→ s2)) .(∂c _) (sti∂c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem (ll ∂ .(_ ∨ _)) (s ←∂→ (s1 ←∨)) .(∂c _) (sti∂c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∨↓))
  shr-tr-theorem (ll ∂ .(_ ∨ _)) (s ←∂→ (∨→ s1)) .(∂c _) (sti∂c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∨→↓))
  shr-tr-theorem (ll ∂ .(_ ∨ _)) (s ←∂→ (s1 ←∨→ s2)) .(∂c _) (sti∂c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem (ll ∂ .(_ ∂ _)) (s ←∂→ (s1 ←∂)) .(∂c _) (sti∂c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∂↓))
  shr-tr-theorem (ll ∂ .(_ ∂ _)) (s ←∂→ (∂→ s1)) .(∂c _) (sti∂c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∂→↓))
  shr-tr-theorem (ll ∂ .(_ ∂ _)) (s ←∂→ (s1 ←∂→ s2)) .(∂c _) (sti∂c (inj₂ y)) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∂→↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ↓ .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) (↓ ←∧) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧←∧ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((s ←∧) ←∧) .(∧∧d _) (sti∧∧d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((∧→ s) ←∧) .(∧∧d _) (sti∧∧d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((s ←∧→ s₁) ←∧) .(∧∧d _) (sti∧∧d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) (∧→ s) .(∧∧d _) (sti∧∧d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) (↓ ←∧→ s₁) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓)) 
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((s ←∧) ←∧→ s₁) .(∧∧d _) (sti∧∧d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((∧→ s) ←∧→ s₁) .(∧∧d _) (sti∧∧d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((↓ ←∧→ s₁) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓)))
  shr-tr-theorem ((.(_ ∧ _) ∧ lrl) ∧ rl) (((s ←∧) ←∧→ s₁) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem ((.(_ ∧ _) ∧ lrl) ∧ rl) (((∧→ s) ←∧→ s₁) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem ((.(_ ∧ _) ∧ lrl) ∧ rl) (((s ←∧→ s₁) ←∧→ s₂) ←∧→ s₃) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem ((.(_ ∨ _) ∧ lrl) ∧ rl) (((s ←∨) ←∧→ s₁) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem ((.(_ ∨ _) ∧ lrl) ∧ rl) (((∨→ s) ←∧→ s₁) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem ((.(_ ∨ _) ∧ lrl) ∧ rl) (((s ←∨→ s₁) ←∧→ s₂) ←∧→ s₃) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem ((.(_ ∂ _) ∧ lrl) ∧ rl) (((s ←∂) ←∧→ s₁) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem ((.(_ ∂ _) ∧ lrl) ∧ rl) (((∂→ s) ←∧→ s₁) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem ((.(_ ∂ _) ∧ lrl) ∧ rl) (((s ←∂→ s₁) ←∧→ s₂) ←∧→ s₃) .(∧∧d _) (sti∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∂→↓)))
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ↓ .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) (↓ ←∧) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧←∧ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((s ←∧) ←∧) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((∧→ s) ←∧) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((s ←∧→ s₁) ←∧) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) (∧→ s) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) (↓ ←∧→ s₁) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((s ←∧) ←∧→ s₁) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((∧→ s) ←∧→ s₁) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((s ←∧→ ↓) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓)))
  shr-tr-theorem ((lll ∧ .(_ ∧ _)) ∧ rl) ((s ←∧→ (s1 ←∧)) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem ((lll ∧ .(_ ∧ _)) ∧ rl) ((s ←∧→ (∧→ s1)) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem ((lll ∧ .(_ ∧ _)) ∧ rl) ((s ←∧→ (s1 ←∧→ s2)) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem ((lll ∧ .(_ ∨ _)) ∧ rl) ((s ←∧→ (s1 ←∨)) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem ((lll ∧ .(_ ∨ _)) ∧ rl) ((s ←∧→ (∨→ s1)) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem ((lll ∧ .(_ ∨ _)) ∧ rl) ((s ←∧→ (s1 ←∨→ s2)) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem ((lll ∧ .(_ ∂ _)) ∧ rl) ((s ←∧→ (s1 ←∂)) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem ((lll ∧ .(_ ∂ _)) ∧ rl) ((s ←∧→ (∂→ s1)) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem ((lll ∧ .(_ ∂ _)) ∧ rl) ((s ←∧→ (s1 ←∂→ s2)) ←∧→ s₂) .(∧∧d _) (sti∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∂→↓)))
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ↓ .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y hitsAtLeastOnce↓)
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) (↓ ←∧) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) with shrink lll ↓ | shr-↓-id lll | shrink lrl ↓ | shr-↓-id lrl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) (↓ ←∧) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) | .lll | refl | .lrl | refl = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((s ←∧) ←∧) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((∧→ s) ←∧) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) ((s ←∧→ s₁) ←∧) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) (∧→ s) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∧ lrl) ∧ rl) (s ←∧→ ↓) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ .(_ ∧ _)) (s ←∧→ (s1 ←∧)) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∧↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ .(_ ∧ _)) (s ←∧→ (∧→ s1)) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∧→↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ .(_ ∧ _)) (s ←∧→ (s1 ←∧→ s2)) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ .(_ ∨ _)) (s ←∧→ (s1 ←∨)) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∨↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ .(_ ∨ _)) (s ←∧→ (∨→ s1)) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∨→↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ .(_ ∨ _)) (s ←∧→ (s1 ←∨→ s2)) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ .(_ ∂ _)) (s ←∧→ (s1 ←∂)) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∂↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ .(_ ∂ _)) (s ←∧→ (∂→ s1)) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∂→↓))
  shr-tr-theorem ((lll ∧ lrl) ∧ .(_ ∂ _)) (s ←∧→ (s1 ←∂→ s2)) .(∧∧d _) (sti∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∂→↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ↓ .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) (↓ ←∨) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨←∨ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((s ←∨) ←∨) .(∨∨d _) (sti∨∨d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((∨→ s) ←∨) .(∨∨d _) (sti∨∨d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((s ←∨→ s₁) ←∨) .(∨∨d _) (sti∨∨d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) (∨→ s) .(∨∨d _) (sti∨∨d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) (↓ ←∨→ s₁) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓)) 
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((s ←∨) ←∨→ s₁) .(∨∨d _) (sti∨∨d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((∨→ s) ←∨→ s₁) .(∨∨d _) (sti∨∨d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((↓ ←∨→ s₁) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓)))
  shr-tr-theorem ((.(_ ∧ _) ∨ lrl) ∨ rl) (((s ←∧) ←∨→ s₁) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem ((.(_ ∧ _) ∨ lrl) ∨ rl) (((∧→ s) ←∨→ s₁) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem ((.(_ ∧ _) ∨ lrl) ∨ rl) (((s ←∧→ s₁) ←∨→ s₂) ←∨→ s₃) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem ((.(_ ∨ _) ∨ lrl) ∨ rl) (((s ←∨) ←∨→ s₁) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem ((.(_ ∨ _) ∨ lrl) ∨ rl) (((∨→ s) ←∨→ s₁) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem ((.(_ ∨ _) ∨ lrl) ∨ rl) (((s ←∨→ s₁) ←∨→ s₂) ←∨→ s₃) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem ((.(_ ∂ _) ∨ lrl) ∨ rl) (((s ←∂) ←∨→ s₁) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem ((.(_ ∂ _) ∨ lrl) ∨ rl) (((∂→ s) ←∨→ s₁) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem ((.(_ ∂ _) ∨ lrl) ∨ rl) (((s ←∂→ s₁) ←∨→ s₂) ←∨→ s₃) .(∨∨d _) (sti∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∂→↓)))
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ↓ .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) (↓ ←∨) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨←∨ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((s ←∨) ←∨) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((∨→ s) ←∨) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((s ←∨→ s₁) ←∨) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) (∨→ s) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) (↓ ←∨→ s₁) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((s ←∨) ←∨→ s₁) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((∨→ s) ←∨→ s₁) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((s ←∨→ ↓) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓)))
  shr-tr-theorem ((lll ∨ .(_ ∧ _)) ∨ rl) ((s ←∨→ (s1 ←∧)) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem ((lll ∨ .(_ ∧ _)) ∨ rl) ((s ←∨→ (∧→ s1)) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem ((lll ∨ .(_ ∧ _)) ∨ rl) ((s ←∨→ (s1 ←∧→ s2)) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem ((lll ∨ .(_ ∨ _)) ∨ rl) ((s ←∨→ (s1 ←∨)) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem ((lll ∨ .(_ ∨ _)) ∨ rl) ((s ←∨→ (∨→ s1)) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem ((lll ∨ .(_ ∨ _)) ∨ rl) ((s ←∨→ (s1 ←∨→ s2)) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem ((lll ∨ .(_ ∂ _)) ∨ rl) ((s ←∨→ (s1 ←∂)) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem ((lll ∨ .(_ ∂ _)) ∨ rl) ((s ←∨→ (∂→ s1)) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem ((lll ∨ .(_ ∂ _)) ∨ rl) ((s ←∨→ (s1 ←∂→ s2)) ←∨→ s₂) .(∨∨d _) (sti∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∂→↓)))
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ↓ .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y hitsAtLeastOnce↓)
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) (↓ ←∨) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) with shrink lll ↓ | shr-↓-id lll | shrink lrl ↓ | shr-↓-id lrl
  ... | .lll | refl | .lrl | refl = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((s ←∨) ←∨) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((∨→ s) ←∨) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) ((s ←∨→ s₁) ←∨) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) (∨→ s) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∨ lrl) ∨ rl) (s ←∨→ ↓) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ .(_ ∧ _)) (s ←∨→ (s1 ←∧)) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∧↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ .(_ ∧ _)) (s ←∨→ (∧→ s1)) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∧→↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ .(_ ∧ _)) (s ←∨→ (s1 ←∧→ s2)) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ .(_ ∨ _)) (s ←∨→ (s1 ←∨)) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∨↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ .(_ ∨ _)) (s ←∨→ (∨→ s1)) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∨→↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ .(_ ∨ _)) (s ←∨→ (s1 ←∨→ s2)) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ .(_ ∂ _)) (s ←∨→ (s1 ←∂)) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∂↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ .(_ ∂ _)) (s ←∨→ (∂→ s1)) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∂→↓))
  shr-tr-theorem ((lll ∨ lrl) ∨ .(_ ∂ _)) (s ←∨→ (s1 ←∂→ s2)) .(∨∨d _) (sti∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∂→↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ↓ .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) (↓ ←∂) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂←∂ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((s ←∂) ←∂) .(∂∂d _) (sti∂∂d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((∂→ s) ←∂) .(∂∂d _) (sti∂∂d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((s ←∂→ s₁) ←∂) .(∂∂d _) (sti∂∂d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) (∂→ s) .(∂∂d _) (sti∂∂d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) (↓ ←∂→ s₁) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓)) 
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((s ←∂) ←∂→ s₁) .(∂∂d _) (sti∂∂d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((∂→ s) ←∂→ s₁) .(∂∂d _) (sti∂∂d (inj₁ x)) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((↓ ←∂→ s₁) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓)))
  shr-tr-theorem ((.(_ ∧ _) ∂ lrl) ∂ rl) (((s ←∧) ←∂→ s₁) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem ((.(_ ∧ _) ∂ lrl) ∂ rl) (((∧→ s) ←∂→ s₁) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem ((.(_ ∧ _) ∂ lrl) ∂ rl) (((s ←∧→ s₁) ←∂→ s₂) ←∂→ s₃) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem ((.(_ ∨ _) ∂ lrl) ∂ rl) (((s ←∨) ←∂→ s₁) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem ((.(_ ∨ _) ∂ lrl) ∂ rl) (((∨→ s) ←∂→ s₁) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem ((.(_ ∨ _) ∂ lrl) ∂ rl) (((s ←∨→ s₁) ←∂→ s₂) ←∂→ s₃) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem ((.(_ ∂ _) ∂ lrl) ∂ rl) (((s ←∂) ←∂→ s₁) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem ((.(_ ∂ _) ∂ lrl) ∂ rl) (((∂→ s) ←∂→ s₁) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem ((.(_ ∂ _) ∂ lrl) ∂ rl) (((s ←∂→ s₁) ←∂→ s₂) ←∂→ s₃) .(∂∂d _) (sti∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∂→↓)))
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ↓ .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) (↓ ←∂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂←∂ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((s ←∂) ←∂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((∂→ s) ←∂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((s ←∂→ s₁) ←∂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) (∂→ s) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) (↓ ←∂→ s₁) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((s ←∂) ←∂→ s₁) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((∂→ s) ←∂→ s₁) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((s ←∂→ ↓) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓)))
  shr-tr-theorem ((lll ∂ .(_ ∧ _)) ∂ rl) ((s ←∂→ (s1 ←∧)) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem ((lll ∂ .(_ ∧ _)) ∂ rl) ((s ←∂→ (∧→ s1)) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem ((lll ∂ .(_ ∧ _)) ∂ rl) ((s ←∂→ (s1 ←∧→ s2)) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem ((lll ∂ .(_ ∨ _)) ∂ rl) ((s ←∂→ (s1 ←∨)) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem ((lll ∂ .(_ ∨ _)) ∂ rl) ((s ←∂→ (∨→ s1)) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem ((lll ∂ .(_ ∨ _)) ∂ rl) ((s ←∂→ (s1 ←∨→ s2)) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem ((lll ∂ .(_ ∂ _)) ∂ rl) ((s ←∂→ (s1 ←∂)) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem ((lll ∂ .(_ ∂ _)) ∂ rl) ((s ←∂→ (∂→ s1)) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem ((lll ∂ .(_ ∂ _)) ∂ rl) ((s ←∂→ (s1 ←∂→ s2)) ←∂→ s₂) .(∂∂d _) (sti∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∂→↓)))
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ↓ .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y hitsAtLeastOnce↓)
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) (↓ ←∂) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) with shrink lll ↓ | shr-↓-id lll | shrink lrl ↓ | shr-↓-id lrl
  ... | .lll | refl | .lrl | refl = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((s ←∂) ←∂) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((∂→ s) ←∂) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) ((s ←∂→ s₁) ←∂) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) (∂→ s) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem ((lll ∂ lrl) ∂ rl) (s ←∂→ ↓) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ .(_ ∧ _)) (s ←∂→ (s1 ←∧)) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∧↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ .(_ ∧ _)) (s ←∂→ (∧→ s1)) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∧→↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ .(_ ∧ _)) (s ←∂→ (s1 ←∧→ s2)) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ .(_ ∨ _)) (s ←∂→ (s1 ←∨)) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∨↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ .(_ ∨ _)) (s ←∂→ (∨→ s1)) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∨→↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ .(_ ∨ _)) (s ←∂→ (s1 ←∨→ s2)) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ .(_ ∂ _)) (s ←∂→ (s1 ←∂)) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∂↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ .(_ ∂ _)) (s ←∂→ (∂→ s1)) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∂→↓))
  shr-tr-theorem ((lll ∂ lrl) ∂ .(_ ∂ _)) (s ←∂→ (s1 ←∂→ s2)) .(∂∂d _) (sti∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∂→↓))

  shr-tr-theorem (ll ∧ (rll ∧ rrl)) ↓ .(¬∧∧d _) (sti¬∧∧d (inj₁ x)) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) ↓ .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) ↓ .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (s ←∧) .(¬∧∧d _) (sti¬∧∧d x) = refl
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (∧→ ↓) .(¬∧∧d _) (sti¬∧∧d x) with shrink rll ↓ | shr-↓-id rll | shrink rrl ↓ | shr-↓-id rrl
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (∧→ ↓) .(¬∧∧d _) (sti¬∧∧d x) | .rll | refl | .rrl | refl = refl
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (∧→ (s ←∧)) .(¬∧∧d _) (sti¬∧∧d x) = refl
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (∧→ (∧→ s)) .(¬∧∧d _) (sti¬∧∧d x) = refl
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (∧→ (s ←∧→ s₁)) .(¬∧∧d _) (sti¬∧∧d x) = refl
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (↓ ←∧→ s₁) .(¬∧∧d _) (sti¬∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓)) 
  shr-tr-theorem (.(_ ∧ _) ∧ (rll ∧ rrl)) ((s ←∧) ←∧→ s₁) .(¬∧∧d _) (sti¬∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∧↓))
  shr-tr-theorem (.(_ ∧ _) ∧ (rll ∧ rrl)) ((∧→ s) ←∧→ s₁) .(¬∧∧d _) (sti¬∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∧→↓))
  shr-tr-theorem (.(_ ∧ _) ∧ (rll ∧ rrl)) ((s ←∧→ s₁) ←∧→ s₂) .(¬∧∧d _) (sti¬∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem (.(_ ∨ _) ∧ (rll ∧ rrl)) ((s ←∨) ←∧→ s₁) .(¬∧∧d _) (sti¬∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∨↓))
  shr-tr-theorem (.(_ ∨ _) ∧ (rll ∧ rrl)) ((∨→ s) ←∧→ s₁) .(¬∧∧d _) (sti¬∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∨→↓))
  shr-tr-theorem (.(_ ∨ _) ∧ (rll ∧ rrl)) ((s ←∨→ s₁) ←∧→ s₂) .(¬∧∧d _) (sti¬∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem (.(_ ∂ _) ∧ (rll ∧ rrl)) ((s ←∂) ←∧→ s₁) .(¬∧∧d _) (sti¬∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∂↓))
  shr-tr-theorem (.(_ ∂ _) ∧ (rll ∧ rrl)) ((∂→ s) ←∧→ s₁) .(¬∧∧d _) (sti¬∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∂→↓))
  shr-tr-theorem (.(_ ∂ _) ∧ (rll ∧ rrl)) ((s ←∂→ s₁) ←∧→ s₂) .(¬∧∧d _) (sti¬∧∧d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∂→↓))
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (s ←∧→ ↓) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓))
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (s ←∧→ (s1 ←∧)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (s ←∧→ (∧→ s1)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (s ←∧→ (s1 ←∧→ ↓)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓)))
  shr-tr-theorem (ll ∧ (rll ∧ .(_ ∧ _))) (s ←∧→ (s1 ←∧→ (s2 ←∧))) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem (ll ∧ (rll ∧ .(_ ∧ _))) (s ←∧→ (s1 ←∧→ (∧→ s2))) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem (ll ∧ (rll ∧ .(_ ∧ _))) (s ←∧→ (s1 ←∧→ (s2 ←∧→ s3))) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                           (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem (ll ∧ (rll ∧ .(_ ∨ _))) (s ←∧→ (s1 ←∧→ (s2 ←∨))) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem (ll ∧ (rll ∧ .(_ ∨ _))) (s ←∧→ (s1 ←∧→ (∨→ s2))) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem (ll ∧ (rll ∧ .(_ ∨ _))) (s ←∧→ (s1 ←∧→ (s2 ←∨→ s3))) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                           (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem (ll ∧ (rll ∧ .(_ ∂ _))) (s ←∧→ (s1 ←∧→ (s2 ←∂))) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem (ll ∧ (rll ∧ .(_ ∂ _))) (s ←∧→ (s1 ←∧→ (∂→ s2))) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem (ll ∧ (rll ∧ .(_ ∂ _))) (s ←∧→ (s1 ←∧→ (s2 ←∂→ s3))) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                           (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce←∂→↓)))
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (s ←∧→ ↓) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓))
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (s ←∧→ (s1 ←∧)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (s ←∧→ (∧→ s1)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem (ll ∧ (rll ∧ rrl)) (s ←∧→ (↓ ←∧→ s2)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓)))
  shr-tr-theorem (ll ∧ (.(_ ∧ _) ∧ rrl)) (s ←∧→ ((s1 ←∧) ←∧→ s2)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem (ll ∧ (.(_ ∧ _) ∧ rrl)) (s ←∧→ ((∧→ s1) ←∧→ s2)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem (ll ∧ (.(_ ∧ _) ∧ rrl)) (s ←∧→ ((s1 ←∧→ s2) ←∧→ s3)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                           (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem (ll ∧ (.(_ ∨ _) ∧ rrl)) (s ←∧→ ((s1 ←∨) ←∧→ s2)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem (ll ∧ (.(_ ∨ _) ∧ rrl)) (s ←∧→ ((∨→ s1) ←∧→ s2)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem (ll ∧ (.(_ ∨ _) ∧ rrl)) (s ←∧→ ((s1 ←∨→ s2) ←∧→ s3)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                           (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem (ll ∧ (.(_ ∂ _) ∧ rrl)) (s ←∧→ ((s1 ←∂) ←∧→ s2)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem (ll ∧ (.(_ ∂ _) ∧ rrl)) (s ←∧→ ((∂→ s1) ←∧→ s2)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem (ll ∧ (.(_ ∂ _) ∧ rrl)) (s ←∧→ ((s1 ←∂→ s2) ←∧→ s3)) .(¬∧∧d _) (sti¬∧∧d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                           (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce←∂→↓)))
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) ↓ .(¬∨∨d _) (sti¬∨∨d (inj₁ x)) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) ↓ .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) ↓ .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (s ←∨) .(¬∨∨d _) (sti¬∨∨d x) = refl
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (∨→ ↓) .(¬∨∨d _) (sti¬∨∨d x) with shrink rll ↓ | shr-↓-id rll | shrink rrl ↓ | shr-↓-id rrl
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (∨→ ↓) .(¬∨∨d _) (sti¬∨∨d x) | .rll | refl | .rrl | refl = refl
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (∨→ (s ←∨)) .(¬∨∨d _) (sti¬∨∨d x) = refl
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (∨→ (∨→ s)) .(¬∨∨d _) (sti¬∨∨d x) = refl
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (∨→ (s ←∨→ s₁)) .(¬∨∨d _) (sti¬∨∨d x) = refl
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (↓ ←∨→ s₁) .(¬∨∨d _) (sti¬∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓)) 
  shr-tr-theorem (.(_ ∧ _) ∨ (rll ∨ rrl)) ((s ←∧) ←∨→ s₁) .(¬∨∨d _) (sti¬∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∧↓))
  shr-tr-theorem (.(_ ∧ _) ∨ (rll ∨ rrl)) ((∧→ s) ←∨→ s₁) .(¬∨∨d _) (sti¬∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∧→↓))
  shr-tr-theorem (.(_ ∧ _) ∨ (rll ∨ rrl)) ((s ←∧→ s₁) ←∨→ s₂) .(¬∨∨d _) (sti¬∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem (.(_ ∨ _) ∨ (rll ∨ rrl)) ((s ←∨) ←∨→ s₁) .(¬∨∨d _) (sti¬∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∨↓))
  shr-tr-theorem (.(_ ∨ _) ∨ (rll ∨ rrl)) ((∨→ s) ←∨→ s₁) .(¬∨∨d _) (sti¬∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∨→↓))
  shr-tr-theorem (.(_ ∨ _) ∨ (rll ∨ rrl)) ((s ←∨→ s₁) ←∨→ s₂) .(¬∨∨d _) (sti¬∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem (.(_ ∂ _) ∨ (rll ∨ rrl)) ((s ←∂) ←∨→ s₁) .(¬∨∨d _) (sti¬∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∂↓))
  shr-tr-theorem (.(_ ∂ _) ∨ (rll ∨ rrl)) ((∂→ s) ←∨→ s₁) .(¬∨∨d _) (sti¬∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∂→↓))
  shr-tr-theorem (.(_ ∂ _) ∨ (rll ∨ rrl)) ((s ←∂→ s₁) ←∨→ s₂) .(¬∨∨d _) (sti¬∨∨d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∂→↓))
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (s ←∨→ ↓) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓))
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (s ←∨→ (s1 ←∨)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (s ←∨→ (∨→ s1)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (s ←∨→ (s1 ←∨→ ↓)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓)))
  shr-tr-theorem (ll ∨ (rll ∨ .(_ ∧ _))) (s ←∨→ (s1 ←∨→ (s2 ←∧))) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem (ll ∨ (rll ∨ .(_ ∧ _))) (s ←∨→ (s1 ←∨→ (∧→ s2))) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem (ll ∨ (rll ∨ .(_ ∧ _))) (s ←∨→ (s1 ←∨→ (s2 ←∧→ s3))) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                           (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem (ll ∨ (rll ∨ .(_ ∨ _))) (s ←∨→ (s1 ←∨→ (s2 ←∨))) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem (ll ∨ (rll ∨ .(_ ∨ _))) (s ←∨→ (s1 ←∨→ (∨→ s2))) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem (ll ∨ (rll ∨ .(_ ∨ _))) (s ←∨→ (s1 ←∨→ (s2 ←∨→ s3))) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                           (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem (ll ∨ (rll ∨ .(_ ∂ _))) (s ←∨→ (s1 ←∨→ (s2 ←∂))) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem (ll ∨ (rll ∨ .(_ ∂ _))) (s ←∨→ (s1 ←∨→ (∂→ s2))) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem (ll ∨ (rll ∨ .(_ ∂ _))) (s ←∨→ (s1 ←∨→ (s2 ←∂→ s3))) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                           (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce←∂→↓)))
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (s ←∨→ ↓) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓))
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (s ←∨→ (s1 ←∨)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (s ←∨→ (∨→ s1)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem (ll ∨ (rll ∨ rrl)) (s ←∨→ (↓ ←∨→ s2)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓)))
  shr-tr-theorem (ll ∨ (.(_ ∧ _) ∨ rrl)) (s ←∨→ ((s1 ←∧) ←∨→ s2)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem (ll ∨ (.(_ ∧ _) ∨ rrl)) (s ←∨→ ((∧→ s1) ←∨→ s2)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem (ll ∨ (.(_ ∧ _) ∨ rrl)) (s ←∨→ ((s1 ←∧→ s2) ←∨→ s3)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                           (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem (ll ∨ (.(_ ∨ _) ∨ rrl)) (s ←∨→ ((s1 ←∨) ←∨→ s2)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem (ll ∨ (.(_ ∨ _) ∨ rrl)) (s ←∨→ ((∨→ s1) ←∨→ s2)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem (ll ∨ (.(_ ∨ _) ∨ rrl)) (s ←∨→ ((s1 ←∨→ s2) ←∨→ s3)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                           (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem (ll ∨ (.(_ ∂ _) ∨ rrl)) (s ←∨→ ((s1 ←∂) ←∨→ s2)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem (ll ∨ (.(_ ∂ _) ∨ rrl)) (s ←∨→ ((∂→ s1) ←∨→ s2)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem (ll ∨ (.(_ ∂ _) ∨ rrl)) (s ←∨→ ((s1 ←∂→ s2) ←∨→ s3)) .(¬∨∨d _) (sti¬∨∨d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                           (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce←∂→↓)))
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) ↓ .(¬∂∂d _) (sti¬∂∂d (inj₁ x)) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) ↓ .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) ↓ .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y hitsAtLeastOnce↓)
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (s ←∂) .(¬∂∂d _) (sti¬∂∂d x) = refl
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (∂→ ↓) .(¬∂∂d _) (sti¬∂∂d x) with shrink rll ↓ | shr-↓-id rll | shrink rrl ↓ | shr-↓-id rrl
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (∂→ ↓) .(¬∂∂d _) (sti¬∂∂d x) | .rll | refl | .rrl | refl = refl
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (∂→ (s ←∂)) .(¬∂∂d _) (sti¬∂∂d x) = refl
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (∂→ (∂→ s)) .(¬∂∂d _) (sti¬∂∂d x) = refl
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (∂→ (s ←∂→ s₁)) .(¬∂∂d _) (sti¬∂∂d x) = refl
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (↓ ←∂→ s₁) .(¬∂∂d _) (sti¬∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓)) 
  shr-tr-theorem (.(_ ∧ _) ∂ (rll ∂ rrl)) ((s ←∧) ←∂→ s₁) .(¬∂∂d _) (sti¬∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∧↓))
  shr-tr-theorem (.(_ ∧ _) ∂ (rll ∂ rrl)) ((∧→ s) ←∂→ s₁) .(¬∂∂d _) (sti¬∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∧→↓))
  shr-tr-theorem (.(_ ∧ _) ∂ (rll ∂ rrl)) ((s ←∧→ s₁) ←∂→ s₂) .(¬∂∂d _) (sti¬∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∧→↓))
  shr-tr-theorem (.(_ ∨ _) ∂ (rll ∂ rrl)) ((s ←∨) ←∂→ s₁) .(¬∂∂d _) (sti¬∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∨↓))
  shr-tr-theorem (.(_ ∨ _) ∂ (rll ∂ rrl)) ((∨→ s) ←∂→ s₁) .(¬∂∂d _) (sti¬∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∨→↓))
  shr-tr-theorem (.(_ ∨ _) ∂ (rll ∂ rrl)) ((s ←∨→ s₁) ←∂→ s₂) .(¬∂∂d _) (sti¬∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∨→↓))
  shr-tr-theorem (.(_ ∂ _) ∂ (rll ∂ rrl)) ((s ←∂) ←∂→ s₁) .(¬∂∂d _) (sti¬∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∂↓))
  shr-tr-theorem (.(_ ∂ _) ∂ (rll ∂ rrl)) ((∂→ s) ←∂→ s₁) .(¬∂∂d _) (sti¬∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∂→↓))
  shr-tr-theorem (.(_ ∂ _) ∂ (rll ∂ rrl)) ((s ←∂→ s₁) ←∂→ s₂) .(¬∂∂d _) (sti¬∂∂d (inj₁ x)) = ⊥-elim (x (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∂→↓))
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (s ←∂→ ↓) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓))
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (s ←∂→ (s1 ←∂)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (s ←∂→ (∂→ s1)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = refl
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (s ←∂→ (s1 ←∂→ ↓)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓)))
  shr-tr-theorem (ll ∂ (rll ∂ .(_ ∧ _))) (s ←∂→ (s1 ←∂→ (s2 ←∧))) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem (ll ∂ (rll ∂ .(_ ∧ _))) (s ←∂→ (s1 ←∂→ (∧→ s2))) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem (ll ∂ (rll ∂ .(_ ∧ _))) (s ←∂→ (s1 ←∂→ (s2 ←∧→ s3))) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                           (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem (ll ∂ (rll ∂ .(_ ∨ _))) (s ←∂→ (s1 ←∂→ (s2 ←∨))) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem (ll ∂ (rll ∂ .(_ ∨ _))) (s ←∂→ (s1 ←∂→ (∨→ s2))) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem (ll ∂ (rll ∂ .(_ ∨ _))) (s ←∂→ (s1 ←∂→ (s2 ←∨→ s3))) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                           (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem (ll ∂ (rll ∂ .(_ ∂ _))) (s ←∂→ (s1 ←∂→ (s2 ←∂))) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem (ll ∂ (rll ∂ .(_ ∂ _))) (s ←∂→ (s1 ←∂→ (∂→ s2))) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem (ll ∂ (rll ∂ .(_ ∂ _))) (s ←∂→ (s1 ←∂→ (s2 ←∂→ s3))) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₁ x))) = ⊥-elim (x
                                                                                                           (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce←∂→↓)))
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (s ←∂→ ↓) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓))
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (s ←∂→ (s1 ←∂)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (s ←∂→ (∂→ s1)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = refl
  shr-tr-theorem (ll ∂ (rll ∂ rrl)) (s ←∂→ (↓ ←∂→ s2)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓)))
  shr-tr-theorem (ll ∂ (.(_ ∧ _) ∂ rrl)) (s ←∂→ ((s1 ←∧) ←∂→ s2)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∧↓)))
  shr-tr-theorem (ll ∂ (.(_ ∧ _) ∂ rrl)) (s ←∂→ ((∧→ s1) ←∂→ s2)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∧→↓)))
  shr-tr-theorem (ll ∂ (.(_ ∧ _) ∂ rrl)) (s ←∂→ ((s1 ←∧→ s2) ←∂→ s3)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                           (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∧→↓)))
  shr-tr-theorem (ll ∂ (.(_ ∨ _) ∂ rrl)) (s ←∂→ ((s1 ←∨) ←∂→ s2)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∨↓)))
  shr-tr-theorem (ll ∂ (.(_ ∨ _) ∂ rrl)) (s ←∂→ ((∨→ s1) ←∂→ s2)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∨→↓)))
  shr-tr-theorem (ll ∂ (.(_ ∨ _) ∂ rrl)) (s ←∂→ ((s1 ←∨→ s2) ←∂→ s3)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                           (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∨→↓)))
  shr-tr-theorem (ll ∂ (.(_ ∂ _) ∂ rrl)) (s ←∂→ ((s1 ←∂) ←∂→ s2)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∂↓)))
  shr-tr-theorem (ll ∂ (.(_ ∂ _) ∂ rrl)) (s ←∂→ ((∂→ s1) ←∂→ s2)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                       (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce∂→↓)))
  shr-tr-theorem (ll ∂ (.(_ ∂ _) ∂ rrl)) (s ←∂→ ((s1 ←∂→ s2) ←∂→ s3)) .(¬∂∂d _) (sti¬∂∂d (inj₂ (inj₂ y))) = ⊥-elim (y
                                                                                                           (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce←∂→↓)))





module _ where

  open IndexLLProp

  
  
  -- TODO IMPORTANT tranlFMSetLL is also used in LinFunCut as a private function. Maybe we need a separate file to add all the transformation by lf of IndexLL and SetLL.
  
  data MIndexLL {i u} (rll ll : LinLogic i {u}) : Set u where
    ∅ : MIndexLL rll ll
    ¬∅ : IndexLL rll ll → MIndexLL rll ll
  
  
  tranLFMIndexLL : ∀{i u rll ll n dt df} → (lf : LFun ll rll)
                   → (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll) → MIndexLL (τ {i} {u} {n} {dt} df) rll
  tranLFMIndexLL lf ∅ = ∅
  tranLFMIndexLL I (¬∅ ind) = ¬∅ ind
  tranLFMIndexLL {ll = ll} {df = df} (_⊂_ {pll = pll} {ell = ell} {ind = lind} lf lf₁) (¬∅ ind) with isLTi lind ind
  ... | no ¬p =  tranLFMIndexLL lf₁ (¬∅ (¬ord-morph ind lind ell (flipNotOrdᵢ (indτ&¬ge⇒¬Ord ind lind ¬p))))
  ... | yes p = tranLFMIndexLL lf₁ (hf2 r) where
    hf : MIndexLL (τ df) pll
    hf = ¬∅ ((ind -ᵢ lind) p)
  
    r = tranLFMIndexLL lf hf
    rind = subst (λ x → IndexLL x (replLL ll lind ell)) (replLL-↓ {ell = ell} lind) (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))
    hf2 : MIndexLL (τ df) ell → MIndexLL (τ df) (replLL ll lind ell)
    hf2 ∅ = ∅
    hf2 (¬∅ x) = ¬∅ (rind +ᵢ x)
    
  tranLFMIndexLL (tr ltr lf) (¬∅ ind) = r where
    ut = indLow⇒UpTran ind ltr
    tind = IndexLLProp.tran ind ltr ut
    r = tranLFMIndexLL lf (¬∅ tind)
  tranLFMIndexLL (com df₁ lf) (¬∅ ind) = ∅
  tranLFMIndexLL (call x) (¬∅ ind) = ∅
  
  
  
  tranLFMSetLL : ∀{i u ll rll} → (lf : LFun {i} {u} ll rll) → MSetLL ll → MSetLL rll
  tranLFMSetLL lf ∅ = ∅
  tranLFMSetLL I (¬∅ x) = ¬∅ x
  tranLFMSetLL (_⊂_ {ind = ind} lf lf₁) (¬∅ x) = tranLFMSetLL lf₁ nmx where
    tlf = tranLFMSetLL lf (truncSetLL x ind)
    nmx = mreplacePartOf (¬∅ x) to tlf at ind
  tranLFMSetLL (tr ltr lf) (¬∅ x) = tranLFMSetLL lf (¬∅ (SetLL.tran x ltr))
  tranLFMSetLL (com df lf) (¬∅ x) = ∅
  tranLFMSetLL (call x) (¬∅ x₁) = ∅
  
  
  
  
  
  
  tranLF-preserves-¬ho : ∀{i u rll ll n dt df tind ts} → (lf : LFun ll rll)
         → (ind : IndexLL (τ {i} {u} {n} {dt} df) ll) → (s : SetLL ll) → ¬ (hitsAtLeastOnce s ind)
         → ¬∅ tind ≡ tranLFMIndexLL lf (¬∅ ind) → ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)
         → ¬ (hitsAtLeastOnce ts tind) 
  tranLF-preserves-¬ho I ind s ¬ho refl refl = ¬ho
  tranLF-preserves-¬ho (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi eqs with truncSetLL s lind | inspect (truncSetLL s) lind | isLTi lind ind
  tranLF-preserves-¬ho (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ∅ | _ | yes p with del s lind ell | inspect (del s lind) ell
  tranLF-preserves-¬ho (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi () | ∅ | _ | yes p | ∅ | [ eq ]
  tranLF-preserves-¬ho (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ∅ | _ | yes p | ¬∅ x | [ eq ] with (tranLFMIndexLL lf (¬∅ ((ind -ᵢ lind) p)))
  tranLF-preserves-¬ho (_⊂_ {ind = ind} lf lf₁) ind₁ s ¬ho () eqs | ∅ | _ | yes p | ¬∅ x | [ eq ] | ∅
  tranLF-preserves-¬ho {ll = ll} (_⊂_ {pll = pll} {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ∅ | _ | yes p | ¬∅ x | [ eq ] | ¬∅ y = tranLF-preserves-¬ho lf₁ (o +ᵢ y) x hf2 eqi eqs where
    r = (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))
    hf = del⇒¬ho s lind (sym eq)
    o = subst (λ x → IndexLL x (replLL ll lind ell)) (replLL-↓ {ell = ell} lind) r
    hf2 : ¬ (hitsAtLeastOnce x (o +ᵢ y))
    hf2 with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | r | hf
    hf2 | g | refl | w | q = ¬ho⇒ind+¬ho x w q y
  tranLF-preserves-¬ho (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ∅ | _ | no ¬p
                                                          with del s lind ell | inspect (del s lind) ell
  tranLF-preserves-¬ho (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi () | ∅ | _ | no ¬p | ∅ | r
  tranLF-preserves-¬ho (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ∅ | _ | no ¬p | ¬∅ x | [ eq ] = is where
    n¬ord = indτ&¬ge⇒¬Ord ind lind ¬p
    hf = ¬ord&¬ho-del⇒¬ho ind s ¬ho lind {x} n¬ord (sym eq)
    is = tranLF-preserves-¬ho lf₁ (¬ord-morph ind lind ell (flipNotOrdᵢ n¬ord)) x hf eqi eqs
  tranLF-preserves-¬ho (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x | _ | yes p with tranLFMSetLL lf (¬∅ x) | inspect (tranLFMSetLL lf) (¬∅ x)
  tranLF-preserves-¬ho (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x | _ | yes p | ∅ | _ with del s lind ell | inspect (del s lind) ell | (tranLFMIndexLL lf (¬∅ ((ind -ᵢ lind) p)))
  tranLF-preserves-¬ho (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi () | ¬∅ x | _ | yes p | ∅ | _ | ∅ | q | g
  tranLF-preserves-¬ho (_⊂_ {ind = lind} lf lf₁) ind s ¬ho () eqs | ¬∅ x₁ | _ | yes p | ∅ | _ | ¬∅ x | q | ∅
  tranLF-preserves-¬ho {ll = ll} (_⊂_ {pll = pll} {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x₂ | _ | yes p | ∅ | _ | ¬∅ x | [ eq ] | ¬∅ y =  tranLF-preserves-¬ho lf₁ (o +ᵢ y) x hf2 eqi eqs where
    r = (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))
    hf = del⇒¬ho s lind (sym eq)
    o = subst (λ x → IndexLL x (replLL ll lind ell)) (replLL-↓ {ell = ell} lind) r
    hf2 : ¬ (hitsAtLeastOnce x (o +ᵢ y))
    hf2 with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | r | hf
    hf2 | g | refl | w | q = ¬ho⇒ind+¬ho x w q y
  tranLF-preserves-¬ho (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x | [ eqt ] | yes p | ¬∅ y | [ eq ]
      with tranLFMIndexLL lf (¬∅ ((ind -ᵢ lind) p)) | inspect (λ z → tranLFMIndexLL lf (¬∅ ((ind -ᵢ lind) z))) p
  tranLF-preserves-¬ho (_⊂_ {ind = lind} lf lf₁) ind s ¬ho () eqs | ¬∅ x | [ eqt ] | yes p | ¬∅ y | [ eq ] | ∅ | g
  tranLF-preserves-¬ho {ll = ll} (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x | [ eqt ] | yes p | ¬∅ y | [ eq ] | ¬∅ t | [ eq₁ ] = tranLF-preserves-¬ho lf₁ (subst (λ z → IndexLL z (replLL ll lind ell)) (replLL-↓ lind)
                                                                                                                           (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))
                                                                                                                           +ᵢ t) (replacePartOf s to y at lind) a eqi eqs where
    w = tranLF-preserves-¬ho lf ((ind -ᵢ lind) p) x (rl&¬ho-trunc⇒¬ho s ind ¬ho lind p (sym eqt)) (sym eq₁) (sym eq)
    a = a≤b&¬ho-repl⇒¬ho s y t lind w
  tranLF-preserves-¬ho (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x | _ | no ¬p with tranLFMSetLL lf (¬∅ x)
  tranLF-preserves-¬ho (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x | _ | no ¬p | ∅
                                                       with del s lind ell | inspect (del s lind) ell
  tranLF-preserves-¬ho (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi () | ¬∅ x | _ | no ¬p | ∅ | ∅ | r
  tranLF-preserves-¬ho (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x₁ | _ | no ¬p | ∅ | ¬∅ x | [ eq ] = is where
    n¬ord = indτ&¬ge⇒¬Ord ind lind ¬p
    hf = ¬ord&¬ho-del⇒¬ho ind s ¬ho lind {x} n¬ord (sym eq)
    is = tranLF-preserves-¬ho lf₁ (¬ord-morph ind lind ell (flipNotOrdᵢ n¬ord)) x hf eqi eqs
  tranLF-preserves-¬ho (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ _ | _ | no ¬p | ¬∅ x = tranLF-preserves-¬ho lf₁ nind (replacePartOf s to x at lind) hf eqi eqs where
    n¬ord = indτ&¬ge⇒¬Ord ind lind ¬p
    nind = ¬ord-morph ind lind ell (flipNotOrdᵢ n¬ord)
    hf = ¬ord&¬ho-repl⇒¬ho ind s {x} ¬ho lind n¬ord
  tranLF-preserves-¬ho {tind = tind} {ts} (tr ltr lf) ind s ¬ho eqi eqs = tranLF-preserves-¬ho lf (IndexLLProp.tran ind ltr ut) (SetLL.tran s ltr) ¬tho eqi eqs  where
    ut = indLow⇒UpTran ind ltr 
    ¬tho = ¬trho ltr s ind ¬ho ut
  tranLF-preserves-¬ho (com df₁ lf) ind s ¬ho () eqs
  tranLF-preserves-¬ho (call x) ind s ¬ho () eqs
  
  
  
  
  
  
  
  -- trunc≡∅-shrmorph : ∀{i u rll ll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll)
  --                   → (ceq : ¬ ((contruct s) ≡ ↓)) → (truncSetLL s ind ≡ ∅)
  --                   → IndexLL rll (shrink ll s ceq)
  -- trunc≡∅-shrmorph s ind ceq treq with complLₛ s | ¬contruct↓⇒¬compl∅ s ceq
  -- trunc≡∅-shrmorph s ind ceq treq | ∅ | r = ⊥-elim (r refl)
  -- trunc≡∅-shrmorph s ind ceq treq | ¬∅ x | r = trunc≡∅-shrmorph` x ind where
  --  trunc≡∅-shrmorph` : ∀{i u rll ll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → (truncSetLL s ind ≡ ∅) → IndexLL rll (shrink ll s ceq)
  --  trunc≡∅-shrmorph` {ll = ∅} s ind treq | ¬∅ ↓ | r = ind
  --  trunc≡∅-shrmorph` {ll = τ y} s ind treq | ¬∅ ↓ | r = ind
  --  trunc≡∅-shrmorph` {ll = ll ∧ rl} s ind treq | ¬∅ ↓ | r = ind
  --  trunc≡∅-shrmorph` {ll = ll ∧ rl} s ind treq | ¬∅ (x ←∧) | r = {!!}
  --  trunc≡∅-shrmorph` {ll = ll ∧ rl} s ind treq | ¬∅ (∧→ x) | r = {!!}
  --  trunc≡∅-shrmorph` {ll = ll ∧ rl} s ind treq | ¬∅ (x ←∧→ x₁) | r = {!!}
  --  trunc≡∅-shrmorph` {ll = ll ∨ rl} s ind treq | ¬∅ x | r = {!!}
  --  trunc≡∅-shrmorph` {ll = ll ∂ rl} s ind treq | ¬∅ x | r = {!!}
  --  trunc≡∅-shrmorph` {ll = call y} s ind treq | ¬∅ x | r = {!!}
  
  
  
  -- data MLFun {i u ll rll pll} (cll : LinLogic i {u}) (ind : IndexLL {i} {u} pll ll) (s : SetLL ll) (lf : LFun {i} {u} ll rll) : Set (lsuc u) where
  --   ∅ :  MLFun cll ind s lf
  --   ¬∅¬∅ : ∀{ts tsind ns nts} → ¬∅ ts ≡ (tranLFMSetLL lf (¬∅ s)) 
  --          → ¬∅ ns ≡ del s ind cll → (ieq : ¬ (contruct ns ≡ ↓)) → ¬∅ tsind ≡ tranLFMSetLL lf (¬∅ (subst (λ x → SetLL x) (replLL-id ll ind pll refl) (∅-add ind pll)))
  --          → let tind = proj₂ (pickOne tsind) in
  ---- Here we can change ll rll on ind tind after the shrink. Thus the shrink process remains the same for the most part.
  --          ¬∅ nts ≡ del ts tind cll → (req : ¬ (contruct nts ≡ ↓)) → LFun (shrink (replLL ll ind cll) ns ieq) (shrink (replLL rll tind cll) nts req) → MLFun cll ind s lf
  --   ¬∅∅ : ∀{ns} → (¬∅ ns ≡ del s ind cll) → (ieq : ¬ (contruct ns ≡ ↓)) → ∅ ≡ (tranLFMSetLL lf (¬∅ s)) → LFun (shrink (replLL ll ind cll) ns ieq) rll → MLFun cll ind s lf
  --   -- TODO Maybe change this : This is when ind is not inside the embedded LFun.
  
  
  
  -- data MLFun¬ind {i u ll rll} (s : SetLL ll) (lf : LFun {i} {u} ll rll) : Set (lsuc u) where
  --   ¬∅¬∅ : ∀{ts} → ¬∅ ts ≡ (tranLFMSetLL lf (¬∅ s)) 
  --            → (ieq : ¬ (contruct s ≡ ↓))
  --            → (req : ¬ (contruct ts ≡ ↓)) → LFun (shrink ll s ieq) (shrink rll ts req) → MLFun¬ind s lf
  --   ¬∅∅ : (ieq : ¬ (contruct s ≡ ↓))
  --         → LFun (shrink ll s ieq) rll → MLFun¬ind s lf
  
  
  
  
  --  -- s here does contain the ind.
  --test : ∀{i u rll ll n dt df} → (cll : LinLogic i {u}) → (ind : IndexLL {i} {u} (τ {i} {u} {n} {dt} df) ll) → (s : SetLL ll) → (lf : LFun ll rll) → MLFun cll ind s lf
  --test cll iind s I with mns | inspect mnsx cll where
  --  mns = del s iind cll
  --  mnsx = λ x → del s iind x
  --test cll iind s I | ∅ | nseq = ∅
  --test cll iind s I | ¬∅ x | [ eq ] with isEq (contruct x) ↓
  --test cll iind s I | ¬∅ x | [ eq ] | yes p = ∅
  --test {i} {u} {rll} {ll} {df = df} cll iind s I | ¬∅ ns | [ eqns ] | no ¬p = ¬∅¬∅ {ts = s} {tsind = tsind} refl (sym eqns) ¬p refl (proj₁ $ proj₂ hf) (proj₁ $ proj₂ $ proj₂ hf) (proj₂ $ proj₂ $ proj₂ hf)  where
  --  pll = τ df
  --  tsind = (subst (λ x → SetLL x) (replLL-id ll iind pll refl) (∅-add iind pll))
  --  tindf = (pickOne tsind)
  --  tind = proj₂ tindf
  --  hf : Σ (SetLL (replLL rll tind cll)) (λ nts
  --       → (¬∅ nts ≡ del s tind cll) × (Σ (¬ (contruct nts ≡ ↓)) (λ req →
  --           LFun (shrink (replLL ll iind cll) ns ¬p) (shrink (replLL rll tind cll) nts req))))
  --  hf with tindf | pickadd-id iind
  --  hf | .(_ , _) | refl = (ns , sym eqns , ¬p , I)
  --test {i} {u} {rll} {ll} {df = df} cll iind s (_⊂_ {ind = ind} lf lf₁) with isLTi ind iind 
  --... | yes le = {!!}
  --... | no ¬le with isLTi iind ind
  --... | yes ge = ⊥-elim (indτ⇒¬le iind ind ¬le ge) 
  --... | no ¬ge = {!!}
  --test cll iind s (tr ltr lf) = {!!}
  --test cll iind s (com df lf) = {!!}
  --test cll iind s (call x) = {!!}
  
  
  
  
  
  
  -- --shrLF : ∀{i u rll ll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → (lf : LFun ll rll) → MLFun¬ind s lf
  -- --shrLF s eq I = ¬∅¬∅ refl eq eq I
  -- --shrLF {rll = rll} s eq (_⊂_ {ell = ell} {ind = ind} lf lf₁) with truncSetLL s ind | inspect (λ x → truncSetLL s x) ind
  -- --... | ¬∅ x | g = {!!}
  -- --... | ∅ | [ eq₁ ] with mrp | inspect mrpx ind where
  -- --mrp = mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at ind
  -- --mrpx = λ x → mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at x
  -- --... | ∅ | [ eq₂ ] = ⊥-elim ((trunc≡∅⇒¬mrpls≡∅ s ind eq₁) eq₂)
  -- --... | ¬∅ x | [ eq₂ ] with shrLF x xc lf₁ where
  -- --xc = ¬contr≡↓⇒¬contrdel≡↓ s eq ind eq₂
  -- --... | ¬∅¬∅ tseq ieq req slf₁ = ¬∅¬∅ {!!} eq {!!} (_⊂_ {ind = {!!}} lf slf₁) where
  -- --ts = tranLFMSetLL (_⊂_ {ind = ind} lf lf₁) (¬∅ s)
  -- --w = {!ts!}
  -- --... | ¬∅∅ ieq x₁ = {!!}
  -- ----     srlF = shrLF lf
  -- ----     srlF = shrLF (truncSetLL s ind ? ?) lf
  -- --shrLF s eq (tr ltr lf) = {!!}
  -- --shrLF s eq (com df lf) = {!!}
  -- --shrLF s eq (call x) = {!!}
  -- --
  
  -- ---- s here does contain the ind.
  -- --test : ∀{i u pll rll ll} → (cll : LinLogic i {u}) → (ind : IndexLL {i} {u} pll ll) → (s : SetLL ll) → (lf : LFun ll rll) → MLFun cll ind s lf
  -- --test cll iind s I with mns | inspect mnsx cll where
  -- --  mns = del s iind cll
  -- --  mnsx = λ x → del s iind x
  -- --test cll iind s I | ∅ | nseq = ∅
  -- --test cll iind s I | ¬∅ x | [ eq ] with isEq (contruct x) ↓
  -- --test cll iind s I | ¬∅ x | [ eq ] | yes p = ∅
  -- --test cll iind s I | ¬∅ x | [ eq ] | no ¬p with mts | inspect mtsx s where
  -- --  mts = tranLFMSetLL I (¬∅ s)
  -- --  mtsx =  λ x → tranLFMSetLL I (¬∅ x)
  -- --test cll iind s I | ¬∅ x | [ eq ] | no ¬p | ∅ | [ () ]
  -- --test {pll = pll} {ll = ll} cll iind s I | ¬∅ x₁ | [ eq ] | no ¬p | ¬∅ x | [ eq₁ ] with mtsind | inspect mtsindx I  where
  -- --  mtsind = tranLFMSetLL I (¬∅ (subst (λ x → SetLL x) (replLL-id ll iind pll refl) (∅-add iind pll)))
  -- --  mtsindx = λ y → tranLFMSetLL y (¬∅ (subst (λ x → SetLL x) (replLL-id ll iind pll refl) (∅-add iind pll)))
  -- --test cll iind s I | ¬∅ x₁ | [ eq ] | no ¬p | ¬∅ x | [ eq₁ ] | ∅ | g = ∅ where
  -- --test cll iind s I | ¬∅ ns | [ eqns ] | no ¬p | ¬∅ ts | [ eqts ] | ¬∅ tsind | [ eqtsind ] with mnts | inspect mntsx cll where
  -- --  tind = proj₂ (pickOne tsind)
  -- --  mnts = del ts tind cll
  -- --  mntsx = del ts tind
  -- --  w = {!!}
  -- --test cll iind s I | ¬∅ ns | [ eqns ] | no ¬p | ¬∅ ts | [ eqts ] | ¬∅ tsind | [ eqtsind ] | ∅ | g = ∅
  -- --test cll iind s I | ¬∅ ns | [ eqns ] | no ¬p | ¬∅ ts | [ eqts ] | ¬∅ tsind | [ eqtsind ] | ¬∅ nts | [ eqnts ] with isEq (contruct nts) ↓
  -- --test cll iind s I | ¬∅ ns | [ eqns ] | no ¬p | ¬∅ ts | [ eqts ] | ¬∅ tsind | [ eqtsind ] | ¬∅ nts | [ eqnts ] | yes cnts = ∅
  -- --test {rll = rll} cll iind s I | ¬∅ ns | [ eqns ] | no ¬p | ¬∅ ts | [ eqts ] | ¬∅ tsind | [ eqtsind ] | ¬∅ nts | [ eqnts ] | no ¬cnts = {!!} where -- ¬∅¬∅ (sym eqts) (sym eqns) ¬p eqtsind (sym eqnts) ¬cnts {!!} where
  -- --  tind = proj₂ (pickOne tsind)
  -- --  g : LFun
  -- --        (shrink (replLL rll iind cll) ns ¬p) 
  -- --        (shrink (replLL rll tind cll) nts ¬cnts)
  -- --  g = {!!}
  -- --test cll iind s (lf ⊂ lf₁) = {!!}
  -- --test cll iind s (tr ltr lf) = {!!}
  -- --test cll iind s (com df lf) = {!!}
  -- --test cll iind s (call x) = {!!}
  -- --
  
