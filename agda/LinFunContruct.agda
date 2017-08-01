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
  ... | ¬∅ ncs | [ nceq ] with shrink-repl-comm s lind qeq teq deq nceq 
  shrink-repl-comm {ll = _ ∧ rs} {ell = ell} (s ←∧) (lind ←∧) refl teq {.nmx ←∧} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | r = cong (λ z → z ∧ (shrink rs (fillAllLower rs))) r
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
  ... | ¬∅ ncs | [ nceq ] with shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∧ _} {ell} (∧→ s) (∧→ lind) refl teq {∧→ .nmx} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | r = cong (λ z → (shrink ls (fillAllLower ls)) ∧ z) r
  shrink-repl-comm {u = _} {ls ∧ _} {ell} (∧→ s) (∧→ lind) eq teq {mx ←∧→ mx₁} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ll = ls ∧ rs} {ell} (s ←∧→ s₁) ↓ eq teq meq ceq = ⊥-elim (¬ho hitsAtLeastOnce←∧→↓) where
    ¬ho = trunc≡∅⇒¬ho (s ←∧→ s₁) ↓ teq
  shrink-repl-comm {ll = ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) eq teq meq ceq  with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) eq teq meq ceq | ∅ | [ qeq ] | e | _ = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl () | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl refl | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x = ⊥-elim ((del⇒¬ho s lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))) 
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl refl | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ¬∅ x₁ | [ nceq ] | ¬∅ x = cong (λ z → z ∧ (shrink rs x)) r where
    r = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | eeq with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | eeq | ¬∅ nmx | [ deq ]  with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl refl | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ∅ = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ¬∅ x
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl () | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (lind ←∧) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x
  shrink-repl-comm {ll = ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) eq teq meq ceq with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) eq teq meq ceq | ∅ | [ qeq ] | e | [ eeq ] =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s₁ lind teq
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl () | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x = ⊥-elim ((del⇒¬ho s₁ lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl refl | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ¬∅ x₁ | [ nceq ] | ¬∅ x = cong (λ z → (shrink ls x) ∧ z) r where
    r = shrink-repl-comm s₁ lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl refl | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ∅ = shrink-repl-comm s₁ lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ¬∅ x
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl () | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∧ rs} {ell} (s ←∧→ s₁) (∧→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x
  shrink-repl-comm (s ←∨) ↓ eq teq meq ceq = ⊥-elim (¬ho hitsAtLeastOnce←∨↓) where
    ¬ho = trunc≡∅⇒¬ho (s ←∨) ↓ teq
  shrink-repl-comm {ll = _ ∨ rs} {ell = ell} (s ←∨) (lind ←∨) eq teq {mx} meq ceq with complLₛ s | inspect complLₛ s | del s lind ell | inspect (del s lind) ell
  ... | ∅ | [ qeq ] | w | t = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {ell = ell} (s ←∨) (lind ←∨) eq teq () ceq | ¬∅ q | [ qeq ] | ∅ | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∨) (lind ←∨) eq teq {↓} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∨) (lind ←∨) eq teq {.nmx ←∨} refl ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  ... | ∅ | [ nceq ] = ⊥-elim (del⇒¬ho s lind (sym deq) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  ... | ¬∅ ncs | [ nceq ] with shrink-repl-comm s lind qeq teq deq nceq 
  shrink-repl-comm {ll = _ ∨ rs} {ell = ell} (s ←∨) (lind ←∨) refl teq {.nmx ←∨} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | r = cong (λ z → z ∨ (shrink rs (fillAllLower rs))) r
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
  ... | ¬∅ ncs | [ nceq ] with shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∨ _} {ell} (∨→ s) (∨→ lind) refl teq {∨→ .nmx} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | r = cong (λ z → (shrink ls (fillAllLower ls)) ∨ z) r
  shrink-repl-comm {u = _} {ls ∨ _} {ell} (∨→ s) (∨→ lind) eq teq {mx ←∨→ mx₁} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ll = ls ∨ rs} {ell} (s ←∨→ s₁) ↓ eq teq meq ceq = ⊥-elim (¬ho hitsAtLeastOnce←∨→↓) where
    ¬ho = trunc≡∅⇒¬ho (s ←∨→ s₁) ↓ teq
  shrink-repl-comm {ll = ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) eq teq meq ceq  with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) eq teq meq ceq | ∅ | [ qeq ] | e | _ = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl () | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl refl | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x = ⊥-elim ((del⇒¬ho s lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))) 
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl refl | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ¬∅ x₁ | [ nceq ] | ¬∅ x = cong (λ z → z ∨ (shrink rs x)) r where
    r = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | eeq with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | eeq | ¬∅ nmx | [ deq ]  with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl refl | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ∅ = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ¬∅ x
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl () | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (lind ←∨) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x
  shrink-repl-comm {ll = ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) eq teq meq ceq with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) eq teq meq ceq | ∅ | [ qeq ] | e | [ eeq ] =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s₁ lind teq
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl () | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x = ⊥-elim ((del⇒¬ho s₁ lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl refl | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ¬∅ x₁ | [ nceq ] | ¬∅ x = cong (λ z → (shrink ls x) ∨ z) r where
    r = shrink-repl-comm s₁ lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl refl | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ∅ = shrink-repl-comm s₁ lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ¬∅ x
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl () | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∨ rs} {ell} (s ←∨→ s₁) (∨→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x
  shrink-repl-comm (s ←∂) ↓ eq teq meq ceq = ⊥-elim (¬ho hitsAtLeastOnce←∂↓) where
    ¬ho = trunc≡∅⇒¬ho (s ←∂) ↓ teq
  shrink-repl-comm {ll = _ ∂ rs} {ell = ell} (s ←∂) (lind ←∂) eq teq {mx} meq ceq with complLₛ s | inspect complLₛ s | del s lind ell | inspect (del s lind) ell
  ... | ∅ | [ qeq ] | w | t = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {ell = ell} (s ←∂) (lind ←∂) eq teq () ceq | ¬∅ q | [ qeq ] | ∅ | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∂) (lind ←∂) eq teq {↓} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ell = ell} (s ←∂) (lind ←∂) eq teq {.nmx ←∂} refl ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  ... | ∅ | [ nceq ] = ⊥-elim (del⇒¬ho s lind (sym deq) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  ... | ¬∅ ncs | [ nceq ] with shrink-repl-comm s lind qeq teq deq nceq 
  shrink-repl-comm {ll = _ ∂ rs} {ell = ell} (s ←∂) (lind ←∂) refl teq {.nmx ←∂} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | r = cong (λ z → z ∂ (shrink rs (fillAllLower rs))) r
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
  ... | ¬∅ ncs | [ nceq ] with shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∂ _} {ell} (∂→ s) (∂→ lind) refl teq {∂→ .nmx} refl refl | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | r = cong (λ z → (shrink ls (fillAllLower ls)) ∂ z) r
  shrink-repl-comm {u = _} {ls ∂ _} {ell} (∂→ s) (∂→ lind) eq teq {mx ←∂→ mx₁} () ceq | ¬∅ q | [ qeq ] | ¬∅ nmx | [ deq ]
  shrink-repl-comm {ll = ls ∂ rs} {ell} (s ←∂→ s₁) ↓ eq teq meq ceq = ⊥-elim (¬ho hitsAtLeastOnce←∂→↓) where
    ¬ho = trunc≡∅⇒¬ho (s ←∂→ s₁) ↓ teq
  shrink-repl-comm {ll = ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) eq teq meq ceq  with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) eq teq meq ceq | ∅ | [ qeq ] | e | _ = ⊥-elim (¬nho (compl≡∅⇒ho s qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s lind teq
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl () | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl refl | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x = ⊥-elim ((del⇒¬ho s lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))) 
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl refl | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ¬∅ x₁ | [ nceq ] | ¬∅ x = cong (λ z → z ∂ (shrink rs x)) r where
    r = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | eeq with del s lind ell | inspect (del s lind) ell
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s lind (trunc≡∅⇒¬ho s lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | eeq | ¬∅ nmx | [ deq ]  with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl refl | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ∅ = shrink-repl-comm s lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ¬∅ x
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s₁
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl () | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (lind ←∂) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x
  shrink-repl-comm {ll = ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) eq teq meq ceq with complLₛ s₁ | inspect complLₛ s₁ | complLₛ s | inspect complLₛ s
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) eq teq meq ceq | ∅ | [ qeq ] | e | [ eeq ] =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ qeq lind)) where
    ¬nho = trunc≡∅⇒¬ho s₁ lind teq
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ∅ | [ deq ] =  ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl () | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x = ⊥-elim ((del⇒¬ho s₁ lind (sym deq)) (compl≡∅⇒ho nmx nceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ¬∅ e | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ x | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl refl | ¬∅ q | [ qeq ] | ¬∅ .x | [ refl ] | ¬∅ nmx | [ deq ] | ¬∅ x₁ | [ nceq ] | ¬∅ x = cong (λ z → (shrink ls x) ∂ z) r where
    r = shrink-repl-comm s₁ lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] with del s₁ lind ell | inspect (del s₁ lind) ell
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq meq ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ∅ | [ deq ] = ⊥-elim ((¬ho⇒¬del≡∅ s₁ lind (trunc≡∅⇒¬ho s₁ lind teq)) deq)
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] with complLₛ nmx | inspect complLₛ nmx
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl refl | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ∅ = shrink-repl-comm s₁ lind qeq teq deq nceq
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ¬∅ ncs | [ nceq ] | ¬∅ x
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] with complLₛ s
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl () | ¬∅ q | [ qeq ] | ∅ | [ eeq ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ∅
  shrink-repl-comm {u = _} {ls ∂ rs} {ell} (s ←∂→ s₁) (∂→ lind) refl teq refl ceq | ¬∅ q | [ qeq ] | ∅ | [ () ] | ¬∅ nmx | [ deq ] | ∅ | [ nceq ] | ¬∅ x
   
  
  
  
  
  
  




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
  data STrIr {i u rll} : ∀ {ll} → (s : SetLL {i} {u} ll) → LLTr rll ll → Set where
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
  
