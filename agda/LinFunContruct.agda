{-# OPTIONS --exact-split #-}
-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS --show-irrelevant #-}

module LinFunContruct where

open import Common
open import LinLogic
open import IndexLLProp
open import LinFun
open import SetLL
open import SetLLProp

open import Relation.Binary.PropositionalEquality
open import Data.Product

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
¬ho-shr-morph {cs = cs} (s ←∧) ceq (ind ←∧) ¬ho | ¬∅ x | [ eq ]
                                           with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∧←∧ x)
¬ho-shr-morph {cs = .(x ←∧→ fillAllLower _)} (s ←∧) refl (ind ←∧) ¬ho | ¬∅ x | [ eq ] | r = r ←∧
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
¬ho-shr-morph {cs = cs} (∧→ s) ceq (∧→ ind) ¬ho | ¬∅ x | [ eq ]
                                             with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce∧→∧→ x)
¬ho-shr-morph {cs = .(fillAllLower _ ←∧→ x)} (∧→ s) refl (∧→ ind) ¬ho | ¬∅ x | [ eq ] | r = ∧→ r
¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce←∧→↓)
¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (ind ←∧) ¬ho with complLₛ s | inspect complLₛ s | complLₛ s₁
¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (ind ←∧) ¬ho | ∅ | [ eq ] | e
             =  ⊥-elim (¬nho (compl≡∅⇒ho s eq ind))  where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∧→←∧ x)
¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (ind ←∧) ¬ho | ¬∅ x | [ eq ] | ∅
             with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∧→←∧ x)
¬ho-shr-morph {cs = .(x ←∧)} (s ←∧→ s₁) refl (ind ←∧) ¬ho | ¬∅ x | [ eq ] | ∅ | r
             = r
¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (ind ←∧) ¬ho | ¬∅ x | [ eq ] | ¬∅ x₁
             with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∧→←∧ x)
¬ho-shr-morph {cs = .(x ←∧→ x₁)} (s ←∧→ s₁) refl (ind ←∧) ¬ho | ¬∅ x | [ eq ] | ¬∅ x₁ | r
             = r ←∧
¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (∧→ ind) ¬ho with complLₛ s | complLₛ s₁ | inspect complLₛ s₁
¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (∧→ ind) ¬ho | r | ∅ | [ eq ]  
             =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ eq ind))  where
  ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ x)
¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (∧→ ind) ¬ho | ∅ | ¬∅ x | [ eq ]
             with ¬ho-shr-morph s₁ eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ x)
¬ho-shr-morph {cs = .(∧→ x)} (s ←∧→ s₁) refl (∧→ ind) ¬ho | ∅ | ¬∅ x | [ eq ] | r = r
¬ho-shr-morph {cs = cs} (s ←∧→ s₁) ceq (∧→ ind) ¬ho | ¬∅ x | ¬∅ x₁ | [ eq ]
             with ¬ho-shr-morph s₁ eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ x)
¬ho-shr-morph {cs = .(x ←∧→ x₁)} (s ←∧→ s₁) refl (∧→ ind) ¬ho | ¬∅ x | ¬∅ x₁ | [ eq ] | r = ∧→ r
¬ho-shr-morph {cs = cs} (s ←∨) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce←∨↓)
¬ho-shr-morph {cs = cs} (s ←∨) ceq (ind ←∨) ¬ho with complLₛ s | inspect complLₛ s
¬ho-shr-morph {cs = cs} (s ←∨) ceq (ind ←∨) ¬ho | ∅ | [ eq ]
                                        =  ⊥-elim (¬nho (compl≡∅⇒ho s eq ind))  where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∨←∨ x)
¬ho-shr-morph {cs = cs} (s ←∨) ceq (ind ←∨) ¬ho | ¬∅ x | [ eq ]
                                           with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∨←∨ x)
¬ho-shr-morph {cs = .(x ←∨→ fillAllLower _)} (s ←∨) refl (ind ←∨) ¬ho | ¬∅ x | [ eq ] | r = r ←∨
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
¬ho-shr-morph {cs = cs} (∨→ s) ceq (∨→ ind) ¬ho | ¬∅ x | [ eq ]
                                             with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce∨→∨→ x)
¬ho-shr-morph {cs = .(fillAllLower _ ←∨→ x)} (∨→ s) refl (∨→ ind) ¬ho | ¬∅ x | [ eq ] | r = ∨→ r
¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce←∨→↓)
¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (ind ←∨) ¬ho with complLₛ s | inspect complLₛ s | complLₛ s₁
¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (ind ←∨) ¬ho | ∅ | [ eq ] | e
             =  ⊥-elim (¬nho (compl≡∅⇒ho s eq ind))  where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∨→←∨ x)
¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (ind ←∨) ¬ho | ¬∅ x | [ eq ] | ∅
             with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∨→←∨ x)
¬ho-shr-morph {cs = .(x ←∨)} (s ←∨→ s₁) refl (ind ←∨) ¬ho | ¬∅ x | [ eq ] | ∅ | r
             = r
¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (ind ←∨) ¬ho | ¬∅ x | [ eq ] | ¬∅ x₁
             with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∨→←∨ x)
¬ho-shr-morph {cs = .(x ←∨→ x₁)} (s ←∨→ s₁) refl (ind ←∨) ¬ho | ¬∅ x | [ eq ] | ¬∅ x₁ | r
             = r ←∨
¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (∨→ ind) ¬ho with complLₛ s | complLₛ s₁ | inspect complLₛ s₁
¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (∨→ ind) ¬ho | r | ∅ | [ eq ]  
             =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ eq ind))  where
  ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ x)
¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (∨→ ind) ¬ho | ∅ | ¬∅ x | [ eq ]
             with ¬ho-shr-morph s₁ eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ x)
¬ho-shr-morph {cs = .(∨→ x)} (s ←∨→ s₁) refl (∨→ ind) ¬ho | ∅ | ¬∅ x | [ eq ] | r = r
¬ho-shr-morph {cs = cs} (s ←∨→ s₁) ceq (∨→ ind) ¬ho | ¬∅ x | ¬∅ x₁ | [ eq ]
             with ¬ho-shr-morph s₁ eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ x)
¬ho-shr-morph {cs = .(x ←∨→ x₁)} (s ←∨→ s₁) refl (∨→ ind) ¬ho | ¬∅ x | ¬∅ x₁ | [ eq ] | r = ∨→ r
¬ho-shr-morph {cs = cs} (s ←∂) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce←∂↓)
¬ho-shr-morph {cs = cs} (s ←∂) ceq (ind ←∂) ¬ho with complLₛ s | inspect complLₛ s
¬ho-shr-morph {cs = cs} (s ←∂) ceq (ind ←∂) ¬ho | ∅ | [ eq ]
                                        =  ⊥-elim (¬nho (compl≡∅⇒ho s eq ind))  where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∂←∂ x)
¬ho-shr-morph {cs = cs} (s ←∂) ceq (ind ←∂) ¬ho | ¬∅ x | [ eq ]
                                           with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∂←∂ x)
¬ho-shr-morph {cs = .(x ←∂→ fillAllLower _)} (s ←∂) refl (ind ←∂) ¬ho | ¬∅ x | [ eq ] | r = r ←∂
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
¬ho-shr-morph {cs = cs} (∂→ s) ceq (∂→ ind) ¬ho | ¬∅ x | [ eq ]
                                             with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce∂→∂→ x)
¬ho-shr-morph {cs = .(fillAllLower _ ←∂→ x)} (∂→ s) refl (∂→ ind) ¬ho | ¬∅ x | [ eq ] | r = ∂→ r
¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq ↓ ¬ho = ⊥-elim (¬ho hitsAtLeastOnce←∂→↓)
¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (ind ←∂) ¬ho with complLₛ s | inspect complLₛ s | complLₛ s₁
¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (ind ←∂) ¬ho | ∅ | [ eq ] | e
             =  ⊥-elim (¬nho (compl≡∅⇒ho s eq ind))  where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∂→←∂ x)
¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (ind ←∂) ¬ho | ¬∅ x | [ eq ] | ∅
             with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∂→←∂ x)
¬ho-shr-morph {cs = .(x ←∂)} (s ←∂→ s₁) refl (ind ←∂) ¬ho | ¬∅ x | [ eq ] | ∅ | r
             = r
¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (ind ←∂) ¬ho | ¬∅ x | [ eq ] | ¬∅ x₁
             with ¬ho-shr-morph s eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∂→←∂ x)
¬ho-shr-morph {cs = .(x ←∂→ x₁)} (s ←∂→ s₁) refl (ind ←∂) ¬ho | ¬∅ x | [ eq ] | ¬∅ x₁ | r
             = r ←∂
¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (∂→ ind) ¬ho with complLₛ s | complLₛ s₁ | inspect complLₛ s₁
¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (∂→ ind) ¬ho | r | ∅ | [ eq ]  
             =  ⊥-elim (¬nho (compl≡∅⇒ho s₁ eq ind))  where
  ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ x)
¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (∂→ ind) ¬ho | ∅ | ¬∅ x | [ eq ]
             with ¬ho-shr-morph s₁ eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ x)
¬ho-shr-morph {cs = .(∂→ x)} (s ←∂→ s₁) refl (∂→ ind) ¬ho | ∅ | ¬∅ x | [ eq ] | r = r
¬ho-shr-morph {cs = cs} (s ←∂→ s₁) ceq (∂→ ind) ¬ho | ¬∅ x | ¬∅ x₁ | [ eq ]
             with ¬ho-shr-morph s₁ eq ind ¬nho where
  ¬nho : ¬ (hitsAtLeastOnce s₁ ind)
  ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ x)
¬ho-shr-morph {cs = .(x ←∂→ x₁)} (s ←∂→ s₁) refl (∂→ ind) ¬ho | ¬∅ x | ¬∅ x₁ | [ eq ] | r = ∂→ r



--shrink : ∀{i u} → ∀ ll → (s : SetLL {i} {u} ll) → ¬ ((contruct s) ≡ ↓) → LinLogic i {u}
--shrink ll s eq with complLₛ s | ¬contruct↓⇒¬compl∅ s eq
--shrink ll s eq | ∅ | e = ⊥-elim (e refl)
--shrink ll s eq | ¬∅ x | e = shrink` ll x where
--  shrink` : ∀{i u} → ∀ ll → SetLL {i} {u} ll → LinLogic i {u}
--  shrink` ∅ ↓ = ∅
--  shrink` (τ x) ↓ = τ x
--  shrink` (li ∧ ri) ↓ = li ∧ ri
--  shrink` (li ∧ ri) (s ←∧) = (shrink` li s)
--  shrink` (li ∧ ri) (∧→ s) = (shrink` ri s)
--  shrink` (li ∧ ri) (s ←∧→ s₁) = (shrink` li s) ∧ (shrink` ri s₁)
--  shrink` (li ∨ ri) ↓ = li ∨ ri
--  shrink` (li ∨ ri) (s ←∨) = (shrink` li s)
--  shrink` (li ∨ ri) (∨→ s) = (shrink` ri s)
--  shrink` (li ∨ ri) (s ←∨→ s₁) = (shrink` li s) ∨ (shrink` ri s₁)
--  shrink` (li ∂ ri) ↓ = li ∂ ri
--  shrink` (li ∂ ri) (s ←∂) = (shrink` li s)
--  shrink` (li ∂ ri) (∂→ s) = (shrink` ri s)
--  shrink` (li ∂ ri) (s ←∂→ s₁) = (shrink` li s) ∂ (shrink` ri s₁)
--  shrink` (call x) ↓ = call x
--


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
