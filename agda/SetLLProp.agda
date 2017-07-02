{-# OPTIONS --exact-split #-}
module SetLLProp where

open import Common
open import LinLogic
open import SetLL
open import IndexLLProp

open import Relation.Binary.PropositionalEquality
import Data.Product



¬contruct↓⇒¬compl∅ : ∀{i u ll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → ¬ (complLₛ s ≡ ∅)
¬contruct↓⇒¬compl∅ ↓ eq = ⊥-elim (eq refl)
¬contruct↓⇒¬compl∅ (s ←∧) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (s ←∧) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∧) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (∧→ s) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (∧→ s) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (∧→ s) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | yes g with contruct s | contruct s₁ 
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes refl | yes refl | .↓ | .↓ = ⊥-elim (eq refl)
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g with ¬contruct↓⇒¬compl∅ s₁ ¬g
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | w | r | ∅ = ⊥-elim (w refl) 
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | w | ∅ | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | w | ¬∅ x | ¬∅ x₁ = λ ()
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g with ¬contruct↓⇒¬compl∅ s ¬p
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g | w | ∅ | e = ⊥-elim (w refl)
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g | w | ¬∅ x | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g | w | ¬∅ x | ¬∅ x₁ = λ ()
¬contruct↓⇒¬compl∅ (s ←∨) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (s ←∨) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∨) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (∨→ s) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (∨→ s) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (∨→ s) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | yes g with contruct s | contruct s₁ 
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes refl | yes refl | .↓ | .↓ = ⊥-elim (eq refl)
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g with ¬contruct↓⇒¬compl∅ s₁ ¬g
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | w | r | ∅ = ⊥-elim (w refl) 
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | w | ∅ | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | w | ¬∅ x | ¬∅ x₁ = λ ()
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g with ¬contruct↓⇒¬compl∅ s ¬p
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g | w | ∅ | e = ⊥-elim (w refl)
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g | w | ¬∅ x | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g | w | ¬∅ x | ¬∅ x₁ = λ ()
¬contruct↓⇒¬compl∅ (s ←∂) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (s ←∂) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∂) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (∂→ s) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (∂→ s) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (∂→ s) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | yes g with contruct s | contruct s₁ 
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes refl | yes refl | .↓ | .↓ = ⊥-elim (eq refl)
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g with ¬contruct↓⇒¬compl∅ s₁ ¬g
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | w | r | ∅ = ⊥-elim (w refl) 
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | w | ∅ | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | w | ¬∅ x | ¬∅ x₁ = λ ()
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g with ¬contruct↓⇒¬compl∅ s ¬p
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g | w | ∅ | e = ⊥-elim (w refl)
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g | w | ¬∅ x | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g | w | ¬∅ x | ¬∅ x₁ = λ ()


module _ where

  open Data.Product
  
  contruct↓⇒compl∅ : ∀{i u ll} → (s : SetLL {i} {u} ll) → (contruct s ≡ ↓) → (complLₛ s ≡ ∅)
  contruct↓⇒compl∅ ↓ eq = refl
  contruct↓⇒compl∅ (s ←∧) ()
  contruct↓⇒compl∅ (∧→ s) ()
  contruct↓⇒compl∅ (s ←∧→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g with complLₛ s | inspect complLₛ s | complLₛ s₁ |  inspect complLₛ s₁
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ∅ | [ eq2 ] = refl
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ¬∅ x | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s₁ g)) eq2
  ... | ()
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g | ¬∅ x | [ eq1 ] | r | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s p)) eq1
  ... | ()
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | no ¬g with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | ↓ | ↓ = ⊥-elim (¬g refl)
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∧
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | ∧→ r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∧→ r₁ 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∨ 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | ∨→ r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∨→ r₁ 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∂ 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | ∂→ r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∂→ r₁ 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∧ | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ∧→ e | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∧→ e₁ | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∨ | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ∨→ e | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∨→ e₁ | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∂ | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ∂→ e | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∂→ e₁ | r 

  contruct↓⇒compl∅ (s ←∧→ s₁) eq | no ¬p | r with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | no ¬p | r | ↓ | w = ⊥-elim (¬p refl)
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∧ | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | ∧→ e | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∧→ e₁ | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∨ | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | ∨→ e | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∨→ e₁ | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∂ | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | ∂→ e | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∂→ e₁ | w 

  contruct↓⇒compl∅ (s ←∨) ()
  contruct↓⇒compl∅ (∨→ s) ()
  contruct↓⇒compl∅ (s ←∨→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g with complLₛ s | inspect complLₛ s | complLₛ s₁ |  inspect complLₛ s₁
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ∅ | [ eq2 ] = refl
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ¬∅ x | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s₁ g)) eq2
  ... | ()
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g | ¬∅ x | [ eq1 ] | r | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s p)) eq1
  ... | ()
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | no ¬g with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | ↓ | ↓ = ⊥-elim (¬g refl)
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∧
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | ∧→ r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∧→ r₁ 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∨ 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | ∨→ r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∨→ r₁ 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∂ 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | ∂→ r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∂→ r₁ 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∧ | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ∧→ e | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∧→ e₁ | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∨ | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ∨→ e | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∨→ e₁ | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∂ | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ∂→ e | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∂→ e₁ | r 

  contruct↓⇒compl∅ (s ←∨→ s₁) eq | no ¬p | r with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | no ¬p | r | ↓ | w = ⊥-elim (¬p refl)
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∧ | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | ∧→ e | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∧→ e₁ | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∨ | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | ∨→ e | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∨→ e₁ | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∂ | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | ∂→ e | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∂→ e₁ | w 

  contruct↓⇒compl∅ (s ←∂) ()
  contruct↓⇒compl∅ (∂→ s) ()
  contruct↓⇒compl∅ (s ←∂→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g with complLₛ s | inspect complLₛ s | complLₛ s₁ |  inspect complLₛ s₁
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ∅ | [ eq2 ] = refl
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ¬∅ x | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s₁ g)) eq2
  ... | ()
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g | ¬∅ x | [ eq1 ] | r | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s p)) eq1
  ... | ()
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | no ¬g with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | ↓ | ↓ = ⊥-elim (¬g refl)
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∧
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | ∧→ r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∧→ r₁ 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∨ 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | ∨→ r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∨→ r₁ 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∂ 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | ∂→ r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∂→ r₁ 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∧ | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ∧→ e | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∧→ e₁ | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∨ | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ∨→ e | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∨→ e₁ | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∂ | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ∂→ e | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∂→ e₁ | r 

  contruct↓⇒compl∅ (s ←∂→ s₁) eq | no ¬p | r with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | no ¬p | r | ↓ | w = ⊥-elim (¬p refl)
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∧ | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | ∧→ e | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∧→ e₁ | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∨ | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | ∨→ e | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∨→ e₁ | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∂ | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | ∂→ e | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∂→ e₁ | w 





  compl∅⇒contruct↓ : ∀{i u ll} → (s : SetLL {i} {u} ll) → (complLₛ s ≡ ∅) → (contruct s ≡ ↓)
  compl∅⇒contruct↓ s eq with isEq (contruct s) ↓
  compl∅⇒contruct↓ s eq | yes p = p
  compl∅⇒contruct↓ s eq | no ¬p = ⊥-elim (¬contruct↓⇒¬compl∅ s ¬p eq)

  ¬compl∅⇒¬contruct↓ : ∀{i u ll} → (s : SetLL {i} {u} ll) → ¬ (complLₛ s ≡ ∅) → ¬ (contruct s ≡ ↓)
  ¬compl∅⇒¬contruct↓ s neq with isEq (contruct s) ↓
  ¬compl∅⇒¬contruct↓ s neq | yes p = ⊥-elim (neq (contruct↓⇒compl∅ s p))
  ¬compl∅⇒¬contruct↓ s neq | no ¬p = ¬p






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




  oi⇒ho : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → onlyInside s ind → hitsAtLeastOnce s ind
  oi⇒ho ↓ ↓ onlyInsideCs↓ = hitsAtLeastOnce↓
  oi⇒ho ↓ (ind ←∧) ()
  oi⇒ho ↓ (∧→ ind) ()
  oi⇒ho ↓ (ind ←∨) ()
  oi⇒ho ↓ (∨→ ind) ()
  oi⇒ho ↓ (ind ←∂) ()
  oi⇒ho ↓ (∂→ ind) ()
  oi⇒ho (s ←∧) ↓ onlyInsideCs↓ = hitsAtLeastOnce←∧↓
  oi⇒ho (s ←∧) (ind ←∧) (onlyInsideC←∧←∧ oi) = hitsAtLeastOnce←∧←∧ (oi⇒ho s ind oi)
  oi⇒ho (s ←∧) (∧→ ind) ()
  oi⇒ho (∧→ s) ↓ oi = hitsAtLeastOnce∧→↓
  oi⇒ho (∧→ s) (ind ←∧) ()
  oi⇒ho (∧→ s) (∧→ ind) (onlyInsideC∧→∧→ x) = hitsAtLeastOnce∧→∧→ (oi⇒ho s ind x)
  oi⇒ho (s ←∧→ s₁) ↓ oi = hitsAtLeastOnce←∧→↓
  oi⇒ho (s ←∧→ s₁) (ind ←∧) ()
  oi⇒ho (s ←∧→ s₁) (∧→ ind) ()
  oi⇒ho (s ←∨) ↓ onlyInsideCs↓ = hitsAtLeastOnce←∨↓
  oi⇒ho (s ←∨) (ind ←∨) (onlyInsideC←∨←∨ oi) = hitsAtLeastOnce←∨←∨ (oi⇒ho s ind oi)
  oi⇒ho (s ←∨) (∨→ ind) ()
  oi⇒ho (∨→ s) ↓ oi = hitsAtLeastOnce∨→↓
  oi⇒ho (∨→ s) (ind ←∨) ()
  oi⇒ho (∨→ s) (∨→ ind) (onlyInsideC∨→∨→ x) = hitsAtLeastOnce∨→∨→ (oi⇒ho s ind x)
  oi⇒ho (s ←∨→ s₁) ↓ oi = hitsAtLeastOnce←∨→↓
  oi⇒ho (s ←∨→ s₁) (ind ←∨) ()
  oi⇒ho (s ←∨→ s₁) (∨→ ind) ()
  oi⇒ho (s ←∂) ↓ onlyInsideCs↓ = hitsAtLeastOnce←∂↓
  oi⇒ho (s ←∂) (ind ←∂) (onlyInsideC←∂←∂ oi) = hitsAtLeastOnce←∂←∂ (oi⇒ho s ind oi)
  oi⇒ho (s ←∂) (∂→ ind) ()
  oi⇒ho (∂→ s) ↓ oi = hitsAtLeastOnce∂→↓
  oi⇒ho (∂→ s) (ind ←∂) ()
  oi⇒ho (∂→ s) (∂→ ind) (onlyInsideC∂→∂→ x) = hitsAtLeastOnce∂→∂→ (oi⇒ho s ind x)
  oi⇒ho (s ←∂→ s₁) ↓ oi = hitsAtLeastOnce←∂→↓
  oi⇒ho (s ←∂→ s₁) (ind ←∂) ()
  oi⇒ho (s ←∂→ s₁) (∂→ ind) ()




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


compl≡∅⇒ho : ∀{i u rll ll} → (s : SetLL {i} {u} ll) → complLₛ s ≡ ∅
                → (ind : IndexLL rll ll) → (hitsAtLeastOnce s ind)
compl≡∅⇒ho ↓ ceq ind = hitsAtLeastOnce↓
compl≡∅⇒ho (s ←∧) ceq ind with complLₛ s
compl≡∅⇒ho (s ←∧) () ind | ∅
compl≡∅⇒ho (s ←∧) () ind | ¬∅ x
compl≡∅⇒ho (∧→ s) ceq ind with complLₛ s
compl≡∅⇒ho (∧→ s) () ind | ∅
compl≡∅⇒ho (∧→ s) () ind | ¬∅ x
compl≡∅⇒ho (s ←∧→ s₁) ceq ind with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
compl≡∅⇒ho (s ←∧→ s₁) ceq ↓ | ∅ | [ eq ] | ∅ | [ eq₁ ] = hitsAtLeastOnce←∧→↓
compl≡∅⇒ho (s ←∧→ s₁) ceq (ind ←∧) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s eq ind
... | r = hitsAtLeastOnce←∧→←∧ r
compl≡∅⇒ho (s ←∧→ s₁) ceq (∧→ ind) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s₁ eq₁ ind
... | r = hitsAtLeastOnce←∧→∧→ r
compl≡∅⇒ho (s ←∧→ s₁) () ind | ∅ | [ eq ] | ¬∅ x | [ eq₁ ]
compl≡∅⇒ho (s ←∧→ s₁) () ind | ¬∅ x | [ eq ] | ∅ | [ eq₁ ]
compl≡∅⇒ho (s ←∧→ s₁) () ind | ¬∅ x | [ eq ] | ¬∅ x₁ | [ eq₁ ]
compl≡∅⇒ho (s ←∨) ceq ind with complLₛ s
compl≡∅⇒ho (s ←∨) () ind | ∅
compl≡∅⇒ho (s ←∨) () ind | ¬∅ x
compl≡∅⇒ho (∨→ s) ceq ind with complLₛ s
compl≡∅⇒ho (∨→ s) () ind | ∅
compl≡∅⇒ho (∨→ s) () ind | ¬∅ x
compl≡∅⇒ho (s ←∨→ s₁) ceq ind with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
compl≡∅⇒ho (s ←∨→ s₁) ceq ↓ | ∅ | [ eq ] | ∅ | [ eq₁ ] = hitsAtLeastOnce←∨→↓
compl≡∅⇒ho (s ←∨→ s₁) ceq (ind ←∨) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s eq ind
... | r = hitsAtLeastOnce←∨→←∨ r
compl≡∅⇒ho (s ←∨→ s₁) ceq (∨→ ind) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s₁ eq₁ ind
... | r = hitsAtLeastOnce←∨→∨→ r
compl≡∅⇒ho (s ←∨→ s₁) () ind | ∅ | [ eq ] | ¬∅ x | [ eq₁ ]
compl≡∅⇒ho (s ←∨→ s₁) () ind | ¬∅ x | [ eq ] | ∅ | [ eq₁ ]
compl≡∅⇒ho (s ←∨→ s₁) () ind | ¬∅ x | [ eq ] | ¬∅ x₁ | [ eq₁ ]
compl≡∅⇒ho (s ←∂) ceq ind with complLₛ s
compl≡∅⇒ho (s ←∂) () ind | ∅
compl≡∅⇒ho (s ←∂) () ind | ¬∅ x
compl≡∅⇒ho (∂→ s) ceq ind with complLₛ s
compl≡∅⇒ho (∂→ s) () ind | ∅
compl≡∅⇒ho (∂→ s) () ind | ¬∅ x
compl≡∅⇒ho (s ←∂→ s₁) ceq ind with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
compl≡∅⇒ho (s ←∂→ s₁) ceq ↓ | ∅ | [ eq ] | ∅ | [ eq₁ ] = hitsAtLeastOnce←∂→↓
compl≡∅⇒ho (s ←∂→ s₁) ceq (ind ←∂) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s eq ind
... | r = hitsAtLeastOnce←∂→←∂ r
compl≡∅⇒ho (s ←∂→ s₁) ceq (∂→ ind) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s₁ eq₁ ind
... | r = hitsAtLeastOnce←∂→∂→ r
compl≡∅⇒ho (s ←∂→ s₁) () ind | ∅ | [ eq ] | ¬∅ x | [ eq₁ ]
compl≡∅⇒ho (s ←∂→ s₁) () ind | ¬∅ x | [ eq ] | ∅ | [ eq₁ ]
compl≡∅⇒ho (s ←∂→ s₁) () ind | ¬∅ x | [ eq ] | ¬∅ x₁ | [ eq₁ ]


module _ where

  open Data.Product

  trunc≡∅⇒¬ho : ∀{i u rll ll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → (truncSetLL s ind ≡ ∅) → ¬ (hitsAtLeastOnce s ind)
  trunc≡∅⇒¬ho s ↓ ()
  trunc≡∅⇒¬ho ↓ (ind ←∧) ()
  trunc≡∅⇒¬ho (s ←∧) (ind ←∧) treq = λ {(hitsAtLeastOnce←∧←∧ x) → is x} where
    is = trunc≡∅⇒¬ho s ind treq
  trunc≡∅⇒¬ho (∧→ s) (ind ←∧) treq = λ ()
  trunc≡∅⇒¬ho (s ←∧→ s₁) (ind ←∧) treq = λ {(hitsAtLeastOnce←∧→←∧ x) → is x} where
    is = trunc≡∅⇒¬ho s ind treq
  trunc≡∅⇒¬ho ↓ (∧→ ind) ()
  trunc≡∅⇒¬ho (s ←∧) (∧→ ind) treq = λ ()
  trunc≡∅⇒¬ho (∧→ s) (∧→ ind) treq = λ {(hitsAtLeastOnce∧→∧→ x) → is x} where
    is = trunc≡∅⇒¬ho s ind treq
  trunc≡∅⇒¬ho (s ←∧→ s₁) (∧→ ind) treq  = λ {(hitsAtLeastOnce←∧→∧→ x) → is x} where
    is = trunc≡∅⇒¬ho s₁ ind treq
  trunc≡∅⇒¬ho ↓ (ind ←∨) ()
  trunc≡∅⇒¬ho (s ←∨) (ind ←∨) treq = λ {(hitsAtLeastOnce←∨←∨ x) → is x} where
    is = trunc≡∅⇒¬ho s ind treq
  trunc≡∅⇒¬ho (∨→ s) (ind ←∨) treq = λ ()
  trunc≡∅⇒¬ho (s ←∨→ s₁) (ind ←∨) treq = λ {(hitsAtLeastOnce←∨→←∨ x) → is x} where
    is = trunc≡∅⇒¬ho s ind treq
  trunc≡∅⇒¬ho ↓ (∨→ ind) ()
  trunc≡∅⇒¬ho (s ←∨) (∨→ ind) treq = λ ()
  trunc≡∅⇒¬ho (∨→ s) (∨→ ind) treq = λ {(hitsAtLeastOnce∨→∨→ x) → is x} where
    is = trunc≡∅⇒¬ho s ind treq
  trunc≡∅⇒¬ho (s ←∨→ s₁) (∨→ ind) treq  = λ {(hitsAtLeastOnce←∨→∨→ x) → is x} where
    is = trunc≡∅⇒¬ho s₁ ind treq
  trunc≡∅⇒¬ho ↓ (ind ←∂) ()
  trunc≡∅⇒¬ho (s ←∂) (ind ←∂) treq = λ {(hitsAtLeastOnce←∂←∂ x) → is x} where
    is = trunc≡∅⇒¬ho s ind treq
  trunc≡∅⇒¬ho (∂→ s) (ind ←∂) treq = λ ()
  trunc≡∅⇒¬ho (s ←∂→ s₁) (ind ←∂) treq = λ {(hitsAtLeastOnce←∂→←∂ x) → is x} where
    is = trunc≡∅⇒¬ho s ind treq
  trunc≡∅⇒¬ho ↓ (∂→ ind) ()
  trunc≡∅⇒¬ho (s ←∂) (∂→ ind) treq = λ ()
  trunc≡∅⇒¬ho (∂→ s) (∂→ ind) treq = λ {(hitsAtLeastOnce∂→∂→ x) → is x} where
    is = trunc≡∅⇒¬ho s ind treq
  trunc≡∅⇒¬ho (s ←∂→ s₁) (∂→ ind) treq  = λ {(hitsAtLeastOnce←∂→∂→ x) → is x} where
    is = trunc≡∅⇒¬ho s₁ ind treq

  ¬ho⇒¬del≡∅ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → ¬(hitsAtLeastOnce s ind) → ¬ (del s ind fll ≡ ∅)
  ¬ho⇒¬del≡∅ ↓ ↓ heq = λ _ → heq hitsAtLeastOnce↓
  ¬ho⇒¬del≡∅ (x ←∧) ↓ heq = λ _ → heq hitsAtLeastOnce←∧↓
  ¬ho⇒¬del≡∅ (∧→ x) ↓ heq = λ _ → heq hitsAtLeastOnce∧→↓
  ¬ho⇒¬del≡∅ (x ←∧→ x₁) ↓ heq = λ _ → heq hitsAtLeastOnce←∧→↓
  ¬ho⇒¬del≡∅ (x ←∨) ↓ heq = λ _ → heq hitsAtLeastOnce←∨↓
  ¬ho⇒¬del≡∅ (∨→ x) ↓ heq = λ _ → heq hitsAtLeastOnce∨→↓
  ¬ho⇒¬del≡∅ (x ←∨→ x₁) ↓ heq = λ _ → heq hitsAtLeastOnce←∨→↓
  ¬ho⇒¬del≡∅ (x ←∂) ↓ heq = λ _ → heq hitsAtLeastOnce←∂↓
  ¬ho⇒¬del≡∅ (∂→ x) ↓ heq = λ _ → heq hitsAtLeastOnce∂→↓
  ¬ho⇒¬del≡∅ (x ←∂→ x₁) ↓ heq = λ _ → heq hitsAtLeastOnce←∂→↓
  ¬ho⇒¬del≡∅ ↓ (ind ←∧) heq = λ _ → heq hitsAtLeastOnce↓
  ¬ho⇒¬del≡∅ {fll = fll} (s ←∧) (ind ←∧) heq with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∧←∧ x) })
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  ¬ho⇒¬del≡∅ (∧→ s) (ind ←∧) heq = λ ()
  ¬ho⇒¬del≡∅ {fll = fll} (s ←∧→ s₁) (ind ←∧) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∧→←∧ x)})
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  ¬ho⇒¬del≡∅ ↓ (∧→ ind) heq = λ _ → heq hitsAtLeastOnce↓
  ¬ho⇒¬del≡∅ (s ←∧) (∧→ ind) heq = λ ()
  ¬ho⇒¬del≡∅ {fll = fll} (∧→ s) (∧→ ind) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce∧→∧→ x) })
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  ¬ho⇒¬del≡∅ {fll = fll} (s ←∧→ s₁) (∧→ ind) heq with del s₁ ind fll | ¬ho⇒¬del≡∅ {fll = fll} s₁ ind (λ {x → heq (hitsAtLeastOnce←∧→∧→ x)})
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  ¬ho⇒¬del≡∅ ↓ (ind ←∨) heq = λ _ → heq hitsAtLeastOnce↓
  ¬ho⇒¬del≡∅ {fll = fll} (s ←∨) (ind ←∨) heq with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∨←∨ x) })
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  ¬ho⇒¬del≡∅ (∨→ s) (ind ←∨) heq = λ ()
  ¬ho⇒¬del≡∅ {fll = fll} (s ←∨→ s₁) (ind ←∨) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∨→←∨ x)})
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  ¬ho⇒¬del≡∅ ↓ (∨→ ind) heq = λ _ → heq hitsAtLeastOnce↓
  ¬ho⇒¬del≡∅ (s ←∨) (∨→ ind) heq = λ ()
  ¬ho⇒¬del≡∅ {fll = fll} (∨→ s) (∨→ ind) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce∨→∨→ x) })
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  ¬ho⇒¬del≡∅ {fll = fll} (s ←∨→ s₁) (∨→ ind) heq with del s₁ ind fll | ¬ho⇒¬del≡∅ {fll = fll} s₁ ind (λ {x → heq (hitsAtLeastOnce←∨→∨→ x)})
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  ¬ho⇒¬del≡∅ ↓ (ind ←∂) heq = λ _ → heq hitsAtLeastOnce↓
  ¬ho⇒¬del≡∅ {fll = fll} (s ←∂) (ind ←∂) heq with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∂←∂ x) })
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  ¬ho⇒¬del≡∅ (∂→ s) (ind ←∂) heq = λ ()
  ¬ho⇒¬del≡∅ {fll = fll} (s ←∂→ s₁) (ind ←∂) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∂→←∂ x)})
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  ¬ho⇒¬del≡∅ ↓ (∂→ ind) heq = λ _ → heq hitsAtLeastOnce↓
  ¬ho⇒¬del≡∅ (s ←∂) (∂→ ind) heq = λ ()
  ¬ho⇒¬del≡∅ {fll = fll} (∂→ s) (∂→ ind) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce∂→∂→ x) })
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  ¬ho⇒¬del≡∅ {fll = fll} (s ←∂→ s₁) (∂→ ind) heq with del s₁ ind fll | ¬ho⇒¬del≡∅ {fll = fll} s₁ ind (λ {x → heq (hitsAtLeastOnce←∂→∂→ x)})
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()


  trunc≡∅⇒¬mrpls≡∅ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → (truncSetLL s ind ≡ ∅) → ¬ (mreplacePartOf (¬∅ s) to (∅ {ll = fll}) at ind ≡ ∅)
  trunc≡∅⇒¬mrpls≡∅ s ind treq = ¬ho⇒¬del≡∅ s ind (trunc≡∅⇒¬ho s ind treq)


  ho⇒¬trunc≡∅ : ∀ {i u ll pll} → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
                 → (prf : hitsAtLeastOnce s ind) → ¬ (truncSetLL s ind ≡ ∅)
  ho⇒¬trunc≡∅ s ind prf x = trunc≡∅⇒¬ho s ind x prf




  oi⇒¬trunc≡∅ : ∀ {i u ll pll} → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
                 → (prf : onlyInside s ind) → ¬ (truncSetLL s ind ≡ ∅)
  oi⇒¬trunc≡∅ s ind prf = ho⇒¬trunc≡∅ s ind (oi⇒ho s ind prf)





-- The ≤s relationship and hitsAtLeastOnce and onlyInside

  oi&ss≤s⇒oiss : ∀ {i u ll pll} → (s ss : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
                 → (oi : onlyInside s ind) → ss ≤s s → onlyInside ss ind
  oi&ss≤s⇒oiss ↓ ss ↓ oi eq = onlyInsideCs↓
  oi&ss≤s⇒oiss ↓ ss (x ←∧) () eq
  oi&ss≤s⇒oiss ↓ ss (∧→ x) () eq
  oi&ss≤s⇒oiss ↓ ss (x ←∨) () eq
  oi&ss≤s⇒oiss ↓ ss (∨→ x) () eq
  oi&ss≤s⇒oiss ↓ ss (x ←∂) () eq
  oi&ss≤s⇒oiss ↓ ss (∂→ x) () eq
  oi&ss≤s⇒oiss (s ←∧) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
  oi&ss≤s⇒oiss (s ←∧) (sx ←∧) (ind ←∧) (onlyInsideC←∧←∧ x) (≤←∧ x₁) = onlyInsideC←∧←∧ (oi&ss≤s⇒oiss s sx ind x x₁)
  oi&ss≤s⇒oiss (∧→ s) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
  oi&ss≤s⇒oiss (∧→ s) (∧→ sx) (∧→ ind) (onlyInsideC∧→∧→ x) (≤∧→ x₁) = onlyInsideC∧→∧→ (oi&ss≤s⇒oiss s sx ind x x₁)
  oi&ss≤s⇒oiss (s ←∧→ s₁) ss ↓ oi eq = onlyInsideCs↓
  oi&ss≤s⇒oiss (s ←∧→ s₁) ss (x ←∧) () eq
  oi&ss≤s⇒oiss (s ←∧→ s₁) ss (∧→ x) () eq
  oi&ss≤s⇒oiss (s ←∨) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
  oi&ss≤s⇒oiss (s ←∨) (sx ←∨) (ind ←∨) (onlyInsideC←∨←∨ x) (≤←∨ x₁) = onlyInsideC←∨←∨ (oi&ss≤s⇒oiss s sx ind x x₁)
  oi&ss≤s⇒oiss (∨→ s) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
  oi&ss≤s⇒oiss (∨→ s) (∨→ sx) (∨→ ind) (onlyInsideC∨→∨→ x) (≤∨→ x₁) = onlyInsideC∨→∨→ (oi&ss≤s⇒oiss s sx ind x x₁)
  oi&ss≤s⇒oiss (s ←∨→ s₁) ss ↓ oi eq = onlyInsideCs↓
  oi&ss≤s⇒oiss (s ←∨→ s₁) ss (x ←∨) () eq
  oi&ss≤s⇒oiss (s ←∨→ s₁) ss (∨→ x) () eq
  oi&ss≤s⇒oiss (s ←∂) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
  oi&ss≤s⇒oiss (s ←∂) (sx ←∂) (ind ←∂) (onlyInsideC←∂←∂ x) (≤←∂ x₁) = onlyInsideC←∂←∂ (oi&ss≤s⇒oiss s sx ind x x₁)
  oi&ss≤s⇒oiss (∂→ s) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
  oi&ss≤s⇒oiss (∂→ s) (∂→ sx) (∂→ ind) (onlyInsideC∂→∂→ x) (≤∂→ x₁) = onlyInsideC∂→∂→ (oi&ss≤s⇒oiss s sx ind x x₁)
  oi&ss≤s⇒oiss (s ←∂→ s₁) ss ↓ oi eq = onlyInsideCs↓
  oi&ss≤s⇒oiss (s ←∂→ s₁) ss (x ←∂) () eq
  oi&ss≤s⇒oiss (s ←∂→ s₁) ss (∂→ x) () eq


  ho&s≤ss⇒hoss : ∀ {i u ll pll} → (s ss : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
                 → (ho : hitsAtLeastOnce s ind) → s ≤s ss → hitsAtLeastOnce ss ind
  ho&s≤ss⇒hoss ↓ ↓ ind ho eq = ho
  ho&s≤ss⇒hoss ↓ (x ←∧) ind ho ()
  ho&s≤ss⇒hoss ↓ (∧→ x) ind ho ()
  ho&s≤ss⇒hoss ↓ (x ←∧→ x₁) ind ho ()
  ho&s≤ss⇒hoss ↓ (x ←∨) ind ho ()
  ho&s≤ss⇒hoss ↓ (∨→ x) ind ho ()
  ho&s≤ss⇒hoss ↓ (x ←∨→ x₁) ind ho ()
  ho&s≤ss⇒hoss ↓ (x ←∂) ind ho ()
  ho&s≤ss⇒hoss ↓ (∂→ x) ind ho ()
  ho&s≤ss⇒hoss ↓ (x ←∂→ x₁) ind ho ()
  ho&s≤ss⇒hoss (s ←∧) ↓ ind ho eq = hitsAtLeastOnce↓
  ho&s≤ss⇒hoss (s ←∧) (x ←∧) .↓ hitsAtLeastOnce←∧↓ eq = hitsAtLeastOnce←∧↓
  ho&s≤ss⇒hoss (s ←∧) (x ←∧) (ind ←∧) (hitsAtLeastOnce←∧←∧ x₁) (≤←∧ x₂) = hitsAtLeastOnce←∧←∧ (ho&s≤ss⇒hoss s x ind x₁ x₂)
  ho&s≤ss⇒hoss (s ←∧) (∧→ ↓) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ ↓) (x ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ ↓) (∧→ x) () eq
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧)) (∧→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∧) (∧→ (∧→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (∧→ x)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (∧→ x)) (∧→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧→ x₁)) (x₂ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧→ x₁)) (∧→ x₂) () eq
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨)) (∧→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∧) (∧→ (∨→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (∨→ x)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (∨→ x)) (∧→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨→ x₁)) (x₂ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨→ x₁)) (∧→ x₂) () eq
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂)) (∧→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∧) (∧→ (∂→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (∂→ x)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (∂→ x)) (∧→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂→ x₁)) (x₂ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂→ x₁)) (∧→ x₂) () eq
  ho&s≤ss⇒hoss (s ←∧) (x ←∧→ x₁) .↓ hitsAtLeastOnce←∧↓ eq = hitsAtLeastOnce←∧→↓
  ho&s≤ss⇒hoss (s ←∧) (x ←∧→ x₁) (ind ←∧) (hitsAtLeastOnce←∧←∧ x₂) (≤d←∧ x₃) = hitsAtLeastOnce←∧→←∧ (ho&s≤ss⇒hoss s x ind x₂ x₃)
  ho&s≤ss⇒hoss (∧→ s) ↓ ind ho eq = hitsAtLeastOnce↓
  ho&s≤ss⇒hoss (∧→ s) (↓ ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (∧→ s) (↓ ←∧) (x ←∧) () eq
  ho&s≤ss⇒hoss (∧→ s) (↓ ←∧) (∧→ x) ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∧) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∧) ←∧) (x₁ ←∧) () eq
  ho&s≤ss⇒hoss (∧→ s) ((x ←∧) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (∧→ s) ((∧→ x) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (∧→ s) ((∧→ x) ←∧) (x₁ ←∧) () eq
  ho&s≤ss⇒hoss (∧→ s) ((∧→ x) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∧→ x₁) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∧→ x₁) ←∧) (x₂ ←∧) () eq
  ho&s≤ss⇒hoss (∧→ s) ((x ←∧→ x₁) ←∧) (∧→ x₂) ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∨) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∨) ←∧) (x₁ ←∧) () eq
  ho&s≤ss⇒hoss (∧→ s) ((x ←∨) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (∧→ s) ((∨→ x) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (∧→ s) ((∨→ x) ←∧) (x₁ ←∧) () eq
  ho&s≤ss⇒hoss (∧→ s) ((∨→ x) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∨→ x₁) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∨→ x₁) ←∧) (x₂ ←∧) () eq
  ho&s≤ss⇒hoss (∧→ s) ((x ←∨→ x₁) ←∧) (∧→ x₂) ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∂) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∂) ←∧) (x₁ ←∧) () eq
  ho&s≤ss⇒hoss (∧→ s) ((x ←∂) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (∧→ s) ((∂→ x) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (∧→ s) ((∂→ x) ←∧) (x₁ ←∧) () eq
  ho&s≤ss⇒hoss (∧→ s) ((∂→ x) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∂→ x₁) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (∧→ s) ((x ←∂→ x₁) ←∧) (x₂ ←∧) () eq
  ho&s≤ss⇒hoss (∧→ s) ((x ←∂→ x₁) ←∧) (∧→ x₂) ho ()
  ho&s≤ss⇒hoss (∧→ s) (∧→ x) .↓ hitsAtLeastOnce∧→↓ eq = hitsAtLeastOnce∧→↓
  ho&s≤ss⇒hoss (∧→ s) (∧→ x) (∧→ ind) (hitsAtLeastOnce∧→∧→ x₁) (≤∧→ x₂) = hitsAtLeastOnce∧→∧→ (ho&s≤ss⇒hoss s x ind x₁ x₂)
  ho&s≤ss⇒hoss (∧→ s) (x ←∧→ x₁) .↓ hitsAtLeastOnce∧→↓ eq = hitsAtLeastOnce←∧→↓
  ho&s≤ss⇒hoss (∧→ s) (x ←∧→ x₁) (∧→ ind) (hitsAtLeastOnce∧→∧→ x₂) (≤d∧→ x₃) = hitsAtLeastOnce←∧→∧→ (ho&s≤ss⇒hoss s x₁ ind x₂ x₃)
  ho&s≤ss⇒hoss (s ←∧→ s₁) ↓ ind ho eq = hitsAtLeastOnce↓
  ho&s≤ss⇒hoss (s ←∧→ s₁) (↓ ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (↓ ←∧) (x ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (↓ ←∧) (∧→ x) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧) ←∧) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((∧→ x) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((∧→ x) ←∧) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((∧→ x) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧→ x₁) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧→ x₁) ←∧) (x₂ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧→ x₁) ←∧) (∧→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨) ←∧) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((∨→ x) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((∨→ x) ←∧) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((∨→ x) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨→ x₁) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨→ x₁) ←∧) (x₂ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨→ x₁) ←∧) (∧→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂) ←∧) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((∂→ x) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((∂→ x) ←∧) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((∂→ x) ←∧) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂→ x₁) ←∧) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂→ x₁) ←∧) (x₂ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂→ x₁) ←∧) (∧→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ ↓) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ ↓) (x ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ ↓) (∧→ x) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧)) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∧→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∧→ x)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∧→ x)) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧→ x₁)) (x₂ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧→ x₁)) (∧→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨)) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∨→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∨→ x)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∨→ x)) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨→ x₁)) (x₂ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨→ x₁)) (∧→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂)) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∂→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∂→ x)) (x₁ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∂→ x)) (∧→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂→ x₁)) (x₂ ←∧) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂→ x₁)) (∧→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∧→ s₁) (x ←∧→ x₁) .↓ hitsAtLeastOnce←∧→↓ eq = hitsAtLeastOnce←∧→↓
  ho&s≤ss⇒hoss (s ←∧→ s₁) (x ←∧→ x₁) (ind ←∧) (hitsAtLeastOnce←∧→←∧ x₂) (≤←∧→ x₃ x₄) = hitsAtLeastOnce←∧→←∧ (ho&s≤ss⇒hoss s x ind x₂ x₃)
  ho&s≤ss⇒hoss (s ←∧→ s₁) (x ←∧→ x₁) (∧→ ind) (hitsAtLeastOnce←∧→∧→ x₂) (≤←∧→ x₃ x₄) = hitsAtLeastOnce←∧→∧→ (ho&s≤ss⇒hoss s₁ x₁ ind x₂ x₄)
  ho&s≤ss⇒hoss (s ←∨) ↓ ind ho eq = hitsAtLeastOnce↓
  ho&s≤ss⇒hoss (s ←∨) (x ←∨) .↓ hitsAtLeastOnce←∨↓ eq = hitsAtLeastOnce←∨↓
  ho&s≤ss⇒hoss (s ←∨) (x ←∨) (ind ←∨) (hitsAtLeastOnce←∨←∨ x₁) (≤←∨ x₂) = hitsAtLeastOnce←∨←∨ (ho&s≤ss⇒hoss s x ind x₁ x₂)
  ho&s≤ss⇒hoss (s ←∨) (∨→ ↓) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ ↓) (x ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ ↓) (∨→ x) () eq
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨)) (∨→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∨) (∨→ (∨→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (∨→ x)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (∨→ x)) (∨→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨→ x₁)) (x₂ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨→ x₁)) (∨→ x₂) () eq
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧)) (∨→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∨) (∨→ (∧→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (∧→ x)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (∧→ x)) (∨→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧→ x₁)) (x₂ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧→ x₁)) (∨→ x₂) () eq
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂)) (∨→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∨) (∨→ (∂→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (∂→ x)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (∂→ x)) (∨→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂→ x₁)) (x₂ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂→ x₁)) (∨→ x₂) () eq
  ho&s≤ss⇒hoss (s ←∨) (x ←∨→ x₁) .↓ hitsAtLeastOnce←∨↓ eq = hitsAtLeastOnce←∨→↓
  ho&s≤ss⇒hoss (s ←∨) (x ←∨→ x₁) (ind ←∨) (hitsAtLeastOnce←∨←∨ x₂) (≤d←∨ x₃) = hitsAtLeastOnce←∨→←∨ (ho&s≤ss⇒hoss s x ind x₂ x₃)
  ho&s≤ss⇒hoss (∨→ s) ↓ ind ho eq = hitsAtLeastOnce↓
  ho&s≤ss⇒hoss (∨→ s) (↓ ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (∨→ s) (↓ ←∨) (x ←∨) () eq
  ho&s≤ss⇒hoss (∨→ s) (↓ ←∨) (∨→ x) ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∨) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∨) ←∨) (x₁ ←∨) () eq
  ho&s≤ss⇒hoss (∨→ s) ((x ←∨) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (∨→ s) ((∨→ x) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (∨→ s) ((∨→ x) ←∨) (x₁ ←∨) () eq
  ho&s≤ss⇒hoss (∨→ s) ((∨→ x) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∨→ x₁) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∨→ x₁) ←∨) (x₂ ←∨) () eq
  ho&s≤ss⇒hoss (∨→ s) ((x ←∨→ x₁) ←∨) (∨→ x₂) ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∧) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∧) ←∨) (x₁ ←∨) () eq
  ho&s≤ss⇒hoss (∨→ s) ((x ←∧) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (∨→ s) ((∧→ x) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (∨→ s) ((∧→ x) ←∨) (x₁ ←∨) () eq
  ho&s≤ss⇒hoss (∨→ s) ((∧→ x) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∧→ x₁) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∧→ x₁) ←∨) (x₂ ←∨) () eq
  ho&s≤ss⇒hoss (∨→ s) ((x ←∧→ x₁) ←∨) (∨→ x₂) ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∂) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∂) ←∨) (x₁ ←∨) () eq
  ho&s≤ss⇒hoss (∨→ s) ((x ←∂) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (∨→ s) ((∂→ x) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (∨→ s) ((∂→ x) ←∨) (x₁ ←∨) () eq
  ho&s≤ss⇒hoss (∨→ s) ((∂→ x) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∂→ x₁) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (∨→ s) ((x ←∂→ x₁) ←∨) (x₂ ←∨) () eq
  ho&s≤ss⇒hoss (∨→ s) ((x ←∂→ x₁) ←∨) (∨→ x₂) ho ()
  ho&s≤ss⇒hoss (∨→ s) (∨→ x) .↓ hitsAtLeastOnce∨→↓ eq = hitsAtLeastOnce∨→↓
  ho&s≤ss⇒hoss (∨→ s) (∨→ x) (∨→ ind) (hitsAtLeastOnce∨→∨→ x₁) (≤∨→ x₂) = hitsAtLeastOnce∨→∨→ (ho&s≤ss⇒hoss s x ind x₁ x₂)
  ho&s≤ss⇒hoss (∨→ s) (x ←∨→ x₁) .↓ hitsAtLeastOnce∨→↓ eq = hitsAtLeastOnce←∨→↓
  ho&s≤ss⇒hoss (∨→ s) (x ←∨→ x₁) (∨→ ind) (hitsAtLeastOnce∨→∨→ x₂) (≤d∨→ x₃) = hitsAtLeastOnce←∨→∨→ (ho&s≤ss⇒hoss s x₁ ind x₂ x₃)
  ho&s≤ss⇒hoss (s ←∨→ s₁) ↓ ind ho eq = hitsAtLeastOnce↓
  ho&s≤ss⇒hoss (s ←∨→ s₁) (↓ ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (↓ ←∨) (x ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (↓ ←∨) (∨→ x) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨) ←∨) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((∨→ x) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((∨→ x) ←∨) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((∨→ x) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨→ x₁) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨→ x₁) ←∨) (x₂ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨→ x₁) ←∨) (∨→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧) ←∨) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((∧→ x) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((∧→ x) ←∨) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((∧→ x) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧→ x₁) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧→ x₁) ←∨) (x₂ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧→ x₁) ←∨) (∨→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂) ←∨) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((∂→ x) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((∂→ x) ←∨) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((∂→ x) ←∨) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂→ x₁) ←∨) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂→ x₁) ←∨) (x₂ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂→ x₁) ←∨) (∨→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ ↓) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ ↓) (x ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ ↓) (∨→ x) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨)) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∨→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∨→ x)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∨→ x)) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨→ x₁)) (x₂ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨→ x₁)) (∨→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧)) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∧→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∧→ x)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∧→ x)) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧→ x₁)) (x₂ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧→ x₁)) (∨→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂)) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∂→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∂→ x)) (x₁ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∂→ x)) (∨→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂→ x₁)) (x₂ ←∨) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂→ x₁)) (∨→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∨→ s₁) (x ←∨→ x₁) .↓ hitsAtLeastOnce←∨→↓ eq = hitsAtLeastOnce←∨→↓
  ho&s≤ss⇒hoss (s ←∨→ s₁) (x ←∨→ x₁) (ind ←∨) (hitsAtLeastOnce←∨→←∨ x₂) (≤←∨→ x₃ x₄) = hitsAtLeastOnce←∨→←∨ (ho&s≤ss⇒hoss s x ind x₂ x₃)
  ho&s≤ss⇒hoss (s ←∨→ s₁) (x ←∨→ x₁) (∨→ ind) (hitsAtLeastOnce←∨→∨→ x₂) (≤←∨→ x₃ x₄) = hitsAtLeastOnce←∨→∨→ (ho&s≤ss⇒hoss s₁ x₁ ind x₂ x₄)
  ho&s≤ss⇒hoss (s ←∂) ↓ ind ho eq = hitsAtLeastOnce↓
  ho&s≤ss⇒hoss (s ←∂) (x ←∂) .↓ hitsAtLeastOnce←∂↓ eq = hitsAtLeastOnce←∂↓
  ho&s≤ss⇒hoss (s ←∂) (x ←∂) (ind ←∂) (hitsAtLeastOnce←∂←∂ x₁) (≤←∂ x₂) = hitsAtLeastOnce←∂←∂ (ho&s≤ss⇒hoss s x ind x₁ x₂)
  ho&s≤ss⇒hoss (s ←∂) (∂→ ↓) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ ↓) (x ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ ↓) (∂→ x) () eq
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂)) (∂→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∂) (∂→ (∂→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (∂→ x)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (∂→ x)) (∂→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂→ x₁)) (x₂ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂→ x₁)) (∂→ x₂) () eq
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨)) (∂→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∂) (∂→ (∨→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (∨→ x)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (∨→ x)) (∂→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨→ x₁)) (x₂ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨→ x₁)) (∂→ x₂) () eq
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧)) (∂→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∂) (∂→ (∧→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (∧→ x)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (∧→ x)) (∂→ x₁) () eq
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧→ x₁)) (x₂ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧→ x₁)) (∂→ x₂) () eq
  ho&s≤ss⇒hoss (s ←∂) (x ←∂→ x₁) .↓ hitsAtLeastOnce←∂↓ eq = hitsAtLeastOnce←∂→↓
  ho&s≤ss⇒hoss (s ←∂) (x ←∂→ x₁) (ind ←∂) (hitsAtLeastOnce←∂←∂ x₂) (≤d←∂ x₃) = hitsAtLeastOnce←∂→←∂ (ho&s≤ss⇒hoss s x ind x₂ x₃)
  ho&s≤ss⇒hoss (∂→ s) ↓ ind ho eq = hitsAtLeastOnce↓
  ho&s≤ss⇒hoss (∂→ s) (↓ ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (∂→ s) (↓ ←∂) (x ←∂) () eq
  ho&s≤ss⇒hoss (∂→ s) (↓ ←∂) (∂→ x) ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∂) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∂) ←∂) (x₁ ←∂) () eq
  ho&s≤ss⇒hoss (∂→ s) ((x ←∂) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (∂→ s) ((∂→ x) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (∂→ s) ((∂→ x) ←∂) (x₁ ←∂) () eq
  ho&s≤ss⇒hoss (∂→ s) ((∂→ x) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∂→ x₁) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∂→ x₁) ←∂) (x₂ ←∂) () eq
  ho&s≤ss⇒hoss (∂→ s) ((x ←∂→ x₁) ←∂) (∂→ x₂) ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∨) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∨) ←∂) (x₁ ←∂) () eq
  ho&s≤ss⇒hoss (∂→ s) ((x ←∨) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (∂→ s) ((∨→ x) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (∂→ s) ((∨→ x) ←∂) (x₁ ←∂) () eq
  ho&s≤ss⇒hoss (∂→ s) ((∨→ x) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∨→ x₁) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∨→ x₁) ←∂) (x₂ ←∂) () eq
  ho&s≤ss⇒hoss (∂→ s) ((x ←∨→ x₁) ←∂) (∂→ x₂) ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∧) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∧) ←∂) (x₁ ←∂) () eq
  ho&s≤ss⇒hoss (∂→ s) ((x ←∧) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (∂→ s) ((∧→ x) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (∂→ s) ((∧→ x) ←∂) (x₁ ←∂) () eq
  ho&s≤ss⇒hoss (∂→ s) ((∧→ x) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∧→ x₁) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (∂→ s) ((x ←∧→ x₁) ←∂) (x₂ ←∂) () eq
  ho&s≤ss⇒hoss (∂→ s) ((x ←∧→ x₁) ←∂) (∂→ x₂) ho ()
  ho&s≤ss⇒hoss (∂→ s) (∂→ x) .↓ hitsAtLeastOnce∂→↓ eq = hitsAtLeastOnce∂→↓
  ho&s≤ss⇒hoss (∂→ s) (∂→ x) (∂→ ind) (hitsAtLeastOnce∂→∂→ x₁) (≤∂→ x₂) = hitsAtLeastOnce∂→∂→ (ho&s≤ss⇒hoss s x ind x₁ x₂)
  ho&s≤ss⇒hoss (∂→ s) (x ←∂→ x₁) .↓ hitsAtLeastOnce∂→↓ eq = hitsAtLeastOnce←∂→↓
  ho&s≤ss⇒hoss (∂→ s) (x ←∂→ x₁) (∂→ ind) (hitsAtLeastOnce∂→∂→ x₂) (≤d∂→ x₃) = hitsAtLeastOnce←∂→∂→ (ho&s≤ss⇒hoss s x₁ ind x₂ x₃)
  ho&s≤ss⇒hoss (s ←∂→ s₁) ↓ ind ho eq = hitsAtLeastOnce↓
  ho&s≤ss⇒hoss (s ←∂→ s₁) (↓ ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (↓ ←∂) (x ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (↓ ←∂) (∂→ x) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂) ←∂) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((∂→ x) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((∂→ x) ←∂) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((∂→ x) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂→ x₁) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂→ x₁) ←∂) (x₂ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂→ x₁) ←∂) (∂→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨) ←∂) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((∨→ x) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((∨→ x) ←∂) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((∨→ x) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨→ x₁) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨→ x₁) ←∂) (x₂ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨→ x₁) ←∂) (∂→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧) ←∂) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((∧→ x) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((∧→ x) ←∂) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((∧→ x) ←∂) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧→ x₁) ←∂) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧→ x₁) ←∂) (x₂ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧→ x₁) ←∂) (∂→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ ↓) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ ↓) (x ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ ↓) (∂→ x) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂)) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∂→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∂→ x)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∂→ x)) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂→ x₁)) (x₂ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂→ x₁)) (∂→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨)) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∨→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∨→ x)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∨→ x)) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨→ x₁)) (x₂ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨→ x₁)) (∂→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧)) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∧→ x)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∧→ x)) (x₁ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∧→ x)) (∂→ x₁) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧→ x₁)) ↓ ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧→ x₁)) (x₂ ←∂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧→ x₁)) (∂→ x₂) ho ()
  ho&s≤ss⇒hoss (s ←∂→ s₁) (x ←∂→ x₁) .↓ hitsAtLeastOnce←∂→↓ eq = hitsAtLeastOnce←∂→↓
  ho&s≤ss⇒hoss (s ←∂→ s₁) (x ←∂→ x₁) (ind ←∂) (hitsAtLeastOnce←∂→←∂ x₂) (≤←∂→ x₃ x₄) = hitsAtLeastOnce←∂→←∂ (ho&s≤ss⇒hoss s x ind x₂ x₃)
  ho&s≤ss⇒hoss (s ←∂→ s₁) (x ←∂→ x₁) (∂→ ind) (hitsAtLeastOnce←∂→∂→ x₂) (≤←∂→ x₃ x₄) = hitsAtLeastOnce←∂→∂→ (ho&s≤ss⇒hoss s₁ x₁ ind x₂ x₄)



  ¬ho&s≤ss⇒¬hos : ∀ {i u ll pll} → (s ss : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
                 → ¬ (hitsAtLeastOnce ss ind) → s ≤s ss → ¬ (hitsAtLeastOnce s ind)
  ¬ho&s≤ss⇒¬hos s ss ind ¬ho rl x = ¬ho (ho&s≤ss⇒hoss s ss ind x rl)


  
  ¬trho : ∀{i u ll pll rll} →  ∀ ltr → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
          → ¬ (hitsAtLeastOnce s ind) → (ut : UpTran {rll = rll} ind ltr)
          → ¬ (hitsAtLeastOnce (SetLL.tran s ltr) (IndexLLProp.tran ind ltr ut))
  ¬trho I s ind ¬ho indI = ¬ho
  ¬trho (∂c ltr) ↓ .(_ ←∂) ¬ho (←∂∂c ut) = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (∂c ltr) ↓ .(∂→ _) ¬ho (∂→∂c ut) = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (∂c ltr) (s ←∂) (ind ←∂) ¬ho (←∂∂c ut) = ¬trho ltr (∂→ s) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ s) (∂→ ind))
    ¬nho (hitsAtLeastOnce∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂←∂ x)
  ¬trho (∂c ltr) (s ←∂) (∂→ ind) ¬ho (∂→∂c ut) = ¬trho ltr (∂→ s) (ind ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ s) (ind ←∂))
    ¬nho ()
  ¬trho (∂c ltr) (∂→ s) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce∂→↓
  ¬trho (∂c ltr) (∂→ s) (ind ←∂) ¬ho (←∂∂c ut) = ¬trho ltr (s ←∂) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (∂→ ind))
    ¬nho ()
  ¬trho (∂c ltr) (∂→ s) (∂→ ind) ¬ho (∂→∂c ut) = ¬trho ltr (s ←∂) (ind ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (ind ←∂))
    ¬nho (hitsAtLeastOnce←∂←∂ x) = ¬ho (hitsAtLeastOnce∂→∂→ x)
  ¬trho (∂c ltr) (s ←∂→ s₁) (ind ←∂) ¬ho (←∂∂c ut) = ¬trho ltr (s₁ ←∂→ s) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∂→ s) (∂→ ind))
    ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  ¬trho (∂c ltr) (s ←∂→ s₁) (∂→ ind) ¬ho (∂→∂c ut)  = ¬trho ltr (s₁ ←∂→ s) (ind ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∂→ s) (ind ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  ¬trho (∧c ltr) ↓ .(_ ←∧) ¬ho (←∧∧c ut) = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (∧c ltr) ↓ .(∧→ _) ¬ho (∧→∧c ut) = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (∧c ltr) (s ←∧) (ind ←∧) ¬ho (←∧∧c ut) = ¬trho ltr (∧→ s) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ s) (∧→ ind))
    ¬nho (hitsAtLeastOnce∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧←∧ x)
  ¬trho (∧c ltr) (s ←∧) (∧→ ind) ¬ho (∧→∧c ut) = ¬trho ltr (∧→ s) (ind ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ s) (ind ←∧))
    ¬nho ()
  ¬trho (∧c ltr) (∧→ s) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce∧→↓
  ¬trho (∧c ltr) (∧→ s) (ind ←∧) ¬ho (←∧∧c ut) = ¬trho ltr (s ←∧) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (∧→ ind))
    ¬nho ()
  ¬trho (∧c ltr) (∧→ s) (∧→ ind) ¬ho (∧→∧c ut) = ¬trho ltr (s ←∧) (ind ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (ind ←∧))
    ¬nho (hitsAtLeastOnce←∧←∧ x) = ¬ho (hitsAtLeastOnce∧→∧→ x)
  ¬trho (∧c ltr) (s ←∧→ s₁) (ind ←∧) ¬ho (←∧∧c ut) = ¬trho ltr (s₁ ←∧→ s) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∧→ s) (∧→ ind))
    ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  ¬trho (∧c ltr) (s ←∧→ s₁) (∧→ ind) ¬ho (∧→∧c ut)  = ¬trho ltr (s₁ ←∧→ s) (ind ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∧→ s) (ind ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  ¬trho (∨c ltr) ↓ .(_ ←∨) ¬ho (←∨∨c ut) = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (∨c ltr) ↓ .(∨→ _) ¬ho (∨→∨c ut) = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (∨c ltr) (s ←∨) (ind ←∨) ¬ho (←∨∨c ut) = ¬trho ltr (∨→ s) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ s) (∨→ ind))
    ¬nho (hitsAtLeastOnce∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨←∨ x)
  ¬trho (∨c ltr) (s ←∨) (∨→ ind) ¬ho (∨→∨c ut) = ¬trho ltr (∨→ s) (ind ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ s) (ind ←∨))
    ¬nho ()
  ¬trho (∨c ltr) (∨→ s) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce∨→↓
  ¬trho (∨c ltr) (∨→ s) (ind ←∨) ¬ho (←∨∨c ut) = ¬trho ltr (s ←∨) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (∨→ ind))
    ¬nho ()
  ¬trho (∨c ltr) (∨→ s) (∨→ ind) ¬ho (∨→∨c ut) = ¬trho ltr (s ←∨) (ind ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (ind ←∨))
    ¬nho (hitsAtLeastOnce←∨←∨ x) = ¬ho (hitsAtLeastOnce∨→∨→ x)
  ¬trho (∨c ltr) (s ←∨→ s₁) (ind ←∨) ¬ho (←∨∨c ut) = ¬trho ltr (s₁ ←∨→ s) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∨→ s) (∨→ ind))
    ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  ¬trho (∨c ltr) (s ←∨→ s₁) (∨→ ind) ¬ho (∨→∨c ut)  = ¬trho ltr (s₁ ←∨→ s) (ind ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∨→ s) (ind ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  ¬trho (∧∧d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (∧∧d ltr) (↓ ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut)
                                      = λ _ → ¬ho (hitsAtLeastOnce←∧←∧ hitsAtLeastOnce↓)
  ¬trho (∧∧d ltr) ((s ←∧) ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (s ←∧) (ind ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (ind ←∧))
    ¬nho (hitsAtLeastOnce←∧←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧←∧ x))
  
  ¬trho (∧∧d ltr) ((∧→ s) ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut)  = ¬trho ltr (∧→ (s ←∧)) (ind ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧)) (ind ←∧))
    ¬nho ()
  
  ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧)) (ind ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧)) (ind ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→←∧ x))
  
  ¬trho (∧∧d ltr) (↓ ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = λ _ → ¬ho (hitsAtLeastOnce←∧←∧ hitsAtLeastOnce↓)
  ¬trho (∧∧d ltr) ((s ←∧) ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧) (∧→ (ind ←∧)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (∧→ (ind ←∧)))
    ¬nho ()
  
  ¬trho (∧∧d ltr) ((∧→ s) ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (∧→ (s ←∧)) (∧→ (ind ←∧)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧)) (∧→ (ind ←∧)))
    ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce∧→∧→ x))
  
  ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧)) (∧→ (ind ←∧)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧)) (∧→ (ind ←∧)))
    ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→∧→ x))
  
  ¬trho (∧∧d ltr) (↓ ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧)) (∧→ (∧→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧)) (∧→ (∧→ ind)))
    ¬nho (hitsAtLeastOnce←∧→∧→ ())
  
  ¬trho (∧∧d ltr) ((s ←∧) ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧) (∧→ (∧→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (∧→ (∧→ ind)))
    ¬nho ()
  
  ¬trho (∧∧d ltr) ((∧→ s) ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (∧→ (s ←∧)) (∧→ (∧→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧)) (∧→ (∧→ ind)))
    ¬nho (hitsAtLeastOnce∧→∧→ ())
  
  ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧)) (∧→ (∧→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧)) (∧→ (∧→ ind)))
    ¬nho (hitsAtLeastOnce←∧→∧→ ())
  
  ¬trho (∧∧d ltr) (∧→ s) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (∧→ (∧→ s)) (ind ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ (∧→ s)) (ind ←∧))
    ¬nho ()
  
  ¬trho (∧∧d ltr) (∧→ s) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (∧→ (∧→ s)) (∧→ (ind ←∧)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ (∧→ s)) (∧→ (ind ←∧)))
    ¬nho (hitsAtLeastOnce∧→∧→ ())
  
  ¬trho (∧∧d ltr) (∧→ s) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (∧→ (∧→ s)) (∧→ (∧→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ (∧→ s)) (∧→ (∧→ ind)))
    ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce∧→∧→ x)
  
  
  
  ¬trho (∧∧d ltr) (↓ ←∧→ s₁) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧→ s₁)) (ind ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧→ s₁)) (ind ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓)
   
  ¬trho (∧∧d ltr) ((s ←∧) ←∧→ s₁) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (∧→ s₁)) (ind ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (∧→ s₁)) (ind ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧←∧ x))
  
  ¬trho (∧∧d ltr) ((∧→ s) ←∧→ s₁) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (∧→ (s ←∧→ s₁)) (ind ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧→ s₁)) (ind ←∧))
    ¬nho ()
  
  ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧→ s₂) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut)  = ¬trho ltr (s ←∧→ (s₁ ←∧→ s₂)) (ind ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧→ s₂)) (ind ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ x))
  
  
  ¬trho (∧∧d ltr) (↓ ←∧→ s₁) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (ind ←∧)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (ind ←∧)))
    ¬nho x = ¬ho (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓)
   
  ¬trho (∧∧d ltr) ((s ←∧) ←∧→ s₁) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (∧→ s₁)) (∧→ (ind ←∧)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (∧→ s₁)) (∧→ (ind ←∧)))
    ¬nho (hitsAtLeastOnce←∧→∧→ ())
  
  ¬trho (∧∧d ltr) ((∧→ s) ←∧→ s₁) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (∧→ (s ←∧→ s₁)) (∧→ (ind ←∧)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧→ s₁)) (∧→ (ind ←∧)))
    ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce∧→∧→ x))
  
  ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧→ s₂) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (ind ←∧)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (ind ←∧)))
    ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ x))
  
  ¬trho (∧∧d ltr) (↓ ←∧→ s₁) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (∧→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (∧→ ind)))
    ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
   
  ¬trho (∧∧d ltr) ((s ←∧) ←∧→ s₁) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧→ (∧→ s₁)) (∧→ (∧→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (∧→ s₁)) (∧→ (∧→ ind)))
    ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
  ¬trho (∧∧d ltr) ((∧→ s) ←∧→ s₁) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (∧→ (s ←∧→ s₁)) (∧→ (∧→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧→ s₁)) (∧→ (∧→ ind)))
    ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
  ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧→ s₂) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (∧→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (∧→ ind)))
    ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
  ¬trho (¬∧∧d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (¬∧∧d ltr) (s ←∧) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce←∧↓
  ¬trho (¬∧∧d ltr) (s ←∧) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s ←∧) ←∧) ((ind ←∧) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s ←∧) ←∧) ((ind ←∧) ←∧))
    ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧←∧ x)
  
  ¬trho (¬∧∧d ltr) (s ←∧) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s ←∧) ←∧) ((∧→ ind) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s ←∧) ←∧) ((∧→ ind) ←∧))
    ¬nho (hitsAtLeastOnce←∧←∧ ())
  
  ¬trho (¬∧∧d ltr) (s ←∧) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s ←∧) ←∧) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s ←∧) ←∧) (∧→ ind))
    ¬nho ()
  
  ¬trho (¬∧∧d ltr) (∧→ ↓) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ ())
  
  ¬trho (¬∧∧d ltr) (∧→ (s ←∧)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((∧→ s) ←∧) ((ind ←∧) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧) ((ind ←∧) ←∧))
    ¬nho (hitsAtLeastOnce←∧←∧ ())
  
  ¬trho (¬∧∧d ltr) (∧→ (∧→ s)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr (∧→ s) ((ind ←∧) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ s) ((ind ←∧) ←∧))
    ¬nho ()
  
  ¬trho (¬∧∧d ltr) (∧→ (s ←∧→ s₁)) (ind ←∧) ¬ho (←∧¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧→ s₁) ((ind ←∧) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧→ s₁) ((ind ←∧) ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ ())
  
  
  ¬trho (¬∧∧d ltr) (∧→ ↓) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr ((∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧))
    ¬nho x = ¬ho (hitsAtLeastOnce∧→∧→ hitsAtLeastOnce↓)
  
  ¬trho (¬∧∧d ltr) (∧→ (s ←∧)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧) ((∧→ ind) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧) ((∧→ ind) ←∧))
    ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧←∧ x))
  
  ¬trho (¬∧∧d ltr) (∧→ (∧→ s)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr (∧→ s) ((∧→ ind) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ s) ((∧→ ind) ←∧))
    ¬nho ()
  
  ¬trho (¬∧∧d ltr) (∧→ (s ←∧→ s₁)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧→ s₁) ((∧→ ind) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧→ s₁) ((∧→ ind) ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→←∧ x))
  
  
  ¬trho (¬∧∧d ltr) (∧→ ↓) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut)   = ¬trho ltr ((∧→ ↓) ←∧→ ↓) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∧→ ↓) ←∧→ ↓) (∧→ ind))
    ¬nho x = ¬ho (hitsAtLeastOnce∧→∧→ hitsAtLeastOnce↓)
  
  ¬trho (¬∧∧d ltr) (∧→ (s ←∧)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧) (∧→ ind))
    ¬nho ()
  
  ¬trho (¬∧∧d ltr) (∧→ (∧→ s)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr (∧→ s) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∧→ s) (∧→ ind))
    ¬nho (hitsAtLeastOnce∧→∧→ x) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce∧→∧→ x))
  
  ¬trho (¬∧∧d ltr) (∧→ (s ←∧→ s₁)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧→ s₁) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧→ s₁) (∧→ ind))
    ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→∧→ x))
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ ↓) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧) ((ind ←∧) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧) ((ind ←∧) ←∧))
    ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ (∧→ s)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧) ←∧→ s) ((ind ←∧) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧) ←∧→ s) ((ind ←∧) ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧→ s₂)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧→ s₂) ((ind ←∧) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧→ s₂) ((ind ←∧) ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ ↓) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧))
    ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓)
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧) ((∧→ ind) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧) ((∧→ ind) ←∧))
    ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧←∧ x))
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ (∧→ s)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧) ←∧→ s) ((∧→ ind) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧) ←∧→ s) ((∧→ ind) ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ ())
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧→ s₂)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧→ s₂) ((∧→ ind) ←∧) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧→ s₂) ((∧→ ind) ←∧))
    ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ x))
  
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ ↓) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ ↓) ←∧→ ↓) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ ↓) ←∧→ ↓) (∧→ ind))
    ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓)
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧) (∧→ ind))
    ¬nho ()
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ (∧→ s)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧) ←∧→ s) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧) ←∧→ s) (∧→ ind))
    ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce∧→∧→ x))
  
  ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧→ s₂)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧→ s₂) (∧→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧→ s₂) (∧→ ind))
    ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ x))
  
  
  ¬trho (∨∨d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (∨∨d ltr) (↓ ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut)
                                      = λ _ → ¬ho (hitsAtLeastOnce←∨←∨ hitsAtLeastOnce↓)
  ¬trho (∨∨d ltr) ((s ←∨) ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (s ←∨) (ind ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (ind ←∨))
    ¬nho (hitsAtLeastOnce←∨←∨ x) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨←∨ x))
  
  ¬trho (∨∨d ltr) ((∨→ s) ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut)  = ¬trho ltr (∨→ (s ←∨)) (ind ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨)) (ind ←∨))
    ¬nho ()
  
  ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨)) (ind ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨)) (ind ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→←∨ x))
  
  ¬trho (∨∨d ltr) (↓ ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = λ _ → ¬ho (hitsAtLeastOnce←∨←∨ hitsAtLeastOnce↓)
  ¬trho (∨∨d ltr) ((s ←∨) ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨) (∨→ (ind ←∨)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (∨→ (ind ←∨)))
    ¬nho ()
  
  ¬trho (∨∨d ltr) ((∨→ s) ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (∨→ (s ←∨)) (∨→ (ind ←∨)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨)) (∨→ (ind ←∨)))
    ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce∨→∨→ x))
  
  ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨)) (∨→ (ind ←∨)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨)) (∨→ (ind ←∨)))
    ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→∨→ x))
  
  ¬trho (∨∨d ltr) (↓ ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨)) (∨→ (∨→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨)) (∨→ (∨→ ind)))
    ¬nho (hitsAtLeastOnce←∨→∨→ ())
  
  ¬trho (∨∨d ltr) ((s ←∨) ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨) (∨→ (∨→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (∨→ (∨→ ind)))
    ¬nho ()
  
  ¬trho (∨∨d ltr) ((∨→ s) ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (∨→ (s ←∨)) (∨→ (∨→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨)) (∨→ (∨→ ind)))
    ¬nho (hitsAtLeastOnce∨→∨→ ())
  
  ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨)) (∨→ (∨→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨)) (∨→ (∨→ ind)))
    ¬nho (hitsAtLeastOnce←∨→∨→ ())
  
  ¬trho (∨∨d ltr) (∨→ s) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (∨→ (∨→ s)) (ind ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ (∨→ s)) (ind ←∨))
    ¬nho ()
  
  ¬trho (∨∨d ltr) (∨→ s) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (∨→ (∨→ s)) (∨→ (ind ←∨)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ (∨→ s)) (∨→ (ind ←∨)))
    ¬nho (hitsAtLeastOnce∨→∨→ ())
  
  ¬trho (∨∨d ltr) (∨→ s) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (∨→ (∨→ s)) (∨→ (∨→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ (∨→ s)) (∨→ (∨→ ind)))
    ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce∨→∨→ x)
  
  
  
  ¬trho (∨∨d ltr) (↓ ←∨→ s₁) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨→ s₁)) (ind ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨→ s₁)) (ind ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓)
   
  ¬trho (∨∨d ltr) ((s ←∨) ←∨→ s₁) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (∨→ s₁)) (ind ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (∨→ s₁)) (ind ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨←∨ x))
  
  ¬trho (∨∨d ltr) ((∨→ s) ←∨→ s₁) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (∨→ (s ←∨→ s₁)) (ind ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨→ s₁)) (ind ←∨))
    ¬nho ()
  
  ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨→ s₂) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut)  = ¬trho ltr (s ←∨→ (s₁ ←∨→ s₂)) (ind ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨→ s₂)) (ind ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ x))
  
  
  ¬trho (∨∨d ltr) (↓ ←∨→ s₁) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (ind ←∨)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (ind ←∨)))
    ¬nho x = ¬ho (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓)
   
  ¬trho (∨∨d ltr) ((s ←∨) ←∨→ s₁) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (∨→ s₁)) (∨→ (ind ←∨)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (∨→ s₁)) (∨→ (ind ←∨)))
    ¬nho (hitsAtLeastOnce←∨→∨→ ())
  
  ¬trho (∨∨d ltr) ((∨→ s) ←∨→ s₁) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (∨→ (s ←∨→ s₁)) (∨→ (ind ←∨)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨→ s₁)) (∨→ (ind ←∨)))
    ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce∨→∨→ x))
  
  ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨→ s₂) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (ind ←∨)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (ind ←∨)))
    ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ x))
  
  ¬trho (∨∨d ltr) (↓ ←∨→ s₁) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (∨→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (∨→ ind)))
    ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
   
  ¬trho (∨∨d ltr) ((s ←∨) ←∨→ s₁) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨→ (∨→ s₁)) (∨→ (∨→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (∨→ s₁)) (∨→ (∨→ ind)))
    ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
  ¬trho (∨∨d ltr) ((∨→ s) ←∨→ s₁) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (∨→ (s ←∨→ s₁)) (∨→ (∨→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨→ s₁)) (∨→ (∨→ ind)))
    ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
  ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨→ s₂) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (∨→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (∨→ ind)))
    ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
  ¬trho (¬∨∨d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (¬∨∨d ltr) (s ←∨) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce←∨↓
  ¬trho (¬∨∨d ltr) (s ←∨) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s ←∨) ←∨) ((ind ←∨) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s ←∨) ←∨) ((ind ←∨) ←∨))
    ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨←∨ x)
  
  ¬trho (¬∨∨d ltr) (s ←∨) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s ←∨) ←∨) ((∨→ ind) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s ←∨) ←∨) ((∨→ ind) ←∨))
    ¬nho (hitsAtLeastOnce←∨←∨ ())
  
  ¬trho (¬∨∨d ltr) (s ←∨) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s ←∨) ←∨) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s ←∨) ←∨) (∨→ ind))
    ¬nho ()
  
  ¬trho (¬∨∨d ltr) (∨→ ↓) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ ())
  
  ¬trho (¬∨∨d ltr) (∨→ (s ←∨)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((∨→ s) ←∨) ((ind ←∨) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨) ((ind ←∨) ←∨))
    ¬nho (hitsAtLeastOnce←∨←∨ ())
  
  ¬trho (¬∨∨d ltr) (∨→ (∨→ s)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr (∨→ s) ((ind ←∨) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ s) ((ind ←∨) ←∨))
    ¬nho ()
  
  ¬trho (¬∨∨d ltr) (∨→ (s ←∨→ s₁)) (ind ←∨) ¬ho (←∨¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨→ s₁) ((ind ←∨) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨→ s₁) ((ind ←∨) ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ ())
  
  
  ¬trho (¬∨∨d ltr) (∨→ ↓) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr ((∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨))
    ¬nho x = ¬ho (hitsAtLeastOnce∨→∨→ hitsAtLeastOnce↓)
  
  ¬trho (¬∨∨d ltr) (∨→ (s ←∨)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨) ((∨→ ind) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨) ((∨→ ind) ←∨))
    ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨←∨ x))
  
  ¬trho (¬∨∨d ltr) (∨→ (∨→ s)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr (∨→ s) ((∨→ ind) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ s) ((∨→ ind) ←∨))
    ¬nho ()
  
  ¬trho (¬∨∨d ltr) (∨→ (s ←∨→ s₁)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨→ s₁) ((∨→ ind) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨→ s₁) ((∨→ ind) ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→←∨ x))
  
  
  ¬trho (¬∨∨d ltr) (∨→ ↓) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut)   = ¬trho ltr ((∨→ ↓) ←∨→ ↓) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∨→ ↓) ←∨→ ↓) (∨→ ind))
    ¬nho x = ¬ho (hitsAtLeastOnce∨→∨→ hitsAtLeastOnce↓)
  
  ¬trho (¬∨∨d ltr) (∨→ (s ←∨)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨) (∨→ ind))
    ¬nho ()
  
  ¬trho (¬∨∨d ltr) (∨→ (∨→ s)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr (∨→ s) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∨→ s) (∨→ ind))
    ¬nho (hitsAtLeastOnce∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce∨→∨→ x))
  
  ¬trho (¬∨∨d ltr) (∨→ (s ←∨→ s₁)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨→ s₁) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨→ s₁) (∨→ ind))
    ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→∨→ x))
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ ↓) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨) ((ind ←∨) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨) ((ind ←∨) ←∨))
    ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ (∨→ s)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨) ←∨→ s) ((ind ←∨) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨) ←∨→ s) ((ind ←∨) ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨→ s₂)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨→ s₂) ((ind ←∨) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨→ s₂) ((ind ←∨) ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ ↓) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨))
    ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓)
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨) ((∨→ ind) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨) ((∨→ ind) ←∨))
    ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨←∨ x))
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ (∨→ s)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨) ←∨→ s) ((∨→ ind) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨) ←∨→ s) ((∨→ ind) ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ ())
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨→ s₂)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨→ s₂) ((∨→ ind) ←∨) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨→ s₂) ((∨→ ind) ←∨))
    ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ x))
  
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ ↓) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ ↓) ←∨→ ↓) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ ↓) ←∨→ ↓) (∨→ ind))
    ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓)
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨) (∨→ ind))
    ¬nho ()
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ (∨→ s)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨) ←∨→ s) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨) ←∨→ s) (∨→ ind))
    ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce∨→∨→ x))
  
  ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨→ s₂)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨→ s₂) (∨→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨→ s₂) (∨→ ind))
    ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ x))
  
  
  ¬trho (∂∂d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (∂∂d ltr) (↓ ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut)
                                      = λ _ → ¬ho (hitsAtLeastOnce←∂←∂ hitsAtLeastOnce↓)
  ¬trho (∂∂d ltr) ((s ←∂) ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (s ←∂) (ind ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (ind ←∂))
    ¬nho (hitsAtLeastOnce←∂←∂ x) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂←∂ x))
  
  ¬trho (∂∂d ltr) ((∂→ s) ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut)  = ¬trho ltr (∂→ (s ←∂)) (ind ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂)) (ind ←∂))
    ¬nho ()
  
  ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂)) (ind ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂)) (ind ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→←∂ x))
  
  ¬trho (∂∂d ltr) (↓ ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = λ _ → ¬ho (hitsAtLeastOnce←∂←∂ hitsAtLeastOnce↓)
  ¬trho (∂∂d ltr) ((s ←∂) ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂) (∂→ (ind ←∂)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (∂→ (ind ←∂)))
    ¬nho ()
  
  ¬trho (∂∂d ltr) ((∂→ s) ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (∂→ (s ←∂)) (∂→ (ind ←∂)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂)) (∂→ (ind ←∂)))
    ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce∂→∂→ x))
  
  ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂)) (∂→ (ind ←∂)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂)) (∂→ (ind ←∂)))
    ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→∂→ x))
  
  ¬trho (∂∂d ltr) (↓ ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂)) (∂→ (∂→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂)) (∂→ (∂→ ind)))
    ¬nho (hitsAtLeastOnce←∂→∂→ ())
  
  ¬trho (∂∂d ltr) ((s ←∂) ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂) (∂→ (∂→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (∂→ (∂→ ind)))
    ¬nho ()
  
  ¬trho (∂∂d ltr) ((∂→ s) ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (∂→ (s ←∂)) (∂→ (∂→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂)) (∂→ (∂→ ind)))
    ¬nho (hitsAtLeastOnce∂→∂→ ())
  
  ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂)) (∂→ (∂→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂)) (∂→ (∂→ ind)))
    ¬nho (hitsAtLeastOnce←∂→∂→ ())
  
  ¬trho (∂∂d ltr) (∂→ s) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (∂→ (∂→ s)) (ind ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ (∂→ s)) (ind ←∂))
    ¬nho ()
  
  ¬trho (∂∂d ltr) (∂→ s) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (∂→ (∂→ s)) (∂→ (ind ←∂)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ (∂→ s)) (∂→ (ind ←∂)))
    ¬nho (hitsAtLeastOnce∂→∂→ ())
  
  ¬trho (∂∂d ltr) (∂→ s) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (∂→ (∂→ s)) (∂→ (∂→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ (∂→ s)) (∂→ (∂→ ind)))
    ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce∂→∂→ x)
  
  
  
  ¬trho (∂∂d ltr) (↓ ←∂→ s₁) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂→ s₁)) (ind ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂→ s₁)) (ind ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓)
   
  ¬trho (∂∂d ltr) ((s ←∂) ←∂→ s₁) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (∂→ s₁)) (ind ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (∂→ s₁)) (ind ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂←∂ x))
  
  ¬trho (∂∂d ltr) ((∂→ s) ←∂→ s₁) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (∂→ (s ←∂→ s₁)) (ind ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂→ s₁)) (ind ←∂))
    ¬nho ()
  
  ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂→ s₂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut)  = ¬trho ltr (s ←∂→ (s₁ ←∂→ s₂)) (ind ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂→ s₂)) (ind ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ x))
  
  
  ¬trho (∂∂d ltr) (↓ ←∂→ s₁) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (ind ←∂)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (ind ←∂)))
    ¬nho x = ¬ho (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓)
   
  ¬trho (∂∂d ltr) ((s ←∂) ←∂→ s₁) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (∂→ s₁)) (∂→ (ind ←∂)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (∂→ s₁)) (∂→ (ind ←∂)))
    ¬nho (hitsAtLeastOnce←∂→∂→ ())
  
  ¬trho (∂∂d ltr) ((∂→ s) ←∂→ s₁) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (∂→ (s ←∂→ s₁)) (∂→ (ind ←∂)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂→ s₁)) (∂→ (ind ←∂)))
    ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce∂→∂→ x))
  
  ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂→ s₂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (ind ←∂)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (ind ←∂)))
    ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ x))
  
  ¬trho (∂∂d ltr) (↓ ←∂→ s₁) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (∂→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (∂→ ind)))
    ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
   
  ¬trho (∂∂d ltr) ((s ←∂) ←∂→ s₁) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂→ (∂→ s₁)) (∂→ (∂→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (∂→ s₁)) (∂→ (∂→ ind)))
    ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
  ¬trho (∂∂d ltr) ((∂→ s) ←∂→ s₁) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (∂→ (s ←∂→ s₁)) (∂→ (∂→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂→ s₁)) (∂→ (∂→ ind)))
    ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
  ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂→ s₂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (∂→ ind)) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (∂→ ind)))
    ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
  ¬trho (¬∂∂d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
  ¬trho (¬∂∂d ltr) (s ←∂) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce←∂↓
  ¬trho (¬∂∂d ltr) (s ←∂) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s ←∂) ←∂) ((ind ←∂) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s ←∂) ←∂) ((ind ←∂) ←∂))
    ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂←∂ x)
  
  ¬trho (¬∂∂d ltr) (s ←∂) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s ←∂) ←∂) ((∂→ ind) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s ←∂) ←∂) ((∂→ ind) ←∂))
    ¬nho (hitsAtLeastOnce←∂←∂ ())
  
  ¬trho (¬∂∂d ltr) (s ←∂) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s ←∂) ←∂) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s ←∂) ←∂) (∂→ ind))
    ¬nho ()
  
  ¬trho (¬∂∂d ltr) (∂→ ↓) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ ())
  
  ¬trho (¬∂∂d ltr) (∂→ (s ←∂)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((∂→ s) ←∂) ((ind ←∂) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂) ((ind ←∂) ←∂))
    ¬nho (hitsAtLeastOnce←∂←∂ ())
  
  ¬trho (¬∂∂d ltr) (∂→ (∂→ s)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr (∂→ s) ((ind ←∂) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ s) ((ind ←∂) ←∂))
    ¬nho ()
  
  ¬trho (¬∂∂d ltr) (∂→ (s ←∂→ s₁)) (ind ←∂) ¬ho (←∂¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂→ s₁) ((ind ←∂) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂→ s₁) ((ind ←∂) ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ ())
  
  
  ¬trho (¬∂∂d ltr) (∂→ ↓) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr ((∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂))
    ¬nho x = ¬ho (hitsAtLeastOnce∂→∂→ hitsAtLeastOnce↓)
  
  ¬trho (¬∂∂d ltr) (∂→ (s ←∂)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂) ((∂→ ind) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂) ((∂→ ind) ←∂))
    ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂←∂ x))
  
  ¬trho (¬∂∂d ltr) (∂→ (∂→ s)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr (∂→ s) ((∂→ ind) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ s) ((∂→ ind) ←∂))
    ¬nho ()
  
  ¬trho (¬∂∂d ltr) (∂→ (s ←∂→ s₁)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂→ s₁) ((∂→ ind) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂→ s₁) ((∂→ ind) ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→←∂ x))
  
  
  ¬trho (¬∂∂d ltr) (∂→ ↓) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut)   = ¬trho ltr ((∂→ ↓) ←∂→ ↓) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∂→ ↓) ←∂→ ↓) (∂→ ind))
    ¬nho x = ¬ho (hitsAtLeastOnce∂→∂→ hitsAtLeastOnce↓)
  
  ¬trho (¬∂∂d ltr) (∂→ (s ←∂)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂) (∂→ ind))
    ¬nho ()
  
  ¬trho (¬∂∂d ltr) (∂→ (∂→ s)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr (∂→ s) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce (∂→ s) (∂→ ind))
    ¬nho (hitsAtLeastOnce∂→∂→ x) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce∂→∂→ x))
  
  ¬trho (¬∂∂d ltr) (∂→ (s ←∂→ s₁)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂→ s₁) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂→ s₁) (∂→ ind))
    ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→∂→ x))
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ ↓) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂) ((ind ←∂) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂) ((ind ←∂) ←∂))
    ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ (∂→ s)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂) ←∂→ s) ((ind ←∂) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂) ←∂→ s) ((ind ←∂) ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂→ s₂)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂→ s₂) ((ind ←∂) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂→ s₂) ((ind ←∂) ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ ↓) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂))
    ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓)
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂) ((∂→ ind) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂) ((∂→ ind) ←∂))
    ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂←∂ x))
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ (∂→ s)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂) ←∂→ s) ((∂→ ind) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂) ←∂→ s) ((∂→ ind) ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ ())
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂→ s₂)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂→ s₂) ((∂→ ind) ←∂) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂→ s₂) ((∂→ ind) ←∂))
    ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ x))
  
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ ↓) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ ↓) ←∂→ ↓) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ ↓) ←∂→ ↓) (∂→ ind))
    ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓)
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂) (∂→ ind))
    ¬nho ()
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ (∂→ s)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂) ←∂→ s) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂) ←∂→ s) (∂→ ind))
    ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce∂→∂→ x))
  
  ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂→ s₂)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂→ s₂) (∂→ ind) ¬nho ut where
    ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂→ s₂) (∂→ ind))
    ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ x))
  
  
  


  truncHOSetLL : ∀ {i u ll pll} → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
                → hitsAtLeastOnce s ind → SetLL pll
  truncHOSetLL s ind ho with truncSetLL s ind | ho⇒¬trunc≡∅ s ind ho
  truncHOSetLL s ind ho | ∅ | e = ⊥-elim (e refl)
  truncHOSetLL s ind ho | ¬∅ x | e = x


-- truncHOSetLL preserves the ≤s relationship

  ≤⇒tr≤ : ∀{i u pll ll} → ∀ s ss → (ind : IndexLL {i} {u} pll ll) → s ≤s ss
          → (lho : hitsAtLeastOnce s ind) → (rho : hitsAtLeastOnce ss ind)
          → truncHOSetLL s ind lho ≤s truncHOSetLL ss ind rho
  ≤⇒tr≤ s ss ↓ eq lho rho = eq
  ≤⇒tr≤ ↓ ↓ (ind ←∧) eq lho rho = ≤↓
  ≤⇒tr≤ ↓ (ss ←∧) (ind ←∧) () lho rho
  ≤⇒tr≤ ↓ (∧→ ss) (ind ←∧) () lho rho
  ≤⇒tr≤ ↓ (ss ←∧→ ss₁) (ind ←∧) () lho rho
  ≤⇒tr≤ (s ←∧) ↓ (ind ←∧) eq lho rho = ≤↓
  ≤⇒tr≤ (s ←∧) (ss ←∧) (ind ←∧) (≤←∧ eq) (hitsAtLeastOnce←∧←∧ lho) (hitsAtLeastOnce←∧←∧ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq lho rho
  ... | ∅ | r | e | q | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | q | t = ⊥-elim (q refl)
  ... | ¬∅ x | r | ¬∅ x₁ | q | t = t
  ≤⇒tr≤ (s ←∧) (∧→ ss) (ind ←∧) () lho rho
  ≤⇒tr≤ (s ←∧) (ss ←∧→ ss₁) (ind ←∧) (≤d←∧ eq) (hitsAtLeastOnce←∧←∧ lho) (hitsAtLeastOnce←∧→←∧ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq lho rho
  ... | ∅ | r | q | e | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | e | t = ⊥-elim (e refl)
  ... | ¬∅ x | r | ¬∅ x₁ | e | t = t
  ≤⇒tr≤ (∧→ s) ss (ind ←∧) eq () rho
  ≤⇒tr≤ (s ←∧→ s₁) ↓ (ind ←∧) eq lho rho = ≤↓
  ≤⇒tr≤ (s ←∧→ s₁) (ss ←∧) (ind ←∧) () lho rho
  ≤⇒tr≤ (s ←∧→ s₁) (∧→ ss) (ind ←∧) () lho rho
  ≤⇒tr≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (ind ←∧) (≤←∧→ eq1 eq2) (hitsAtLeastOnce←∧→←∧ lho) (hitsAtLeastOnce←∧→←∧ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq1 lho rho 
  ... | ∅ | e | r | g | t = ⊥-elim (e refl)
  ... | ¬∅ x | e | ∅ | g | t = ⊥-elim (g refl)
  ... | ¬∅ x | e | ¬∅ x₁ | g | t = t
  ≤⇒tr≤ ↓ ↓ (∧→ ind) eq lho rho = ≤↓
  ≤⇒tr≤ ↓ (ss ←∧) (∧→ ind) () lho rho
  ≤⇒tr≤ ↓ (∧→ ss) (∧→ ind) () lho rho
  ≤⇒tr≤ ↓ (ss ←∧→ ss₁) (∧→ ind) () lho rho
  ≤⇒tr≤ (s ←∧) ss (∧→ ind) eq () rho
  ≤⇒tr≤ (∧→ s) ↓ (∧→ ind) eq lho rho = ≤↓
  ≤⇒tr≤ (∧→ s) (ss ←∧) (∧→ ind) () lho rho
  ≤⇒tr≤ (∧→ s) (∧→ ss) (∧→ ind) (≤∧→ eq) (hitsAtLeastOnce∧→∧→ lho) (hitsAtLeastOnce∧→∧→ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq lho rho
  ... | ∅ | r | e | q | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | q | t = ⊥-elim (q refl)
  ... | ¬∅ x | r | ¬∅ x₁ | q | t = t
  ≤⇒tr≤ (∧→ s) (ss ←∧→ ss₁) (∧→ ind) (≤d∧→ eq) (hitsAtLeastOnce∧→∧→ lho) (hitsAtLeastOnce←∧→∧→ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss₁ ind | ho⇒¬trunc≡∅ ss₁ ind rho | ≤⇒tr≤ s ss₁ ind eq lho rho
  ... | ∅ | r | q | e | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | e | t = ⊥-elim (e refl)
  ... | ¬∅ x | r | ¬∅ x₁ | e | t = t
  ≤⇒tr≤ (s ←∧→ s₁) ↓ (∧→ ind) eq lho rho = ≤↓
  ≤⇒tr≤ (s ←∧→ s₁) (ss ←∧) (∧→ ind) () lho rho
  ≤⇒tr≤ (s ←∧→ s₁) (∧→ ss) (∧→ ind) () lho rho
  ≤⇒tr≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (∧→ ind) (≤←∧→ eq eq₁) (hitsAtLeastOnce←∧→∧→ lho) (hitsAtLeastOnce←∧→∧→ rho)
    with truncSetLL s₁ ind | ho⇒¬trunc≡∅ s₁ ind lho | truncSetLL ss₁ ind | ho⇒¬trunc≡∅ ss₁ ind rho | ≤⇒tr≤ s₁ ss₁ ind eq₁ lho rho 
  ... | ∅ | e | r | g | t = ⊥-elim (e refl)
  ... | ¬∅ x | e | ∅ | g | t = ⊥-elim (g refl)
  ... | ¬∅ x | e | ¬∅ x₁ | g | t = t
  ≤⇒tr≤ ↓ ↓ (ind ←∨) eq lho rho = ≤↓
  ≤⇒tr≤ ↓ (ss ←∨) (ind ←∨) () lho rho
  ≤⇒tr≤ ↓ (∨→ ss) (ind ←∨) () lho rho
  ≤⇒tr≤ ↓ (ss ←∨→ ss₁) (ind ←∨) () lho rho
  ≤⇒tr≤ (s ←∨) ↓ (ind ←∨) eq lho rho = ≤↓
  ≤⇒tr≤ (s ←∨) (ss ←∨) (ind ←∨) (≤←∨ eq) (hitsAtLeastOnce←∨←∨ lho) (hitsAtLeastOnce←∨←∨ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq lho rho
  ... | ∅ | r | e | q | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | q | t = ⊥-elim (q refl)
  ... | ¬∅ x | r | ¬∅ x₁ | q | t = t
  ≤⇒tr≤ (s ←∨) (∨→ ss) (ind ←∨) () lho rho
  ≤⇒tr≤ (s ←∨) (ss ←∨→ ss₁) (ind ←∨) (≤d←∨ eq) (hitsAtLeastOnce←∨←∨ lho) (hitsAtLeastOnce←∨→←∨ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq lho rho
  ... | ∅ | r | q | e | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | e | t = ⊥-elim (e refl)
  ... | ¬∅ x | r | ¬∅ x₁ | e | t = t
  ≤⇒tr≤ (∨→ s) ss (ind ←∨) eq () rho
  ≤⇒tr≤ (s ←∨→ s₁) ↓ (ind ←∨) eq lho rho = ≤↓
  ≤⇒tr≤ (s ←∨→ s₁) (ss ←∨) (ind ←∨) () lho rho
  ≤⇒tr≤ (s ←∨→ s₁) (∨→ ss) (ind ←∨) () lho rho
  ≤⇒tr≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (ind ←∨) (≤←∨→ eq1 eq2) (hitsAtLeastOnce←∨→←∨ lho) (hitsAtLeastOnce←∨→←∨ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq1 lho rho 
  ... | ∅ | e | r | g | t = ⊥-elim (e refl)
  ... | ¬∅ x | e | ∅ | g | t = ⊥-elim (g refl)
  ... | ¬∅ x | e | ¬∅ x₁ | g | t = t
  ≤⇒tr≤ ↓ ↓ (∨→ ind) eq lho rho = ≤↓
  ≤⇒tr≤ ↓ (ss ←∨) (∨→ ind) () lho rho
  ≤⇒tr≤ ↓ (∨→ ss) (∨→ ind) () lho rho
  ≤⇒tr≤ ↓ (ss ←∨→ ss₁) (∨→ ind) () lho rho
  ≤⇒tr≤ (s ←∨) ss (∨→ ind) eq () rho
  ≤⇒tr≤ (∨→ s) ↓ (∨→ ind) eq lho rho = ≤↓
  ≤⇒tr≤ (∨→ s) (ss ←∨) (∨→ ind) () lho rho
  ≤⇒tr≤ (∨→ s) (∨→ ss) (∨→ ind) (≤∨→ eq) (hitsAtLeastOnce∨→∨→ lho) (hitsAtLeastOnce∨→∨→ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq lho rho
  ... | ∅ | r | e | q | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | q | t = ⊥-elim (q refl)
  ... | ¬∅ x | r | ¬∅ x₁ | q | t = t
  ≤⇒tr≤ (∨→ s) (ss ←∨→ ss₁) (∨→ ind) (≤d∨→ eq) (hitsAtLeastOnce∨→∨→ lho) (hitsAtLeastOnce←∨→∨→ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss₁ ind | ho⇒¬trunc≡∅ ss₁ ind rho | ≤⇒tr≤ s ss₁ ind eq lho rho
  ... | ∅ | r | q | e | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | e | t = ⊥-elim (e refl)
  ... | ¬∅ x | r | ¬∅ x₁ | e | t = t
  ≤⇒tr≤ (s ←∨→ s₁) ↓ (∨→ ind) eq lho rho = ≤↓
  ≤⇒tr≤ (s ←∨→ s₁) (ss ←∨) (∨→ ind) () lho rho
  ≤⇒tr≤ (s ←∨→ s₁) (∨→ ss) (∨→ ind) () lho rho
  ≤⇒tr≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (∨→ ind) (≤←∨→ eq eq₁) (hitsAtLeastOnce←∨→∨→ lho) (hitsAtLeastOnce←∨→∨→ rho)
    with truncSetLL s₁ ind | ho⇒¬trunc≡∅ s₁ ind lho | truncSetLL ss₁ ind | ho⇒¬trunc≡∅ ss₁ ind rho | ≤⇒tr≤ s₁ ss₁ ind eq₁ lho rho 
  ... | ∅ | e | r | g | t = ⊥-elim (e refl)
  ... | ¬∅ x | e | ∅ | g | t = ⊥-elim (g refl)
  ... | ¬∅ x | e | ¬∅ x₁ | g | t = t
  ≤⇒tr≤ ↓ ↓ (ind ←∂) eq lho rho = ≤↓
  ≤⇒tr≤ ↓ (ss ←∂) (ind ←∂) () lho rho
  ≤⇒tr≤ ↓ (∂→ ss) (ind ←∂) () lho rho
  ≤⇒tr≤ ↓ (ss ←∂→ ss₁) (ind ←∂) () lho rho
  ≤⇒tr≤ (s ←∂) ↓ (ind ←∂) eq lho rho = ≤↓
  ≤⇒tr≤ (s ←∂) (ss ←∂) (ind ←∂) (≤←∂ eq) (hitsAtLeastOnce←∂←∂ lho) (hitsAtLeastOnce←∂←∂ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq lho rho
  ... | ∅ | r | e | q | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | q | t = ⊥-elim (q refl)
  ... | ¬∅ x | r | ¬∅ x₁ | q | t = t
  ≤⇒tr≤ (s ←∂) (∂→ ss) (ind ←∂) () lho rho
  ≤⇒tr≤ (s ←∂) (ss ←∂→ ss₁) (ind ←∂) (≤d←∂ eq) (hitsAtLeastOnce←∂←∂ lho) (hitsAtLeastOnce←∂→←∂ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq lho rho
  ... | ∅ | r | q | e | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | e | t = ⊥-elim (e refl)
  ... | ¬∅ x | r | ¬∅ x₁ | e | t = t
  ≤⇒tr≤ (∂→ s) ss (ind ←∂) eq () rho
  ≤⇒tr≤ (s ←∂→ s₁) ↓ (ind ←∂) eq lho rho = ≤↓
  ≤⇒tr≤ (s ←∂→ s₁) (ss ←∂) (ind ←∂) () lho rho
  ≤⇒tr≤ (s ←∂→ s₁) (∂→ ss) (ind ←∂) () lho rho
  ≤⇒tr≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (ind ←∂) (≤←∂→ eq1 eq2) (hitsAtLeastOnce←∂→←∂ lho) (hitsAtLeastOnce←∂→←∂ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq1 lho rho 
  ... | ∅ | e | r | g | t = ⊥-elim (e refl)
  ... | ¬∅ x | e | ∅ | g | t = ⊥-elim (g refl)
  ... | ¬∅ x | e | ¬∅ x₁ | g | t = t
  ≤⇒tr≤ ↓ ↓ (∂→ ind) eq lho rho = ≤↓
  ≤⇒tr≤ ↓ (ss ←∂) (∂→ ind) () lho rho
  ≤⇒tr≤ ↓ (∂→ ss) (∂→ ind) () lho rho
  ≤⇒tr≤ ↓ (ss ←∂→ ss₁) (∂→ ind) () lho rho
  ≤⇒tr≤ (s ←∂) ss (∂→ ind) eq () rho
  ≤⇒tr≤ (∂→ s) ↓ (∂→ ind) eq lho rho = ≤↓
  ≤⇒tr≤ (∂→ s) (ss ←∂) (∂→ ind) () lho rho
  ≤⇒tr≤ (∂→ s) (∂→ ss) (∂→ ind) (≤∂→ eq) (hitsAtLeastOnce∂→∂→ lho) (hitsAtLeastOnce∂→∂→ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss ind | ho⇒¬trunc≡∅ ss ind rho | ≤⇒tr≤ s ss ind eq lho rho
  ... | ∅ | r | e | q | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | q | t = ⊥-elim (q refl)
  ... | ¬∅ x | r | ¬∅ x₁ | q | t = t
  ≤⇒tr≤ (∂→ s) (ss ←∂→ ss₁) (∂→ ind) (≤d∂→ eq) (hitsAtLeastOnce∂→∂→ lho) (hitsAtLeastOnce←∂→∂→ rho)
    with truncSetLL s ind | ho⇒¬trunc≡∅ s ind lho | truncSetLL ss₁ ind | ho⇒¬trunc≡∅ ss₁ ind rho | ≤⇒tr≤ s ss₁ ind eq lho rho
  ... | ∅ | r | q | e | t = ⊥-elim (r refl)
  ... | ¬∅ x | r | ∅ | e | t = ⊥-elim (e refl)
  ... | ¬∅ x | r | ¬∅ x₁ | e | t = t
  ≤⇒tr≤ (s ←∂→ s₁) ↓ (∂→ ind) eq lho rho = ≤↓
  ≤⇒tr≤ (s ←∂→ s₁) (ss ←∂) (∂→ ind) () lho rho
  ≤⇒tr≤ (s ←∂→ s₁) (∂→ ss) (∂→ ind) () lho rho
  ≤⇒tr≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (∂→ ind) (≤←∂→ eq eq₁) (hitsAtLeastOnce←∂→∂→ lho) (hitsAtLeastOnce←∂→∂→ rho)
    with truncSetLL s₁ ind | ho⇒¬trunc≡∅ s₁ ind lho | truncSetLL ss₁ ind | ho⇒¬trunc≡∅ ss₁ ind rho | ≤⇒tr≤ s₁ ss₁ ind eq₁ lho rho 
  ... | ∅ | e | r | g | t = ⊥-elim (e refl)
  ... | ¬∅ x | e | ∅ | g | t = ⊥-elim (g refl)
  ... | ¬∅ x | e | ¬∅ x₁ | g | t = t



-- extend trunc leads to a loss of data, making the result ≤ s.

  ≤s-extr : ∀{i u ll pll}→ (ind : IndexLL {i} {u} pll ll) → (s : SetLL ll) → (prf : hitsAtLeastOnce s ind)
            → extend ind (truncHOSetLL s ind prf) ≤s s
  ≤s-extr ↓ s prf = ≤s-refl s
  ≤s-extr {ll = li ∧ ri} {pll} (ind ←∧) ↓ hitsAtLeastOnce↓ = ≤↓
  ≤s-extr {ll = li ∧ ri} {pll} (ind ←∧) (s ←∧) (hitsAtLeastOnce←∧←∧ prf) 
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL li ind pll | replLL-id li ind pll refl | extendg ind x
  ... | .li | refl | w = ≤←∧ e
  ≤s-extr (ind ←∧) (∧→ s) ()
  ≤s-extr {ll = li ∧ ri} {pll} (ind ←∧) (s ←∧→ s₁) (hitsAtLeastOnce←∧→←∧ prf) 
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL li ind pll | replLL-id li ind pll refl | extendg ind x
  ... | .li | refl | w = ≤d←∧ e
  ≤s-extr (∧→ ind) ↓ ho = ≤↓
  ≤s-extr (∧→ ind) (s ←∧) ()
  ≤s-extr {ll = li ∧ ri} {pll} (∧→ ind) (∧→ s) (hitsAtLeastOnce∧→∧→ prf)  
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind x
  ... | .ri | refl | w = ≤∧→ e
  ≤s-extr {ll = li ∧ ri} {pll} (∧→ ind) (s₁ ←∧→ s) (hitsAtLeastOnce←∧→∧→ prf)
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind x
  ... | .ri | refl | w = ≤d∧→ e
  ≤s-extr (ind ←∨) ↓ ho = ≤↓
  ≤s-extr {ll = li ∨ ri} {pll} (ind ←∨) (s ←∨) (hitsAtLeastOnce←∨←∨ prf)  
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL li ind pll | replLL-id li ind pll refl | extendg ind x
  ... | .li | refl | w = ≤←∨ e
  ≤s-extr (ind ←∨) (∨→ s) ()
  ≤s-extr {ll = li ∨ ri} {pll} (ind ←∨) (s ←∨→ s₁) (hitsAtLeastOnce←∨→←∨ prf)
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL li ind pll | replLL-id li ind pll refl | extendg ind x
  ... | .li | refl | w = ≤d←∨ e
  ≤s-extr (∨→ ind) ↓ ho = ≤↓
  ≤s-extr (∨→ ind) (s ←∨) ()
  ≤s-extr {ll = li ∨ ri} {pll} (∨→ ind) (∨→ s) (hitsAtLeastOnce∨→∨→ prf)  
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind x
  ... | .ri | refl | w = ≤∨→ e
  ≤s-extr {ll = li ∨ ri} {pll} (∨→ ind) (s₁ ←∨→ s) (hitsAtLeastOnce←∨→∨→ prf)
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind x
  ... | .ri | refl | w = ≤d∨→ e
  ≤s-extr (ind ←∂) ↓ ho = ≤↓
  ≤s-extr {ll = li ∂ ri} {pll} (ind ←∂) (s ←∂) (hitsAtLeastOnce←∂←∂ prf)  
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL li ind pll | replLL-id li ind pll refl | extendg ind x
  ... | .li | refl | w = ≤←∂ e
  ≤s-extr (ind ←∂) (∂→ s) ()
  ≤s-extr {ll = li ∂ ri} {pll} (ind ←∂) (s ←∂→ s₁) (hitsAtLeastOnce←∂→←∂ prf)
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL li ind pll | replLL-id li ind pll refl | extendg ind x
  ... | .li | refl | w = ≤d←∂ e
  ≤s-extr (∂→ ind) ↓ ho = ≤↓
  ≤s-extr (∂→ ind) (s ←∂) ()
  ≤s-extr {ll = li ∂ ri} {pll} (∂→ ind) (∂→ s) (hitsAtLeastOnce∂→∂→ prf)  
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind x
  ... | .ri | refl | w = ≤∂→ e
  ≤s-extr {ll = li ∂ ri} {pll} (∂→ ind) (s₁ ←∂→ s) (hitsAtLeastOnce←∂→∂→ prf)
    with  truncSetLL s ind | ho⇒¬trunc≡∅ s ind prf | ≤s-extr ind s prf where
  ... | ∅ | r | e = ⊥-elim (r refl)
  ... | ¬∅ x | r | e with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind x
  ... | .ri | refl | w = ≤d∂→ e




-- Extending a set gives us onlyInside and hitsAtLeastOnce immediately because the rest is empty.

  ext⇒oi : ∀{i u pll ll} → ∀ s → (ind : IndexLL {i} {u} pll ll)
         → onlyInside (extend ind s) ind
  ext⇒oi {pll = pll} {(li ∧ _)} s (ind ←∧)
    with replLL li ind pll | replLL-id li ind pll refl | extendg ind s | ext⇒oi s ind 
  ... | .li | refl | e | q = onlyInsideC←∧←∧ q
  ext⇒oi {pll = pll} {(_ ∧ ri)} s (∧→ ind)
    with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind s | ext⇒oi s ind 
  ... | .ri | refl | e | q = onlyInsideC∧→∧→ q
  ext⇒oi {pll = pll} {(li ∨ _)} s (ind ←∨)
    with replLL li ind pll | replLL-id li ind pll refl | extendg ind s | ext⇒oi s ind 
  ... | .li | refl | e | q = onlyInsideC←∨←∨ q
  ext⇒oi {pll = pll} {(_ ∨ ri)} s (∨→ ind)
    with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind s | ext⇒oi s ind 
  ... | .ri | refl | e | q = onlyInsideC∨→∨→ q
  ext⇒oi {pll = pll} {(li ∂ _)} s (ind ←∂)
    with replLL li ind pll | replLL-id li ind pll refl | extendg ind s | ext⇒oi s ind 
  ... | .li | refl | e | q = onlyInsideC←∂←∂ q
  ext⇒oi {pll = pll} {(_ ∂ ri)} s (∂→ ind)
    with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind s | ext⇒oi s ind 
  ... | .ri | refl | e | q = onlyInsideC∂→∂→ q
  ext⇒oi s ↓ = onlyInsideCs↓

  ext⇒ho : ∀{i u pll ll} → ∀ s → (ind : IndexLL {i} {u} pll ll)
         → hitsAtLeastOnce (extend ind s) ind
  ext⇒ho s ind = oi⇒ho (extend ind s) ind (ext⇒oi s ind)



  ¬ho⇒ind+¬ho : ∀{i u pll rll ll} → (s : SetLL {i} {u} ll) → (ind : IndexLL pll ll)
              → ¬ (hitsAtLeastOnce s ind) → (lind : IndexLL rll pll)
              → ¬ (hitsAtLeastOnce s (ind +ᵢ lind))
  ¬ho⇒ind+¬ho ↓ (ind ←∧) ¬ho lind x = ¬ho hitsAtLeastOnce↓
  ¬ho⇒ind+¬ho (s ←∧) (ind ←∧) ¬ho lind (hitsAtLeastOnce←∧←∧ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∧←∧ z)) lind x
  ¬ho⇒ind+¬ho (∧→ s) (ind ←∧) ¬ho lind ()
  ¬ho⇒ind+¬ho (s ←∧→ s₁) (ind ←∧) ¬ho lind (hitsAtLeastOnce←∧→←∧ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∧→←∧ z)) lind x
  ¬ho⇒ind+¬ho ↓ (∧→ ind) ¬ho lind x = ¬ho hitsAtLeastOnce↓
  ¬ho⇒ind+¬ho (s ←∧) (∧→ ind) ¬ho lind ()
  ¬ho⇒ind+¬ho (∧→ s) (∧→ ind) ¬ho lind (hitsAtLeastOnce∧→∧→ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∧→∧→ z)) lind x
  ¬ho⇒ind+¬ho (s ←∧→ s₁) (∧→ ind) ¬ho lind (hitsAtLeastOnce←∧→∧→ x) = ¬ho⇒ind+¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∧→∧→ z)) lind x
  ¬ho⇒ind+¬ho ↓ (ind ←∨) ¬ho lind x = ¬ho hitsAtLeastOnce↓
  ¬ho⇒ind+¬ho (s ←∨) (ind ←∨) ¬ho lind (hitsAtLeastOnce←∨←∨ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∨←∨ z)) lind x
  ¬ho⇒ind+¬ho (∨→ s) (ind ←∨) ¬ho lind ()
  ¬ho⇒ind+¬ho (s ←∨→ s₁) (ind ←∨) ¬ho lind (hitsAtLeastOnce←∨→←∨ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∨→←∨ z)) lind x
  ¬ho⇒ind+¬ho ↓ (∨→ ind) ¬ho lind x = ¬ho hitsAtLeastOnce↓
  ¬ho⇒ind+¬ho (s ←∨) (∨→ ind) ¬ho lind ()
  ¬ho⇒ind+¬ho (∨→ s) (∨→ ind) ¬ho lind (hitsAtLeastOnce∨→∨→ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∨→∨→ z)) lind x
  ¬ho⇒ind+¬ho (s ←∨→ s₁) (∨→ ind) ¬ho lind (hitsAtLeastOnce←∨→∨→ x) = ¬ho⇒ind+¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∨→∨→ z)) lind x
  ¬ho⇒ind+¬ho ↓ (ind ←∂) ¬ho lind x = ¬ho hitsAtLeastOnce↓
  ¬ho⇒ind+¬ho (s ←∂) (ind ←∂) ¬ho lind (hitsAtLeastOnce←∂←∂ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∂←∂ z)) lind x
  ¬ho⇒ind+¬ho (∂→ s) (ind ←∂) ¬ho lind ()
  ¬ho⇒ind+¬ho (s ←∂→ s₁) (ind ←∂) ¬ho lind (hitsAtLeastOnce←∂→←∂ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∂→←∂ z)) lind x
  ¬ho⇒ind+¬ho ↓ (∂→ ind) ¬ho lind x = ¬ho hitsAtLeastOnce↓
  ¬ho⇒ind+¬ho (s ←∂) (∂→ ind) ¬ho lind ()
  ¬ho⇒ind+¬ho (∂→ s) (∂→ ind) ¬ho lind (hitsAtLeastOnce∂→∂→ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∂→∂→ z)) lind x
  ¬ho⇒ind+¬ho (s ←∂→ s₁) (∂→ ind) ¬ho lind (hitsAtLeastOnce←∂→∂→ x) = ¬ho⇒ind+¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∂→∂→ z)) lind x
  ¬ho⇒ind+¬ho ↓ ↓ ¬ho lind x = ¬ho hitsAtLeastOnce↓
  ¬ho⇒ind+¬ho (x ←∧) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce←∧↓
  ¬ho⇒ind+¬ho (∧→ x) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce∧→↓
  ¬ho⇒ind+¬ho (x ←∧→ x₁) ↓ ¬ho lind x₂ = ¬ho hitsAtLeastOnce←∧→↓
  ¬ho⇒ind+¬ho (x ←∨) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce←∨↓
  ¬ho⇒ind+¬ho (∨→ x) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce∨→↓
  ¬ho⇒ind+¬ho (x ←∨→ x₁) ↓ ¬ho lind x₂ = ¬ho hitsAtLeastOnce←∨→↓
  ¬ho⇒ind+¬ho (x ←∂) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce←∂↓
  ¬ho⇒ind+¬ho (∂→ x) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce∂→↓
  ¬ho⇒ind+¬ho (x ←∂→ x₁) ↓ ¬ho lind x₂ = ¬ho hitsAtLeastOnce←∂→↓
  
  



  ¬ord&ext⇒¬ho : ∀{i u pll rll ll tll} → ∀ (s : SetLL tll) → (ind : IndexLL {i} {u} pll ll)
        → (lind : IndexLL rll ll) → (nord : ¬ Orderedᵢ lind ind)
        → ¬ hitsAtLeastOnce (extendg ind s) (¬ord-morph lind ind tll (flipNotOrdᵢ nord))
  ¬ord&ext⇒¬ho s ↓ lind nord = λ _ → nord (b≤ᵢa ≤ᵢ↓)
  ¬ord&ext⇒¬ho s (ind ←∧) ↓ nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
  ¬ord&ext⇒¬ho {pll = pll} {_} {ll = li ∧ ri} {tll} s (ind ←∧) (lind ←∧) nord = hf where
  
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ←∧ x))
    nnord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ←∧ x))
  
    is = ¬ord&ext⇒¬ho s ind lind nnord

    hf : ¬ hitsAtLeastOnce (SetLL (_ ∧ ri) ∋ (extendg ind s ←∧)) ((¬ord-morph lind ind tll (flipNotOrdᵢ nnord)) ←∧)
    hf (hitsAtLeastOnce←∧←∧ x) = is x

  ¬ord&ext⇒¬ho s (ind ←∧) (∧→ lind) nord = λ ()
  ¬ord&ext⇒¬ho s (∧→ ind) ↓ nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
  ¬ord&ext⇒¬ho s (∧→ ind) (lind ←∧) nord = λ ()
  ¬ord&ext⇒¬ho {pll = pll} {_} {ll = li ∧ ri} {tll} s (∧→ ind) (∧→ lind) nord = hf where
  
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ∧→ x))
    nnord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ∧→ x))
  
    is = ¬ord&ext⇒¬ho s ind lind nnord
  
    hf : ¬ hitsAtLeastOnce (SetLL (li ∧ _) ∋ (∧→ extendg ind s)) (∧→ (¬ord-morph lind ind tll (flipNotOrdᵢ nnord)))
    hf (hitsAtLeastOnce∧→∧→ x) = is x
  ¬ord&ext⇒¬ho s (ind ←∨) ↓ nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
  ¬ord&ext⇒¬ho {pll = pll} {_} {ll = li ∨ ri} {tll} s (ind ←∨) (lind ←∨) nord = hf where
  
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ←∨ x))
    nnord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ←∨ x))
  
    is = ¬ord&ext⇒¬ho s ind lind nnord
  
    hf : ¬ hitsAtLeastOnce (SetLL (_ ∨ ri) ∋ (extendg ind s ←∨)) ((¬ord-morph lind ind tll (flipNotOrdᵢ nnord)) ←∨)
    hf (hitsAtLeastOnce←∨←∨ x) = is x
  
  ¬ord&ext⇒¬ho s (ind ←∨) (∨→ lind) nord = λ ()
  ¬ord&ext⇒¬ho s (∨→ ind) ↓ nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
  ¬ord&ext⇒¬ho s (∨→ ind) (lind ←∨) nord = λ ()
  ¬ord&ext⇒¬ho {pll = pll} {_} {ll = li ∨ ri} {tll} s (∨→ ind) (∨→ lind) nord = hf where
  
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ∨→ x))
    nnord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ∨→ x))
  
    is = ¬ord&ext⇒¬ho s ind lind nnord
  
    hf : ¬ hitsAtLeastOnce (SetLL (li ∨ _) ∋ (∨→ extendg ind s)) (∨→ (¬ord-morph lind ind tll (flipNotOrdᵢ nnord)))
    hf (hitsAtLeastOnce∨→∨→ x) = is x
  
  ¬ord&ext⇒¬ho s (ind ←∂) ↓ nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
  ¬ord&ext⇒¬ho {pll = pll} {_} {ll = li ∂ ri} {tll} s (ind ←∂) (lind ←∂) nord = hf where
  
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ←∂ x))
    nnord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ←∂ x))
  
    is = ¬ord&ext⇒¬ho s ind lind nnord
  
    hf : ¬ hitsAtLeastOnce (SetLL (_ ∂ ri) ∋ (extendg ind s ←∂)) ((¬ord-morph lind ind tll (flipNotOrdᵢ nnord)) ←∂)
    hf (hitsAtLeastOnce←∂←∂ x) = is x
  
  ¬ord&ext⇒¬ho s (ind ←∂) (∂→ lind) nord = λ ()
  ¬ord&ext⇒¬ho s (∂→ ind) ↓ nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
  ¬ord&ext⇒¬ho s (∂→ ind) (lind ←∂) nord = λ ()
  ¬ord&ext⇒¬ho {pll = pll} {_} {ll = li ∂ ri} {tll} s (∂→ ind) (∂→ lind) nord = hf where
  
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ∂→ x))
    nnord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ∂→ x))
  
    is = ¬ord&ext⇒¬ho s ind lind nnord
  
    hf : ¬ hitsAtLeastOnce (SetLL (li ∂ _) ∋ (∂→ extendg ind s)) (∂→ (¬ord-morph lind ind tll (flipNotOrdᵢ nnord)))
    hf (hitsAtLeastOnce∂→∂→ x) = is x
  
  


  
  ¬ord&¬ho-repl⇒¬ho : ∀{i u rll pll ll tll} → (lind : IndexLL {i} {u} rll ll) → (s : SetLL ll) → ∀{rs : SetLL tll}
        → ¬ (hitsAtLeastOnce s lind) → (ind : IndexLL pll ll)
        → (nord : ¬ Orderedᵢ lind ind)
        → ¬ (hitsAtLeastOnce (replacePartOf s to rs at ind) (¬ord-morph lind ind tll (flipNotOrdᵢ nord)))
  ¬ord&¬ho-repl⇒¬ho ↓ s ¬ho ind ¬ord = λ _ → ¬ord (a≤ᵢb ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (lind ←∧) ↓ ¬ho ind ¬ord = λ _ → ¬ho hitsAtLeastOnce↓
  ¬ord&¬ho-repl⇒¬ho (lind ←∧) (s ←∧) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (lind ←∧) (s ←∧) {rs} ¬ho (ind ←∧) ¬ord x
                                   with ¬ord&¬ho-repl⇒¬ho lind s {rs} (λ z → ¬ho (hitsAtLeastOnce←∧←∧ z)) ind hf where
    hf : ¬ Orderedᵢ lind ind
    hf (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ←∧ x))
    hf (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ←∧ x))
  ¬ord&¬ho-repl⇒¬ho (lind ←∧) (s ←∧) {rs} ¬ho (ind ←∧) ¬ord (hitsAtLeastOnce←∧←∧ x) | r = ⊥-elim (r x)
  ¬ord&¬ho-repl⇒¬ho (lind ←∧) (s ←∧) ¬ho (∧→ ind) ¬ord (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ x)
  ¬ord&¬ho-repl⇒¬ho (lind ←∧) (∧→ s) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho {tll = tll} (lind ←∧) (∧→ s) {rs} ¬ho (ind ←∧) ¬ord = hf where
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ←∧ x))
    nnord (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ←∧ x))
    
    h1 = ¬ord&ext⇒¬ho rs ind lind nnord
  
    hf : ¬ hitsAtLeastOnce (extendg ind rs ←∧→ s) (¬ord-morph (lind ←∧) (ind ←∧) tll (flipNotOrdᵢ ¬ord))
    hf (hitsAtLeastOnce←∧→←∧ x) = h1 x
  ¬ord&¬ho-repl⇒¬ho (lind ←∧) (∧→ s) ¬ho (∧→ ind) ¬ord = λ ()
  ¬ord&¬ho-repl⇒¬ho (lind ←∧) (s ←∧→ s₁) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (lind ←∧) (s ←∧→ s₁) {rs} ¬ho (ind ←∧) ¬ord (hitsAtLeastOnce←∧→←∧ x) = is x where
    hf : ¬ hitsAtLeastOnce s lind
    hf x = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
    hf2 : ¬ Orderedᵢ lind ind
    hf2 (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ←∧ x))
    hf2 (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ←∧ x))
    
    is = ¬ord&¬ho-repl⇒¬ho lind s {rs} hf ind hf2
  ¬ord&¬ho-repl⇒¬ho (lind ←∧) (s ←∧→ s₁) {rs} ¬ho (∧→ ind) ¬ord (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  ¬ord&¬ho-repl⇒¬ho (∧→ lind) ↓ ¬ho ind ¬ord = λ _ → ¬ho hitsAtLeastOnce↓
  ¬ord&¬ho-repl⇒¬ho (∧→ lind) (s ←∧) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (∧→ lind) (s ←∧) ¬ho (ind ←∧) ¬ord = λ ()
  ¬ord&¬ho-repl⇒¬ho {tll = tll} (∧→ lind) (s ←∧) {rs} ¬ho (∧→ ind) ¬ord = hf where
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ∧→ x))
    nnord (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ∧→ x))
    
    h1 = ¬ord&ext⇒¬ho rs ind lind nnord
  
    hf : ¬ hitsAtLeastOnce (s ←∧→ extendg ind rs) (¬ord-morph (∧→ lind) (∧→ ind) tll (flipNotOrdᵢ ¬ord))
    hf (hitsAtLeastOnce←∧→∧→ x) = h1 x
  
  ¬ord&¬ho-repl⇒¬ho (∧→ lind) (∧→ s) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (∧→ lind) (∧→ s) ¬ho (ind ←∧) ¬ord (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce∧→∧→ x)
  ¬ord&¬ho-repl⇒¬ho (∧→ lind) (∧→ s) {rs} ¬ho (∧→ ind) ¬ord x
                             with ¬ord&¬ho-repl⇒¬ho lind s {rs} (λ z → ¬ho (hitsAtLeastOnce∧→∧→ z)) ind hf where
    hf : ¬ Orderedᵢ lind ind
    hf (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ∧→ x))
    hf (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ∧→ x))
  ¬ord&¬ho-repl⇒¬ho (∧→ lind) (∧→ s) ¬ho (∧→ ind) ¬ord (hitsAtLeastOnce∧→∧→ x) | r = r x
  ¬ord&¬ho-repl⇒¬ho (∧→ lind) (s ←∧→ s₁) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) ¬ord (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  ¬ord&¬ho-repl⇒¬ho (∧→ lind) (s ←∧→ s₁) {rs} ¬ho (∧→ ind) ¬ord (hitsAtLeastOnce←∧→∧→ x) = is x where
    hf : ¬ hitsAtLeastOnce s₁ lind
    hf x = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
    hf2 : ¬ Orderedᵢ lind ind
    hf2 (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ∧→ x))
    hf2 (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ∧→ x))
    
    is = ¬ord&¬ho-repl⇒¬ho lind s₁ {rs} hf ind hf2
  ¬ord&¬ho-repl⇒¬ho (lind ←∨) ↓ ¬ho ind ¬ord = λ _ → ¬ho hitsAtLeastOnce↓
  ¬ord&¬ho-repl⇒¬ho (lind ←∨) (s ←∨) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (lind ←∨) (s ←∨) {rs} ¬ho (ind ←∨) ¬ord x
                                   with ¬ord&¬ho-repl⇒¬ho lind s {rs} (λ z → ¬ho (hitsAtLeastOnce←∨←∨ z)) ind hf where
    hf : ¬ Orderedᵢ lind ind
    hf (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ←∨ x))
    hf (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ←∨ x))
  ¬ord&¬ho-repl⇒¬ho (lind ←∨) (s ←∨) {rs} ¬ho (ind ←∨) ¬ord (hitsAtLeastOnce←∨←∨ x) | r = ⊥-elim (r x)
  ¬ord&¬ho-repl⇒¬ho (lind ←∨) (s ←∨) ¬ho (∨→ ind) ¬ord (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨←∨ x)
  ¬ord&¬ho-repl⇒¬ho (lind ←∨) (∨→ s) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho {tll = tll} (lind ←∨) (∨→ s) {rs} ¬ho (ind ←∨) ¬ord = hf where
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ←∨ x))
    nnord (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ←∨ x))
    
    h1 = ¬ord&ext⇒¬ho rs ind lind nnord
  
    hf : ¬ hitsAtLeastOnce (extendg ind rs ←∨→ s) (¬ord-morph (lind ←∨) (ind ←∨) tll (flipNotOrdᵢ ¬ord))
    hf (hitsAtLeastOnce←∨→←∨ x) = h1 x
  ¬ord&¬ho-repl⇒¬ho (lind ←∨) (∨→ s) ¬ho (∨→ ind) ¬ord = λ ()
  ¬ord&¬ho-repl⇒¬ho (lind ←∨) (s ←∨→ s₁) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (lind ←∨) (s ←∨→ s₁) {rs} ¬ho (ind ←∨) ¬ord (hitsAtLeastOnce←∨→←∨ x) = is x where
    hf : ¬ hitsAtLeastOnce s lind
    hf x = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
    hf2 : ¬ Orderedᵢ lind ind
    hf2 (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ←∨ x))
    hf2 (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ←∨ x))
    
    is = ¬ord&¬ho-repl⇒¬ho lind s {rs} hf ind hf2
  ¬ord&¬ho-repl⇒¬ho (lind ←∨) (s ←∨→ s₁) {rs} ¬ho (∨→ ind) ¬ord (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  ¬ord&¬ho-repl⇒¬ho (∨→ lind) ↓ ¬ho ind ¬ord = λ _ → ¬ho hitsAtLeastOnce↓
  ¬ord&¬ho-repl⇒¬ho (∨→ lind) (s ←∨) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (∨→ lind) (s ←∨) ¬ho (ind ←∨) ¬ord = λ ()
  ¬ord&¬ho-repl⇒¬ho {tll = tll} (∨→ lind) (s ←∨) {rs} ¬ho (∨→ ind) ¬ord = hf where
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ∨→ x))
    nnord (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ∨→ x))
    
    h1 = ¬ord&ext⇒¬ho rs ind lind nnord
  
    hf : ¬ hitsAtLeastOnce (s ←∨→ extendg ind rs) (¬ord-morph (∨→ lind) (∨→ ind) tll (flipNotOrdᵢ ¬ord))
    hf (hitsAtLeastOnce←∨→∨→ x) = h1 x
  
  ¬ord&¬ho-repl⇒¬ho (∨→ lind) (∨→ s) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (∨→ lind) (∨→ s) ¬ho (ind ←∨) ¬ord (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ x)
  ¬ord&¬ho-repl⇒¬ho (∨→ lind) (∨→ s) {rs} ¬ho (∨→ ind) ¬ord x
                             with ¬ord&¬ho-repl⇒¬ho lind s {rs} (λ z → ¬ho (hitsAtLeastOnce∨→∨→ z)) ind hf where
    hf : ¬ Orderedᵢ lind ind
    hf (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ∨→ x))
    hf (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ∨→ x))
  ¬ord&¬ho-repl⇒¬ho (∨→ lind) (∨→ s) ¬ho (∨→ ind) ¬ord (hitsAtLeastOnce∨→∨→ x) | r = r x
  ¬ord&¬ho-repl⇒¬ho (∨→ lind) (s ←∨→ s₁) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) ¬ord (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  ¬ord&¬ho-repl⇒¬ho (∨→ lind) (s ←∨→ s₁) {rs} ¬ho (∨→ ind) ¬ord (hitsAtLeastOnce←∨→∨→ x) = is x where
    hf : ¬ hitsAtLeastOnce s₁ lind
    hf x = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
    hf2 : ¬ Orderedᵢ lind ind
    hf2 (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ∨→ x))
    hf2 (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ∨→ x))
    
    is = ¬ord&¬ho-repl⇒¬ho lind s₁ {rs} hf ind hf2
  ¬ord&¬ho-repl⇒¬ho (lind ←∂) ↓ ¬ho ind ¬ord = λ _ → ¬ho hitsAtLeastOnce↓
  ¬ord&¬ho-repl⇒¬ho (lind ←∂) (s ←∂) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (lind ←∂) (s ←∂) {rs} ¬ho (ind ←∂) ¬ord x
                                   with ¬ord&¬ho-repl⇒¬ho lind s {rs} (λ z → ¬ho (hitsAtLeastOnce←∂←∂ z)) ind hf where
    hf : ¬ Orderedᵢ lind ind
    hf (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ←∂ x))
    hf (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ←∂ x))
  ¬ord&¬ho-repl⇒¬ho (lind ←∂) (s ←∂) {rs} ¬ho (ind ←∂) ¬ord (hitsAtLeastOnce←∂←∂ x) | r = ⊥-elim (r x)
  ¬ord&¬ho-repl⇒¬ho (lind ←∂) (s ←∂) ¬ho (∂→ ind) ¬ord (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂←∂ x)
  ¬ord&¬ho-repl⇒¬ho (lind ←∂) (∂→ s) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho {tll = tll} (lind ←∂) (∂→ s) {rs} ¬ho (ind ←∂) ¬ord = hf where
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ←∂ x))
    nnord (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ←∂ x))
    
    h1 = ¬ord&ext⇒¬ho rs ind lind nnord
  
    hf : ¬ hitsAtLeastOnce (extendg ind rs ←∂→ s) (¬ord-morph (lind ←∂) (ind ←∂) tll (flipNotOrdᵢ ¬ord))
    hf (hitsAtLeastOnce←∂→←∂ x) = h1 x
  ¬ord&¬ho-repl⇒¬ho (lind ←∂) (∂→ s) ¬ho (∂→ ind) ¬ord = λ ()
  ¬ord&¬ho-repl⇒¬ho (lind ←∂) (s ←∂→ s₁) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (lind ←∂) (s ←∂→ s₁) {rs} ¬ho (ind ←∂) ¬ord (hitsAtLeastOnce←∂→←∂ x) = is x where
    hf : ¬ hitsAtLeastOnce s lind
    hf x = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
    hf2 : ¬ Orderedᵢ lind ind
    hf2 (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ←∂ x))
    hf2 (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ←∂ x))
    
    is = ¬ord&¬ho-repl⇒¬ho lind s {rs} hf ind hf2
  ¬ord&¬ho-repl⇒¬ho (lind ←∂) (s ←∂→ s₁) {rs} ¬ho (∂→ ind) ¬ord (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  ¬ord&¬ho-repl⇒¬ho (∂→ lind) ↓ ¬ho ind ¬ord = λ _ → ¬ho hitsAtLeastOnce↓
  ¬ord&¬ho-repl⇒¬ho (∂→ lind) (s ←∂) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (∂→ lind) (s ←∂) ¬ho (ind ←∂) ¬ord = λ ()
  ¬ord&¬ho-repl⇒¬ho {tll = tll} (∂→ lind) (s ←∂) {rs} ¬ho (∂→ ind) ¬ord = hf where
    nnord : ¬ Orderedᵢ lind ind
    nnord (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ∂→ x))
    nnord (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ∂→ x))
    
    h1 = ¬ord&ext⇒¬ho rs ind lind nnord
  
    hf : ¬ hitsAtLeastOnce (s ←∂→ extendg ind rs) (¬ord-morph (∂→ lind) (∂→ ind) tll (flipNotOrdᵢ ¬ord))
    hf (hitsAtLeastOnce←∂→∂→ x) = h1 x
  
  ¬ord&¬ho-repl⇒¬ho (∂→ lind) (∂→ s) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (∂→ lind) (∂→ s) ¬ho (ind ←∂) ¬ord (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce∂→∂→ x)
  ¬ord&¬ho-repl⇒¬ho (∂→ lind) (∂→ s) {rs} ¬ho (∂→ ind) ¬ord x
                             with ¬ord&¬ho-repl⇒¬ho lind s {rs} (λ z → ¬ho (hitsAtLeastOnce∂→∂→ z)) ind hf where
    hf : ¬ Orderedᵢ lind ind
    hf (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ∂→ x))
    hf (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ∂→ x))
  ¬ord&¬ho-repl⇒¬ho (∂→ lind) (∂→ s) ¬ho (∂→ ind) ¬ord (hitsAtLeastOnce∂→∂→ x) | r = r x
  ¬ord&¬ho-repl⇒¬ho (∂→ lind) (s ←∂→ s₁) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
  ¬ord&¬ho-repl⇒¬ho (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) ¬ord (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  ¬ord&¬ho-repl⇒¬ho (∂→ lind) (s ←∂→ s₁) {rs} ¬ho (∂→ ind) ¬ord (hitsAtLeastOnce←∂→∂→ x) = is x where
    hf : ¬ hitsAtLeastOnce s₁ lind
    hf x = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
    hf2 : ¬ Orderedᵢ lind ind
    hf2 (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ∂→ x))
    hf2 (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ∂→ x))
    
    is = ¬ord&¬ho-repl⇒¬ho lind s₁ {rs} hf ind hf2
  
  
  


-- Not being Ordered is only necessary to morph the type of the index. but this statement is true in general.
¬ord&¬ho-del⇒¬ho : ∀{i u rll pll ll tll} → (lind : IndexLL {i} {u} rll ll) → (s : SetLL ll)
      → ¬ (hitsAtLeastOnce s lind) → (ind : IndexLL pll ll) → ∀{ds}
      → (nord : ¬ Orderedᵢ lind ind)
      → ¬∅ ds ≡ del s ind tll
      → ¬ (hitsAtLeastOnce ds (¬ord-morph lind ind tll (flipNotOrdᵢ nord)))
¬ord&¬ho-del⇒¬ho ↓ s ¬ho ind nord eqd = λ _ → nord (a≤ᵢb ≤ᵢ↓)
¬ord&¬ho-del⇒¬ho (lind ←∧) s ¬ho ↓ nord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
¬ord&¬ho-del⇒¬ho (lind ←∧) ↓ ¬ho (ind ←∧) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (s ←∧) ¬ho (ind ←∧) nord eqd y with del s ind tll | inspect (del s ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (s ←∧) ¬ho (ind ←∧) nord () y | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (s ←∧) ¬ho (ind ←∧) nord refl (hitsAtLeastOnce←∧←∧ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ←∧ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ←∧ x₁))

  hf2 : ¬ hitsAtLeastOnce s lind
  hf2 x = ¬ho (hitsAtLeastOnce←∧←∧ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s hf2 ind hf (sym eq)
¬ord&¬ho-del⇒¬ho (lind ←∧) (∧→ s) ¬ho (ind ←∧) nord refl = λ ()
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (ind ←∧) nord eqd y with del s ind tll | inspect (del s ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (ind ←∧) nord refl () | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (ind ←∧) nord refl (hitsAtLeastOnce←∧→←∧ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ←∧ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ←∧ x₁))

  hf2 : ¬ hitsAtLeastOnce s lind
  hf2 x = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s hf2 ind hf (sym eq)
¬ord&¬ho-del⇒¬ho (lind ←∧) ↓ ¬ho (∧→ ind) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho (lind ←∧) (s ←∧) ¬ho (∧→ ind) nord refl (hitsAtLeastOnce←∧←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ x)
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (∧→ s) ¬ho (∧→ ind) nord eqd with del s ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (∧→ s) ¬ho (∧→ ind) nord () | ∅
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (∧→ s) ¬ho (∧→ ind) nord refl | ¬∅ x = λ ()
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (∧→ ind) nord eqd y with del s₁ ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (∧→ ind) nord refl (hitsAtLeastOnce←∧←∧ y) | ∅ = ¬ho (hitsAtLeastOnce←∧→←∧ y)
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (∧→ ind) nord refl (hitsAtLeastOnce←∧→←∧ y) | ¬∅ x = ¬ho (hitsAtLeastOnce←∧→←∧ y)
¬ord&¬ho-del⇒¬ho (∧→ lind) s ¬ho ↓ nord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
¬ord&¬ho-del⇒¬ho (∧→ lind) ↓ ¬ho (ind ←∧) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (s ←∧) ¬ho (ind ←∧) nord eqd with del s ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (s ←∧) ¬ho (ind ←∧) nord () | ∅
¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (s ←∧) ¬ho (ind ←∧) nord refl | ¬∅ x = λ ()
¬ord&¬ho-del⇒¬ho (∧→ lind) (∧→ s) ¬ho (ind ←∧) nord refl (hitsAtLeastOnce∧→∧→ x) = ¬ho (hitsAtLeastOnce∧→∧→ x)
¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) nord eqd y with del s ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) nord refl (hitsAtLeastOnce∧→∧→ y) | ∅ = ¬ho (hitsAtLeastOnce←∧→∧→ y)
¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) nord refl (hitsAtLeastOnce←∧→∧→ y) | ¬∅ x = ¬ho (hitsAtLeastOnce←∧→∧→ y)
¬ord&¬ho-del⇒¬ho (∧→ lind) ↓ ¬ho (∧→ ind) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho (∧→ lind) (s ←∧) ¬ho (∧→ ind) nord refl = λ ()
¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (∧→ s) ¬ho (∧→ ind) nord eqd y with del s ind tll | inspect (del s ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (∧→ s) ¬ho (∧→ ind) nord () y | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (∧→ s) ¬ho (∧→ ind) nord refl (hitsAtLeastOnce∧→∧→ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ∧→ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ∧→ x₁))

  hf2 : ¬ hitsAtLeastOnce s lind
  hf2 x = ¬ho (hitsAtLeastOnce∧→∧→ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s hf2 ind hf (sym eq)

¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (∧→ ind) nord eqd y with del s₁ ind tll | inspect (del s₁ ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (∧→ ind) nord refl () | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (∧→ ind) nord refl (hitsAtLeastOnce←∧→∧→ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ∧→ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ∧→ x₁))

  hf2 : ¬ hitsAtLeastOnce s₁ lind
  hf2 x = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s₁ hf2 ind hf (sym eq)

¬ord&¬ho-del⇒¬ho (lind ←∨) s ¬ho ↓ nord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
¬ord&¬ho-del⇒¬ho (lind ←∨) ↓ ¬ho (ind ←∨) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (s ←∨) ¬ho (ind ←∨) nord eqd y with del s ind tll | inspect (del s ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (s ←∨) ¬ho (ind ←∨) nord () y | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (s ←∨) ¬ho (ind ←∨) nord refl (hitsAtLeastOnce←∨←∨ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ←∨ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ←∨ x₁))

  hf2 : ¬ hitsAtLeastOnce s lind
  hf2 x = ¬ho (hitsAtLeastOnce←∨←∨ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s hf2 ind hf (sym eq)
¬ord&¬ho-del⇒¬ho (lind ←∨) (∨→ s) ¬ho (ind ←∨) nord refl = λ ()
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (ind ←∨) nord eqd y with del s ind tll | inspect (del s ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (ind ←∨) nord refl () | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (ind ←∨) nord refl (hitsAtLeastOnce←∨→←∨ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ←∨ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ←∨ x₁))

  hf2 : ¬ hitsAtLeastOnce s lind
  hf2 x = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s hf2 ind hf (sym eq)
¬ord&¬ho-del⇒¬ho (lind ←∨) ↓ ¬ho (∨→ ind) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho (lind ←∨) (s ←∨) ¬ho (∨→ ind) nord refl (hitsAtLeastOnce←∨←∨ x) = ¬ho (hitsAtLeastOnce←∨←∨ x)
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (∨→ s) ¬ho (∨→ ind) nord eqd with del s ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (∨→ s) ¬ho (∨→ ind) nord () | ∅
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (∨→ s) ¬ho (∨→ ind) nord refl | ¬∅ x = λ ()
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (∨→ ind) nord eqd y with del s₁ ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (∨→ ind) nord refl (hitsAtLeastOnce←∨←∨ y) | ∅ = ¬ho (hitsAtLeastOnce←∨→←∨ y)
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (∨→ ind) nord refl (hitsAtLeastOnce←∨→←∨ y) | ¬∅ x = ¬ho (hitsAtLeastOnce←∨→←∨ y)
¬ord&¬ho-del⇒¬ho (∨→ lind) s ¬ho ↓ nord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
¬ord&¬ho-del⇒¬ho (∨→ lind) ↓ ¬ho (ind ←∨) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (s ←∨) ¬ho (ind ←∨) nord eqd with del s ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (s ←∨) ¬ho (ind ←∨) nord () | ∅
¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (s ←∨) ¬ho (ind ←∨) nord refl | ¬∅ x = λ ()
¬ord&¬ho-del⇒¬ho (∨→ lind) (∨→ s) ¬ho (ind ←∨) nord refl (hitsAtLeastOnce∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ x)
¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) nord eqd y with del s ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) nord refl (hitsAtLeastOnce∨→∨→ y) | ∅ = ¬ho (hitsAtLeastOnce←∨→∨→ y)
¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) nord refl (hitsAtLeastOnce←∨→∨→ y) | ¬∅ x = ¬ho (hitsAtLeastOnce←∨→∨→ y)
¬ord&¬ho-del⇒¬ho (∨→ lind) ↓ ¬ho (∨→ ind) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho (∨→ lind) (s ←∨) ¬ho (∨→ ind) nord refl = λ ()
¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (∨→ s) ¬ho (∨→ ind) nord eqd y with del s ind tll | inspect (del s ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (∨→ s) ¬ho (∨→ ind) nord () y | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (∨→ s) ¬ho (∨→ ind) nord refl (hitsAtLeastOnce∨→∨→ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ∨→ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ∨→ x₁))

  hf2 : ¬ hitsAtLeastOnce s lind
  hf2 x = ¬ho (hitsAtLeastOnce∨→∨→ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s hf2 ind hf (sym eq)

¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (∨→ ind) nord eqd y with del s₁ ind tll | inspect (del s₁ ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (∨→ ind) nord refl () | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (∨→ ind) nord refl (hitsAtLeastOnce←∨→∨→ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ∨→ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ∨→ x₁))

  hf2 : ¬ hitsAtLeastOnce s₁ lind
  hf2 x = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s₁ hf2 ind hf (sym eq)

¬ord&¬ho-del⇒¬ho (lind ←∂) s ¬ho ↓ nord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
¬ord&¬ho-del⇒¬ho (lind ←∂) ↓ ¬ho (ind ←∂) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (s ←∂) ¬ho (ind ←∂) nord eqd y with del s ind tll | inspect (del s ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (s ←∂) ¬ho (ind ←∂) nord () y | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (s ←∂) ¬ho (ind ←∂) nord refl (hitsAtLeastOnce←∂←∂ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ←∂ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ←∂ x₁))

  hf2 : ¬ hitsAtLeastOnce s lind
  hf2 x = ¬ho (hitsAtLeastOnce←∂←∂ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s hf2 ind hf (sym eq)
¬ord&¬ho-del⇒¬ho (lind ←∂) (∂→ s) ¬ho (ind ←∂) nord refl = λ ()
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (ind ←∂) nord eqd y with del s ind tll | inspect (del s ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (ind ←∂) nord refl () | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (ind ←∂) nord refl (hitsAtLeastOnce←∂→←∂ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ←∂ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ←∂ x₁))

  hf2 : ¬ hitsAtLeastOnce s lind
  hf2 x = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s hf2 ind hf (sym eq)
¬ord&¬ho-del⇒¬ho (lind ←∂) ↓ ¬ho (∂→ ind) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho (lind ←∂) (s ←∂) ¬ho (∂→ ind) nord refl (hitsAtLeastOnce←∂←∂ x) = ¬ho (hitsAtLeastOnce←∂←∂ x)
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (∂→ s) ¬ho (∂→ ind) nord eqd with del s ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (∂→ s) ¬ho (∂→ ind) nord () | ∅
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (∂→ s) ¬ho (∂→ ind) nord refl | ¬∅ x = λ ()
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (∂→ ind) nord eqd y with del s₁ ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (∂→ ind) nord refl (hitsAtLeastOnce←∂←∂ y) | ∅ = ¬ho (hitsAtLeastOnce←∂→←∂ y)
¬ord&¬ho-del⇒¬ho {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (∂→ ind) nord refl (hitsAtLeastOnce←∂→←∂ y) | ¬∅ x = ¬ho (hitsAtLeastOnce←∂→←∂ y)
¬ord&¬ho-del⇒¬ho (∂→ lind) s ¬ho ↓ nord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
¬ord&¬ho-del⇒¬ho (∂→ lind) ↓ ¬ho (ind ←∂) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (s ←∂) ¬ho (ind ←∂) nord eqd with del s ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (s ←∂) ¬ho (ind ←∂) nord () | ∅
¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (s ←∂) ¬ho (ind ←∂) nord refl | ¬∅ x = λ ()
¬ord&¬ho-del⇒¬ho (∂→ lind) (∂→ s) ¬ho (ind ←∂) nord refl (hitsAtLeastOnce∂→∂→ x) = ¬ho (hitsAtLeastOnce∂→∂→ x)
¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) nord eqd y with del s ind tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) nord refl (hitsAtLeastOnce∂→∂→ y) | ∅ = ¬ho (hitsAtLeastOnce←∂→∂→ y)
¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) nord refl (hitsAtLeastOnce←∂→∂→ y) | ¬∅ x = ¬ho (hitsAtLeastOnce←∂→∂→ y)
¬ord&¬ho-del⇒¬ho (∂→ lind) ↓ ¬ho (∂→ ind) nord eqd = λ _ → ¬ho hitsAtLeastOnce↓
¬ord&¬ho-del⇒¬ho (∂→ lind) (s ←∂) ¬ho (∂→ ind) nord refl = λ ()
¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (∂→ s) ¬ho (∂→ ind) nord eqd y with del s ind tll | inspect (del s ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (∂→ s) ¬ho (∂→ ind) nord () y | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (∂→ s) ¬ho (∂→ ind) nord refl (hitsAtLeastOnce∂→∂→ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ∂→ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ∂→ x₁))

  hf2 : ¬ hitsAtLeastOnce s lind
  hf2 x = ¬ho (hitsAtLeastOnce∂→∂→ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s hf2 ind hf (sym eq)

¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (∂→ ind) nord eqd y with del s₁ ind tll | inspect (del s₁ ind) tll
¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (∂→ ind) nord refl () | ∅ | r
¬ord&¬ho-del⇒¬ho {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (∂→ ind) nord refl (hitsAtLeastOnce←∂→∂→ y) | ¬∅ x | [ eq ] = is y where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = nord (a≤ᵢb (≤ᵢ∂→ x₁))
  hf (b≤ᵢa x₁) = nord (b≤ᵢa (≤ᵢ∂→ x₁))

  hf2 : ¬ hitsAtLeastOnce s₁ lind
  hf2 x = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  is =  ¬ord&¬ho-del⇒¬ho lind s₁ hf2 ind hf (sym eq)


 
  
  
module _ where

  open import IndexLLProp
  
  ho-trans : ∀{i u pll rll ll} → ∀ s → (ind1 : IndexLL {i} {u} pll ll) → (ind2 : IndexLL rll pll)
         → (ho1 : hitsAtLeastOnce s ind1) → hitsAtLeastOnce (truncHOSetLL s ind1 ho1) ind2
         → hitsAtLeastOnce s (ind1 +ᵢ ind2)
  ho-trans ↓ ind ind2 ho1 ho2 = hitsAtLeastOnce↓
  ho-trans (s ←∧) ↓ ind2 ho1 ho2 = ho2
  ho-trans (s ←∧) (ind ←∧) ind2 (hitsAtLeastOnce←∧←∧ ho1) ho2 = hitsAtLeastOnce←∧←∧ r where
    r = ho-trans s ind ind2 ho1 ho2
  ho-trans (s ←∧) (∧→ ind) ind2 () ho2
  ho-trans (∧→ s) ↓ ind2 ho1 ho2 = ho2
  ho-trans (∧→ s) (ind ←∧) ind2 () ho2
  ho-trans (∧→ s) (∧→ ind) ind2 (hitsAtLeastOnce∧→∧→ ho1) ho2 = hitsAtLeastOnce∧→∧→ r where
    r = ho-trans s ind ind2 ho1 ho2
  ho-trans (s ←∧→ s₁) ↓ ind2 ho1 ho2 = ho2
  ho-trans (s ←∧→ s₁) (ind ←∧) ind2 (hitsAtLeastOnce←∧→←∧ ho1) ho2 = hitsAtLeastOnce←∧→←∧ r where
    r = ho-trans s ind ind2 ho1 ho2
  ho-trans (s ←∧→ s₁) (∧→ ind) ind2 (hitsAtLeastOnce←∧→∧→ ho1) ho2 = hitsAtLeastOnce←∧→∧→ r where
    r = ho-trans s₁ ind ind2 ho1 ho2
  ho-trans (s ←∨) ↓ ind2 ho1 ho2 = ho2
  ho-trans (s ←∨) (ind ←∨) ind2 (hitsAtLeastOnce←∨←∨ ho1) ho2 = hitsAtLeastOnce←∨←∨ r where
    r = ho-trans s ind ind2 ho1 ho2
  ho-trans (s ←∨) (∨→ ind) ind2 () ho2
  ho-trans (∨→ s) ↓ ind2 ho1 ho2 = ho2
  ho-trans (∨→ s) (ind ←∨) ind2 () ho2
  ho-trans (∨→ s) (∨→ ind) ind2 (hitsAtLeastOnce∨→∨→ ho1) ho2 = hitsAtLeastOnce∨→∨→ r where
    r = ho-trans s ind ind2 ho1 ho2
  ho-trans (s ←∨→ s₁) ↓ ind2 ho1 ho2 = ho2
  ho-trans (s ←∨→ s₁) (ind ←∨) ind2 (hitsAtLeastOnce←∨→←∨ ho1) ho2 = hitsAtLeastOnce←∨→←∨ r where
    r = ho-trans s ind ind2 ho1 ho2
  ho-trans (s ←∨→ s₁) (∨→ ind) ind2 (hitsAtLeastOnce←∨→∨→ ho1) ho2 = hitsAtLeastOnce←∨→∨→ r where
    r = ho-trans s₁ ind ind2 ho1 ho2
  ho-trans (s ←∂) ↓ ind2 ho1 ho2 = ho2
  ho-trans (s ←∂) (ind ←∂) ind2 (hitsAtLeastOnce←∂←∂ ho1) ho2 = hitsAtLeastOnce←∂←∂ r where
    r = ho-trans s ind ind2 ho1 ho2
  ho-trans (s ←∂) (∂→ ind) ind2 () ho2
  ho-trans (∂→ s) ↓ ind2 ho1 ho2 = ho2
  ho-trans (∂→ s) (ind ←∂) ind2 () ho2
  ho-trans (∂→ s) (∂→ ind) ind2 (hitsAtLeastOnce∂→∂→ ho1) ho2 = hitsAtLeastOnce∂→∂→ r where
    r = ho-trans s ind ind2 ho1 ho2
  ho-trans (s ←∂→ s₁) ↓ ind2 ho1 ho2 = ho2
  ho-trans (s ←∂→ s₁) (ind ←∂) ind2 (hitsAtLeastOnce←∂→←∂ ho1) ho2 = hitsAtLeastOnce←∂→←∂ r where
    r = ho-trans s ind ind2 ho1 ho2
  ho-trans (s ←∂→ s₁) (∂→ ind) ind2 (hitsAtLeastOnce←∂→∂→ ho1) ho2 = hitsAtLeastOnce←∂→∂→ r where
    r = ho-trans s₁ ind ind2 ho1 ho2


  oi-trans : ∀{i u pll rll ll} → ∀ s → (ind1 : IndexLL {i} {u} pll ll) → (ind2 : IndexLL rll pll)
         → (oi1 : onlyInside s ind1) → onlyInside (truncHOSetLL s ind1 (oi⇒ho s ind1 oi1)) ind2
         → onlyInside s (ind1 +ᵢ ind2)
  oi-trans ↓ ↓ ind2 oi1 oi2 = oi2
  oi-trans ↓ (x ←∧) ind2 () oi2
  oi-trans ↓ (∧→ x) ind2 () oi2
  oi-trans ↓ (x ←∨) ind2 () oi2
  oi-trans ↓ (∨→ x) ind2 () oi2
  oi-trans ↓ (x ←∂) ind2 () oi2
  oi-trans ↓ (∂→ x) ind2 () oi2
  oi-trans (s ←∧) ↓ ind2 oi1 oi2 = oi2
  oi-trans (s ←∧) (ind1 ←∧) ind2 (onlyInsideC←∧←∧ oi1) oi2 = onlyInsideC←∧←∧ r where
    r = oi-trans s ind1 ind2 oi1 oi2
  oi-trans (s ←∧) (∧→ ind1) ind2 () oi2
  oi-trans (∧→ s) ↓ ind2 oi1 oi2 = oi2
  oi-trans (∧→ s) (ind1 ←∧) ind2 () oi2
  oi-trans (∧→ s) (∧→ ind1) ind2 (onlyInsideC∧→∧→ oi1) oi2 = onlyInsideC∧→∧→ r where
    r = oi-trans s ind1 ind2 oi1 oi2
  oi-trans (s ←∧→ s₁) ↓ ind2 oi1 oi2 = oi2
  oi-trans (s ←∧→ s₁) (ind1 ←∧) ind2 () oi2
  oi-trans (s ←∧→ s₁) (∧→ ind1) ind2 () oi2
  oi-trans (s ←∨) ↓ ind2 oi1 oi2 = oi2
  oi-trans (s ←∨) (ind1 ←∨) ind2 (onlyInsideC←∨←∨ oi1) oi2 = onlyInsideC←∨←∨ r where
    r = oi-trans s ind1 ind2 oi1 oi2
  oi-trans (s ←∨) (∨→ ind1) ind2 () oi2
  oi-trans (∨→ s) ↓ ind2 oi1 oi2 = oi2
  oi-trans (∨→ s) (ind1 ←∨) ind2 () oi2
  oi-trans (∨→ s) (∨→ ind1) ind2 (onlyInsideC∨→∨→ oi1) oi2 = onlyInsideC∨→∨→ r where
    r = oi-trans s ind1 ind2 oi1 oi2
  oi-trans (s ←∨→ s₁) ↓ ind2 oi1 oi2 = oi2
  oi-trans (s ←∨→ s₁) (ind1 ←∨) ind2 () oi2
  oi-trans (s ←∨→ s₁) (∨→ ind1) ind2 () oi2
  oi-trans (s ←∂) ↓ ind2 oi1 oi2 = oi2
  oi-trans (s ←∂) (ind1 ←∂) ind2 (onlyInsideC←∂←∂ oi1) oi2 = onlyInsideC←∂←∂ r where
    r = oi-trans s ind1 ind2 oi1 oi2
  oi-trans (s ←∂) (∂→ ind1) ind2 () oi2
  oi-trans (∂→ s) ↓ ind2 oi1 oi2 = oi2
  oi-trans (∂→ s) (ind1 ←∂) ind2 () oi2
  oi-trans (∂→ s) (∂→ ind1) ind2 (onlyInsideC∂→∂→ oi1) oi2 = onlyInsideC∂→∂→ r where
    r = oi-trans s ind1 ind2 oi1 oi2
  oi-trans (s ←∂→ s₁) ↓ ind2 oi1 oi2 = oi2
  oi-trans (s ←∂→ s₁) (ind1 ←∂) ind2 () oi2
  oi-trans (s ←∂→ s₁) (∂→ ind1) ind2 () oi2



  contr-pres≤ : ∀{i u ll} → (s ss : SetLL {i} {u} ll) → s ≤s ss → contruct s ≤s contruct ss 
  contr-pres≤ ↓ ↓ eq = eq
  contr-pres≤ ↓ (x ←∧) ()
  contr-pres≤ ↓ (∧→ x) ()
  contr-pres≤ ↓ (x ←∧→ x₁) ()
  contr-pres≤ ↓ (x ←∨) ()
  contr-pres≤ ↓ (∨→ x) ()
  contr-pres≤ ↓ (x ←∨→ x₁) ()
  contr-pres≤ ↓ (x ←∂) ()
  contr-pres≤ ↓ (∂→ x) ()
  contr-pres≤ ↓ (x ←∂→ x₁) ()
  contr-pres≤ (s ←∧) ↓ eq = ≤↓
  contr-pres≤ (s ←∧) (ss ←∧) (≤←∧ x) = ≤←∧ (contr-pres≤ s ss x)
  contr-pres≤ (s ←∧) (∧→ ss) ()
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss eq
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | ↓ | e = ≤↓
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∧ | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | ∧→ g | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∧→ g₁ | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∨ | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | ∨→ g | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∨→ g₁ | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∂ | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | ∂→ g | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∂→ g₁ | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∧ | g | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ∧→ r | g | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∧→ r₁ | g | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∨ | g | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ∨→ r | g | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∨→ r₁ | g | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∂ | g | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ∂→ r | g | e = ≤d←∧ e
  contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∂→ r₁ | g | e = ≤d←∧ e
  contr-pres≤ (∧→ s) ↓ eq = ≤↓
  contr-pres≤ (∧→ s) (ss ←∧) ()
  contr-pres≤ (∧→ s) (∧→ ss) (≤∧→ x) = ≤∧→ (contr-pres≤ s ss x)
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss₁ eq
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | ↓ | e = ≤↓
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∧ | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | ∧→ g | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∧→ g₁ | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∨ | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | ∨→ g | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∨→ g₁ | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∂ | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | ∂→ g | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∂→ g₁ | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∧ | g | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ∧→ r | g | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∧→ r₁ | g | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∨ | g | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ∨→ r | g | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∨→ r₁ | g | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∂ | g | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ∂→ r | g | e = ≤d∧→ e
  contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∂→ r₁ | g | e = ≤d∧→ e
  contr-pres≤ (s ←∧→ s₁) ↓ eq = ≤↓
  contr-pres≤ (s ←∧→ s₁) (ss ←∧) ()
  contr-pres≤ (s ←∧→ s₁) (∧→ ss) ()
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) with contruct s | contruct s₁ | contruct ss | contruct ss₁ | contr-pres≤ s ss eq | contr-pres≤ s₁ ss₁ eq₁
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ↓ | .↓ | .↓ | ≤↓ | ≤↓ = ≤↓
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧ | .↓ | ∧→ h | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∧→ g | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∧→ g | .↓ | ∧→ h | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ∧→ h | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨ | .↓ | ∨→ h | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∨→ g | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∨→ g | .↓ | ∨→ h | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ∨→ h | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂ | .↓ | ∂→ h | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∂→ g | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∂→ g | .↓ | ∂→ h | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂ | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ∂→ h | ≤↓ | q = ≤←∧→ ≤↓ q
  contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
  ... | r ←∧ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∧ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
  ... | r ←∧ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
  ... | r ←∧ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∧ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
  ... | r ←∧ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
  ... | r ←∧ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∧ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
  ... | r ←∧ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
  ... | r ←∧ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∧ | g | t ←∧ | h | e | q = ≤←∧→ e q
  ... | r ←∧ | g | ∧→ t | h | e | q = ≤←∧→ e q
  ... | r ←∧ | g | t ←∧→ t₁ | h | e | q = ≤←∧→ e q
  ... | ∧→ r | g | ↓ | ↓ | e | q = ≤↓
  ... | ∧→ r | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
  ... | ∧→ r | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
  ... | ∧→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
  ... | ∧→ r | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
  ... | ∧→ r | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
  ... | ∧→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
  ... | ∧→ r | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
  ... | ∧→ r | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
  ... | ∧→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
  ... | ∧→ r | g | t ←∧ | h | e | q = ≤←∧→ e q
  ... | ∧→ r | g | ∧→ t | h | e | q = ≤←∧→ e q
  ... | ∧→ r | g | t ←∧→ t₁ | h | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∧→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | t ←∧ | h | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | ∧→ t | h | e | q = ≤←∧→ e q
  ... | r ←∧→ r₁ | g | t ←∧→ t₁ | h | e | q = ≤←∧→ e q
  ... | r ←∨ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∨ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
  ... | r ←∨ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
  ... | r ←∨ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∨ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
  ... | r ←∨ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
  ... | r ←∨ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∨ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
  ... | r ←∨ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
  ... | r ←∨ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∨ | g | t ←∨ | h | e | q = ≤←∧→ e q
  ... | r ←∨ | g | ∨→ t | h | e | q = ≤←∧→ e q
  ... | r ←∨ | g | t ←∨→ t₁ | h | e | q = ≤←∧→ e q
  ... | ∨→ r | g | ↓ | ↓ | e | q = ≤↓
  ... | ∨→ r | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
  ... | ∨→ r | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
  ... | ∨→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
  ... | ∨→ r | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
  ... | ∨→ r | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
  ... | ∨→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
  ... | ∨→ r | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
  ... | ∨→ r | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
  ... | ∨→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
  ... | ∨→ r | g | t ←∨ | h | e | q = ≤←∧→ e q
  ... | ∨→ r | g | ∨→ t | h | e | q = ≤←∧→ e q
  ... | ∨→ r | g | t ←∨→ t₁ | h | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∨→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | t ←∨ | h | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | ∨→ t | h | e | q = ≤←∧→ e q
  ... | r ←∨→ r₁ | g | t ←∨→ t₁ | h | e | q = ≤←∧→ e q
  ... | r ←∂ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∂ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
  ... | r ←∂ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
  ... | r ←∂ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∂ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
  ... | r ←∂ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
  ... | r ←∂ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∂ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
  ... | r ←∂ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
  ... | r ←∂ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∂ | g | t ←∂ | h | e | q = ≤←∧→ e q
  ... | r ←∂ | g | ∂→ t | h | e | q = ≤←∧→ e q
  ... | r ←∂ | g | t ←∂→ t₁ | h | e | q = ≤←∧→ e q
  ... | ∂→ r | g | ↓ | ↓ | e | q = ≤↓
  ... | ∂→ r | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
  ... | ∂→ r | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
  ... | ∂→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
  ... | ∂→ r | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
  ... | ∂→ r | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
  ... | ∂→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
  ... | ∂→ r | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
  ... | ∂→ r | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
  ... | ∂→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
  ... | ∂→ r | g | t ←∂ | h | e | q = ≤←∧→ e q
  ... | ∂→ r | g | ∂→ t | h | e | q = ≤←∧→ e q
  ... | ∂→ r | g | t ←∂→ t₁ | h | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∂→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | t ←∂ | h | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | ∂→ t | h | e | q = ≤←∧→ e q
  ... | r ←∂→ r₁ | g | t ←∂→ t₁ | h | e | q = ≤←∧→ e q
  contr-pres≤ (s ←∨) ↓ eq = ≤↓
  contr-pres≤ (s ←∨) (ss ←∨) (≤←∨ x) = ≤←∨ (contr-pres≤ s ss x)
  contr-pres≤ (s ←∨) (∨→ ss) ()
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss eq
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | ↓ | e = ≤↓
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∧ | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | ∧→ g | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∧→ g₁ | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∨ | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | ∨→ g | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∨→ g₁ | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∂ | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | ∂→ g | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∂→ g₁ | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∧ | g | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ∧→ r | g | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∧→ r₁ | g | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∨ | g | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ∨→ r | g | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∨→ r₁ | g | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∂ | g | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ∂→ r | g | e = ≤d←∨ e
  contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∂→ r₁ | g | e = ≤d←∨ e
  contr-pres≤ (∨→ s) ↓ eq = ≤↓
  contr-pres≤ (∨→ s) (ss ←∨) ()
  contr-pres≤ (∨→ s) (∨→ ss) (≤∨→ x) = ≤∨→ (contr-pres≤ s ss x)
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss₁ eq
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | ↓ | e = ≤↓
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∧ | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | ∧→ g | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∧→ g₁ | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∨ | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | ∨→ g | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∨→ g₁ | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∂ | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | ∂→ g | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∂→ g₁ | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∧ | g | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ∧→ r | g | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∧→ r₁ | g | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∨ | g | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ∨→ r | g | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∨→ r₁ | g | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∂ | g | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ∂→ r | g | e = ≤d∨→ e
  contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∂→ r₁ | g | e = ≤d∨→ e
  contr-pres≤ (s ←∨→ s₁) ↓ eq = ≤↓
  contr-pres≤ (s ←∨→ s₁) (ss ←∨) ()
  contr-pres≤ (s ←∨→ s₁) (∨→ ss) ()
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) with contruct s | contruct s₁ | contruct ss | contruct ss₁ | contr-pres≤ s ss eq | contr-pres≤ s₁ ss₁ eq₁
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ↓ | .↓ | .↓ | ≤↓ | ≤↓ = ≤↓
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧ | .↓ | ∧→ h | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∧→ g | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∧→ g | .↓ | ∧→ h | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ∧→ h | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨ | .↓ | ∨→ h | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∨→ g | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∨→ g | .↓ | ∨→ h | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ∨→ h | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂ | .↓ | ∂→ h | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∂→ g | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∂→ g | .↓ | ∂→ h | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂ | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ∂→ h | ≤↓ | q = ≤←∨→ ≤↓ q
  contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
  ... | r ←∧ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∧ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
  ... | r ←∧ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
  ... | r ←∧ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∧ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
  ... | r ←∧ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
  ... | r ←∧ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∧ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
  ... | r ←∧ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
  ... | r ←∧ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∧ | g | t ←∧ | h | e | q = ≤←∨→ e q
  ... | r ←∧ | g | ∧→ t | h | e | q = ≤←∨→ e q
  ... | r ←∧ | g | t ←∧→ t₁ | h | e | q = ≤←∨→ e q
  ... | ∧→ r | g | ↓ | ↓ | e | q = ≤↓
  ... | ∧→ r | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
  ... | ∧→ r | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
  ... | ∧→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
  ... | ∧→ r | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
  ... | ∧→ r | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
  ... | ∧→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
  ... | ∧→ r | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
  ... | ∧→ r | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
  ... | ∧→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
  ... | ∧→ r | g | t ←∧ | h | e | q = ≤←∨→ e q
  ... | ∧→ r | g | ∧→ t | h | e | q = ≤←∨→ e q
  ... | ∧→ r | g | t ←∧→ t₁ | h | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∧→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | t ←∧ | h | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | ∧→ t | h | e | q = ≤←∨→ e q
  ... | r ←∧→ r₁ | g | t ←∧→ t₁ | h | e | q = ≤←∨→ e q
  ... | r ←∨ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∨ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
  ... | r ←∨ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
  ... | r ←∨ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∨ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
  ... | r ←∨ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
  ... | r ←∨ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∨ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
  ... | r ←∨ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
  ... | r ←∨ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∨ | g | t ←∨ | h | e | q = ≤←∨→ e q
  ... | r ←∨ | g | ∨→ t | h | e | q = ≤←∨→ e q
  ... | r ←∨ | g | t ←∨→ t₁ | h | e | q = ≤←∨→ e q
  ... | ∨→ r | g | ↓ | ↓ | e | q = ≤↓
  ... | ∨→ r | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
  ... | ∨→ r | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
  ... | ∨→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
  ... | ∨→ r | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
  ... | ∨→ r | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
  ... | ∨→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
  ... | ∨→ r | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
  ... | ∨→ r | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
  ... | ∨→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
  ... | ∨→ r | g | t ←∨ | h | e | q = ≤←∨→ e q
  ... | ∨→ r | g | ∨→ t | h | e | q = ≤←∨→ e q
  ... | ∨→ r | g | t ←∨→ t₁ | h | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∨→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | t ←∨ | h | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | ∨→ t | h | e | q = ≤←∨→ e q
  ... | r ←∨→ r₁ | g | t ←∨→ t₁ | h | e | q = ≤←∨→ e q
  ... | r ←∂ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∂ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
  ... | r ←∂ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
  ... | r ←∂ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∂ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
  ... | r ←∂ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
  ... | r ←∂ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∂ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
  ... | r ←∂ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
  ... | r ←∂ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∂ | g | t ←∂ | h | e | q = ≤←∨→ e q
  ... | r ←∂ | g | ∂→ t | h | e | q = ≤←∨→ e q
  ... | r ←∂ | g | t ←∂→ t₁ | h | e | q = ≤←∨→ e q
  ... | ∂→ r | g | ↓ | ↓ | e | q = ≤↓
  ... | ∂→ r | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
  ... | ∂→ r | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
  ... | ∂→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
  ... | ∂→ r | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
  ... | ∂→ r | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
  ... | ∂→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
  ... | ∂→ r | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
  ... | ∂→ r | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
  ... | ∂→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
  ... | ∂→ r | g | t ←∂ | h | e | q = ≤←∨→ e q
  ... | ∂→ r | g | ∂→ t | h | e | q = ≤←∨→ e q
  ... | ∂→ r | g | t ←∂→ t₁ | h | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∂→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | t ←∂ | h | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | ∂→ t | h | e | q = ≤←∨→ e q
  ... | r ←∂→ r₁ | g | t ←∂→ t₁ | h | e | q = ≤←∨→ e q
  contr-pres≤ (s ←∂) ↓ eq = ≤↓
  contr-pres≤ (s ←∂) (ss ←∂) (≤←∂ x) = ≤←∂ (contr-pres≤ s ss x)
  contr-pres≤ (s ←∂) (∂→ ss) ()
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss eq
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | ↓ | e = ≤↓
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∧ | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | ∧→ g | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∧→ g₁ | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∨ | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | ∨→ g | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∨→ g₁ | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∂ | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | ∂→ g | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∂→ g₁ | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∧ | g | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ∧→ r | g | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∧→ r₁ | g | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∨ | g | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ∨→ r | g | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∨→ r₁ | g | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∂ | g | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ∂→ r | g | e = ≤d←∂ e
  contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∂→ r₁ | g | e = ≤d←∂ e
  contr-pres≤ (∂→ s) ↓ eq = ≤↓
  contr-pres≤ (∂→ s) (ss ←∂) ()
  contr-pres≤ (∂→ s) (∂→ ss) (≤∂→ x) = ≤∂→ (contr-pres≤ s ss x)
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss₁ eq
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | ↓ | e = ≤↓
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∧ | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | ∧→ g | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∧→ g₁ | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∨ | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | ∨→ g | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∨→ g₁ | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∂ | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | ∂→ g | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∂→ g₁ | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∧ | g | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ∧→ r | g | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∧→ r₁ | g | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∨ | g | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ∨→ r | g | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∨→ r₁ | g | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∂ | g | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ∂→ r | g | e = ≤d∂→ e
  contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∂→ r₁ | g | e = ≤d∂→ e
  contr-pres≤ (s ←∂→ s₁) ↓ eq = ≤↓
  contr-pres≤ (s ←∂→ s₁) (ss ←∂) ()
  contr-pres≤ (s ←∂→ s₁) (∂→ ss) ()
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) with contruct s | contruct s₁ | contruct ss | contruct ss₁ | contr-pres≤ s ss eq | contr-pres≤ s₁ ss₁ eq₁
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ↓ | .↓ | .↓ | ≤↓ | ≤↓ = ≤↓
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧ | .↓ | ∧→ h | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∧→ g | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∧→ g | .↓ | ∧→ h | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ∧→ h | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨ | .↓ | ∨→ h | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∨→ g | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∨→ g | .↓ | ∨→ h | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ∨→ h | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂ | .↓ | ∂→ h | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∂→ g | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∂→ g | .↓ | ∂→ h | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂ | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ∂→ h | ≤↓ | q = ≤←∂→ ≤↓ q
  contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
  ... | r ←∧ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∧ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
  ... | r ←∧ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
  ... | r ←∧ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∧ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
  ... | r ←∧ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
  ... | r ←∧ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∧ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
  ... | r ←∧ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
  ... | r ←∧ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∧ | g | t ←∧ | h | e | q = ≤←∂→ e q
  ... | r ←∧ | g | ∧→ t | h | e | q = ≤←∂→ e q
  ... | r ←∧ | g | t ←∧→ t₁ | h | e | q = ≤←∂→ e q
  ... | ∧→ r | g | ↓ | ↓ | e | q = ≤↓
  ... | ∧→ r | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
  ... | ∧→ r | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
  ... | ∧→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
  ... | ∧→ r | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
  ... | ∧→ r | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
  ... | ∧→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
  ... | ∧→ r | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
  ... | ∧→ r | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
  ... | ∧→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
  ... | ∧→ r | g | t ←∧ | h | e | q = ≤←∂→ e q
  ... | ∧→ r | g | ∧→ t | h | e | q = ≤←∂→ e q
  ... | ∧→ r | g | t ←∧→ t₁ | h | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∧→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | t ←∧ | h | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | ∧→ t | h | e | q = ≤←∂→ e q
  ... | r ←∧→ r₁ | g | t ←∧→ t₁ | h | e | q = ≤←∂→ e q
  ... | r ←∨ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∨ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
  ... | r ←∨ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
  ... | r ←∨ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∨ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
  ... | r ←∨ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
  ... | r ←∨ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∨ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
  ... | r ←∨ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
  ... | r ←∨ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∨ | g | t ←∨ | h | e | q = ≤←∂→ e q
  ... | r ←∨ | g | ∨→ t | h | e | q = ≤←∂→ e q
  ... | r ←∨ | g | t ←∨→ t₁ | h | e | q = ≤←∂→ e q
  ... | ∨→ r | g | ↓ | ↓ | e | q = ≤↓
  ... | ∨→ r | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
  ... | ∨→ r | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
  ... | ∨→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
  ... | ∨→ r | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
  ... | ∨→ r | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
  ... | ∨→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
  ... | ∨→ r | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
  ... | ∨→ r | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
  ... | ∨→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
  ... | ∨→ r | g | t ←∨ | h | e | q = ≤←∂→ e q
  ... | ∨→ r | g | ∨→ t | h | e | q = ≤←∂→ e q
  ... | ∨→ r | g | t ←∨→ t₁ | h | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∨→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | t ←∨ | h | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | ∨→ t | h | e | q = ≤←∂→ e q
  ... | r ←∨→ r₁ | g | t ←∨→ t₁ | h | e | q = ≤←∂→ e q
  ... | r ←∂ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∂ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
  ... | r ←∂ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
  ... | r ←∂ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∂ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
  ... | r ←∂ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
  ... | r ←∂ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∂ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
  ... | r ←∂ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
  ... | r ←∂ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∂ | g | t ←∂ | h | e | q = ≤←∂→ e q
  ... | r ←∂ | g | ∂→ t | h | e | q = ≤←∂→ e q
  ... | r ←∂ | g | t ←∂→ t₁ | h | e | q = ≤←∂→ e q
  ... | ∂→ r | g | ↓ | ↓ | e | q = ≤↓
  ... | ∂→ r | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
  ... | ∂→ r | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
  ... | ∂→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
  ... | ∂→ r | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
  ... | ∂→ r | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
  ... | ∂→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
  ... | ∂→ r | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
  ... | ∂→ r | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
  ... | ∂→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
  ... | ∂→ r | g | t ←∂ | h | e | q = ≤←∂→ e q
  ... | ∂→ r | g | ∂→ t | h | e | q = ≤←∂→ e q
  ... | ∂→ r | g | t ←∂→ t₁ | h | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | ↓ | ↓ | e | q = ≤↓
  ... | r ←∂→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | t ←∂ | h | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | ∂→ t | h | e | q = ≤←∂→ e q
  ... | r ←∂→ r₁ | g | t ←∂→ t₁ | h | e | q = ≤←∂→ e q



  ¬contr≡↓⇒¬contrdel≡↓ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → (ind : IndexLL rll ll) → ∀{x} → del s ind fll ≡ ¬∅ x → ¬ (contruct x ≡ ↓)
  ¬contr≡↓⇒¬contrdel≡↓ s eq ↓ ()
  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∧) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) deq with del s ind fll 
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) refl | ¬∅ di = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ (∧→ s) eq (ind ←∧) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) deq with del s ind fll | inspect (λ x → del s x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ∅ | [ eq1 ] = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∧ rs} {fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
    hf : ¬ (contruct s₁ ≡ ↓)
    hf x with contruct s₁
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∧→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
    hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
    hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
    hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
    hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
    hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∧→ s₁)) ≡ ↓)
    hf t eq x with contruct t | isEq (contruct t) ↓
    hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | g ←∧ | no ¬p
    hf t eq₁ () | ∧→ g | no ¬p
    hf t eq₁ () | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | g ←∨ | no ¬p 
    hf t eq₁ () | ∨→ g | no ¬p 
    hf t eq₁ () | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | g ←∂ | no ¬p 
    hf t eq₁ () | ∂→ g | no ¬p 
    hf t eq₁ () | g ←∂→ g₁ | no ¬p 
  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∧→ ind) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ (s ←∧) eq (∧→ ind) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) deq with del s ind fll
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) refl | ¬∅ x = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ∅ | r = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
    hf : ¬ (contruct s ≡ ↓)
    hf x with contruct s
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∧→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | isEq (contruct e) ↓
    hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
    hf2 t e eq₂ () | ce ←∧ | no ¬p
    hf2 t e eq₂ () | ∧→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∨ | no ¬p 
    hf2 t e eq₂ () | ∨→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∂ | no ¬p 
    hf2 t e eq₂ () | ∂→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∧→ t)) ≡ ↓)
    hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
    hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | ↓ | g ←∧ | no ¬p
    hf t eq₁ () | ↓ | ∧→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∨ | no ¬p 
    hf t eq₁ () | ↓ | ∨→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∂ | no ¬p 
    hf t eq₁ () | ↓ | ∂→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf t eq₁ () | r ←∧ | g | no ¬p 
    hf t eq₁ () | ∧→ r | g | no ¬p 
    hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∨ | g | no ¬p 
    hf t eq₁ () | ∨→ r | g | no ¬p 
    hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∂ | g | no ¬p 
    hf t eq₁ () | ∂→ r | g | no ¬p 
    hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∨) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) deq with del s ind fll 
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) refl | ¬∅ di = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ (∨→ s) eq (ind ←∨) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) deq with del s ind fll | inspect (λ x → del s x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ∅ | [ eq1 ] = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∨ rs} {fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
    hf : ¬ (contruct s₁ ≡ ↓)
    hf x with contruct s₁
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∨→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
    hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
    hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
    hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
    hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
    hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∨→ s₁)) ≡ ↓)
    hf t eq x with contruct t | isEq (contruct t) ↓
    hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | g ←∧ | no ¬p
    hf t eq₁ () | ∧→ g | no ¬p
    hf t eq₁ () | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | g ←∨ | no ¬p 
    hf t eq₁ () | ∨→ g | no ¬p 
    hf t eq₁ () | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | g ←∂ | no ¬p 
    hf t eq₁ () | ∂→ g | no ¬p 
    hf t eq₁ () | g ←∂→ g₁ | no ¬p 
  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∨→ ind) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ (s ←∨) eq (∨→ ind) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) deq with del s ind fll
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) refl | ¬∅ x = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ∅ | r = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
    hf : ¬ (contruct s ≡ ↓)
    hf x with contruct s
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∨→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | isEq (contruct e) ↓
    hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
    hf2 t e eq₂ () | ce ←∧ | no ¬p
    hf2 t e eq₂ () | ∧→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∨ | no ¬p 
    hf2 t e eq₂ () | ∨→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∂ | no ¬p 
    hf2 t e eq₂ () | ∂→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∨→ t)) ≡ ↓)
    hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
    hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | ↓ | g ←∧ | no ¬p
    hf t eq₁ () | ↓ | ∧→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∨ | no ¬p 
    hf t eq₁ () | ↓ | ∨→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∂ | no ¬p 
    hf t eq₁ () | ↓ | ∂→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf t eq₁ () | r ←∧ | g | no ¬p 
    hf t eq₁ () | ∧→ r | g | no ¬p 
    hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∨ | g | no ¬p 
    hf t eq₁ () | ∨→ r | g | no ¬p 
    hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∂ | g | no ¬p 
    hf t eq₁ () | ∂→ r | g | no ¬p 
    hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∂) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) deq with del s ind fll 
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) refl | ¬∅ di = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ (∂→ s) eq (ind ←∂) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) deq with del s ind fll | inspect (λ x → del s x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ∅ | [ eq1 ] = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∂ rs} {fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
    hf : ¬ (contruct s₁ ≡ ↓)
    hf x with contruct s₁
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∂→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
    hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
    hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
    hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
    hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
    hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∂→ s₁)) ≡ ↓)
    hf t eq x with contruct t | isEq (contruct t) ↓
    hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | g ←∧ | no ¬p
    hf t eq₁ () | ∧→ g | no ¬p
    hf t eq₁ () | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | g ←∨ | no ¬p 
    hf t eq₁ () | ∨→ g | no ¬p 
    hf t eq₁ () | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | g ←∂ | no ¬p 
    hf t eq₁ () | ∂→ g | no ¬p 
    hf t eq₁ () | g ←∂→ g₁ | no ¬p 
  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∂→ ind) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ (s ←∂) eq (∂→ ind) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) deq with del s ind fll
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) refl | ¬∅ x = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ∅ | r = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
    hf : ¬ (contruct s ≡ ↓)
    hf x with contruct s
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∂→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | isEq (contruct e) ↓
    hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
    hf2 t e eq₂ () | ce ←∧ | no ¬p
    hf2 t e eq₂ () | ∧→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∨ | no ¬p 
    hf2 t e eq₂ () | ∨→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∂ | no ¬p 
    hf2 t e eq₂ () | ∂→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∂→ t)) ≡ ↓)
    hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
    hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | ↓ | g ←∧ | no ¬p
    hf t eq₁ () | ↓ | ∧→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∨ | no ¬p 
    hf t eq₁ () | ↓ | ∨→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∂ | no ¬p 
    hf t eq₁ () | ↓ | ∂→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf t eq₁ () | r ←∧ | g | no ¬p 
    hf t eq₁ () | ∧→ r | g | no ¬p 
    hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∨ | g | no ¬p 
    hf t eq₁ () | ∨→ r | g | no ¬p 
    hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∂ | g | no ¬p 
    hf t eq₁ () | ∂→ r | g | no ¬p 
    hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 


module _ where

  open Data.Product
  
  ¬contr≡↓&trunc≡∅⇒¬contrdel≡↓ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → (ind : IndexLL rll ll) → (truncSetLL s ind ≡ ∅)
                                 → Σ (SetLL (replLL ll ind fll)) (λ x → (del s ind fll ≡ ¬∅ x) × (¬ (contruct x ≡ ↓)))
  ¬contr≡↓&trunc≡∅⇒¬contrdel≡↓ {fll = fll} s ceq ind treq with del s ind fll | inspect (λ x → del s x fll) ind
  ... | ∅ | [ eq ] = ⊥-elim (d eq) where
    d = trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind treq
  ... | ¬∅ x | [ eq ] = (x , refl , c) where
    c = ¬contr≡↓⇒¬contrdel≡↓ s ceq ind eq



