module CTT where

open import PathPrelude
open import Data.Empty
open import Relation.Nullary



¬fun-eq : ∀{ℓ} → {A : Set ℓ} → (f g : ¬ A) → f ≡ g
¬fun-eq f g = funExt (¬fun-eq' f g) where
  ¬fun-eq' : ∀{ℓ} → {A : Set ℓ} → (f g : ¬ A) → (x : A) → f x ≡ g x
  ¬fun-eq' f g x = ⊥-elim (f x)
