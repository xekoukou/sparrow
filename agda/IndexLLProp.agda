{-# OPTIONS --exact-split #-}
-- {-# OPTIONS --show-implicit #-}

module IndexLLProp where

open import Common
open import LinLogic
open import Data.Maybe
open import Data.Product
import Relation.Binary.HeterogeneousEquality
open import Relation.Binary.PropositionalEquality using (subst ; cong ; subst₂)
open import CTT

data _≅ᵢ_ {i u gll} : ∀{fll ll} → IndexLL {i} {u} gll ll → IndexLL {i} {u} fll ll → Set where
  ≅ᵢ↓ :  ↓ ≅ᵢ ↓
  ≅ᵢ←∧ : ∀{fll li ri} → {sind : IndexLL gll li} → {bind : IndexLL fll li} → (sind ≅ᵢ bind)
         → _≅ᵢ_ {ll = li ∧ ri} (sind ←∧) (bind ←∧)
  ≅ᵢ∧→ : ∀{fll li ri} → {sind : IndexLL gll ri} → {bind : IndexLL fll ri} → (sind ≅ᵢ bind)
         → _≅ᵢ_ {ll = li ∧ ri} (∧→ sind) (∧→ bind)
  ≅ᵢ←∨ : ∀{fll li ri} → {sind : IndexLL gll li} → {bind : IndexLL fll li} → (sind ≅ᵢ bind)
         → _≅ᵢ_ {ll = li ∨ ri} (sind ←∨) (bind ←∨)
  ≅ᵢ∨→ : ∀{fll li ri} → {sind : IndexLL gll ri} → {bind : IndexLL fll ri} → (sind ≅ᵢ bind)
         → _≅ᵢ_ {ll = li ∨ ri} (∨→ sind) (∨→ bind)
  ≅ᵢ←∂ : ∀{fll li ri} → {sind : IndexLL gll li} → {bind : IndexLL fll li} → (sind ≅ᵢ bind)
         → _≅ᵢ_ {ll = li ∂ ri} (sind ←∂) (bind ←∂)
  ≅ᵢ∂→ : ∀{fll li ri} → {sind : IndexLL gll ri} → {bind : IndexLL fll ri} → (sind ≅ᵢ bind)
         → _≅ᵢ_ {ll = li ∂ ri} (∂→ sind) (∂→ bind)


≅ᵢ-reflexive : ∀{i u rll ll} → (a : IndexLL {i} {u} rll ll) → a ≅ᵢ a
≅ᵢ-reflexive ↓ = ≅ᵢ↓
≅ᵢ-reflexive (x ←∧) = ≅ᵢ←∧ (≅ᵢ-reflexive x)
≅ᵢ-reflexive (∧→ x) = ≅ᵢ∧→ (≅ᵢ-reflexive x)
≅ᵢ-reflexive (x ←∨) = ≅ᵢ←∨ (≅ᵢ-reflexive x)
≅ᵢ-reflexive (∨→ x) = ≅ᵢ∨→ (≅ᵢ-reflexive x)
≅ᵢ-reflexive (x ←∂) = ≅ᵢ←∂ (≅ᵢ-reflexive x)
≅ᵢ-reflexive (∂→ x) = ≅ᵢ∂→ (≅ᵢ-reflexive x)

≡-to-≅ᵢ : ∀{i u rll ll} → (a b : IndexLL {i} {u} rll ll) → a ≡ b → a ≅ᵢ b
≡-to-≅ᵢ a .a refl = ≅ᵢ-reflexive a



data _≤ᵢ_ {i u gll fll} : ∀{ll} → IndexLL {i} {u} gll ll → IndexLL {i} {u} fll ll → Set where
  ≤ᵢ↓ : {ind : IndexLL fll gll} → ↓ ≤ᵢ ind
  ≤ᵢ←∧ : ∀{li ri} → {sind : IndexLL gll li} → {bind : IndexLL fll li} → (sind ≤ᵢ bind)
         → _≤ᵢ_ {ll = li ∧ ri} (sind ←∧) (bind ←∧)
  ≤ᵢ∧→ : ∀{li ri} → {sind : IndexLL gll ri} → {bind : IndexLL fll ri} → (sind ≤ᵢ bind)
         → _≤ᵢ_ {ll = li ∧ ri} (∧→ sind) (∧→ bind)
  ≤ᵢ←∨ : ∀{li ri} → {sind : IndexLL gll li} → {bind : IndexLL fll li} → (sind ≤ᵢ bind)
         → _≤ᵢ_ {ll = li ∨ ri} (sind ←∨) (bind ←∨)
  ≤ᵢ∨→ : ∀{li ri} → {sind : IndexLL gll ri} → {bind : IndexLL fll ri} → (sind ≤ᵢ bind)
         → _≤ᵢ_ {ll = li ∨ ri} (∨→ sind) (∨→ bind)
  ≤ᵢ←∂ : ∀{li ri} → {sind : IndexLL gll li} → {bind : IndexLL fll li} → (sind ≤ᵢ bind)
         → _≤ᵢ_ {ll = li ∂ ri} (sind ←∂) (bind ←∂)
  ≤ᵢ∂→ : ∀{li ri} → {sind : IndexLL gll ri} → {bind : IndexLL fll ri} → (sind ≤ᵢ bind)
         → _≤ᵢ_ {ll = li ∂ ri} (∂→ sind) (∂→ bind)

≤ᵢ-reflexive : ∀{i u gll ll} → (ind : IndexLL {i} {u} gll ll) → ind ≤ᵢ ind
≤ᵢ-reflexive ↓ = ≤ᵢ↓
≤ᵢ-reflexive (ind ←∧) = ≤ᵢ←∧ (≤ᵢ-reflexive ind)
≤ᵢ-reflexive (∧→ ind) = ≤ᵢ∧→ (≤ᵢ-reflexive ind)
≤ᵢ-reflexive (ind ←∨) = ≤ᵢ←∨ (≤ᵢ-reflexive ind)
≤ᵢ-reflexive (∨→ ind) = ≤ᵢ∨→ (≤ᵢ-reflexive ind)
≤ᵢ-reflexive (ind ←∂) = ≤ᵢ←∂ (≤ᵢ-reflexive ind)
≤ᵢ-reflexive (∂→ ind) = ≤ᵢ∂→ (≤ᵢ-reflexive ind)

≤ᵢ-transitive : ∀{i u gll fll mll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL fll ll} → {c : IndexLL mll ll} → (a ≤ᵢ b) → (b ≤ᵢ c) → (a ≤ᵢ c)
≤ᵢ-transitive ≤ᵢ↓ ltbc = ≤ᵢ↓
≤ᵢ-transitive (≤ᵢ←∧ ltab) (≤ᵢ←∧ ltbc) = ≤ᵢ←∧ (≤ᵢ-transitive ltab ltbc)
≤ᵢ-transitive (≤ᵢ∧→ ltab) (≤ᵢ∧→ ltbc) = ≤ᵢ∧→ (≤ᵢ-transitive ltab ltbc)
≤ᵢ-transitive (≤ᵢ←∨ ltab) (≤ᵢ←∨ ltbc) = ≤ᵢ←∨ (≤ᵢ-transitive ltab ltbc)
≤ᵢ-transitive (≤ᵢ∨→ ltab) (≤ᵢ∨→ ltbc) = ≤ᵢ∨→ (≤ᵢ-transitive ltab ltbc)
≤ᵢ-transitive (≤ᵢ←∂ ltab) (≤ᵢ←∂ ltbc) = ≤ᵢ←∂ (≤ᵢ-transitive ltab ltbc)
≤ᵢ-transitive (≤ᵢ∂→ ltab) (≤ᵢ∂→ ltbc) = ≤ᵢ∂→ (≤ᵢ-transitive ltab ltbc)


isLTi : ∀{i u gll ll fll} → (s : IndexLL {i} {u} gll ll) → (b : IndexLL fll ll) → Dec (s ≤ᵢ b)
isLTi ↓ b = yes ≤ᵢ↓
isLTi (s ←∧) ↓ = no (λ ())
isLTi (s ←∧) (b ←∧) with (isLTi s b)
isLTi (s ←∧) (b ←∧) | yes p = yes $ ≤ᵢ←∧ p
isLTi (s ←∧) (b ←∧) | no ¬p = no (λ {(≤ᵢ←∧ p) → ¬p p }) 
isLTi (s ←∧) (∧→ b) = no (λ ())
isLTi (∧→ s) ↓ = no (λ ())
isLTi (∧→ s) (b ←∧) = no (λ ())
isLTi (∧→ s) (∧→ b) with (isLTi s b)
isLTi (∧→ s) (∧→ b) | yes p = yes (≤ᵢ∧→ p)
isLTi (∧→ s) (∧→ b) | no ¬p = no (λ {(≤ᵢ∧→ p) → ¬p p })
isLTi (s ←∨) ↓ = no (λ ())
isLTi (s ←∨) (b ←∨) with (isLTi s b)
isLTi (s ←∨) (b ←∨) | yes p = yes $ ≤ᵢ←∨ p
isLTi (s ←∨) (b ←∨) | no ¬p = no (λ {(≤ᵢ←∨ p) → ¬p p }) 
isLTi (s ←∨) (∨→ b) = no (λ ())
isLTi (∨→ s) ↓ = no (λ ())
isLTi (∨→ s) (b ←∨) = no (λ ())
isLTi (∨→ s) (∨→ b) with (isLTi s b)
isLTi (∨→ s) (∨→ b) | yes p = yes (≤ᵢ∨→ p)
isLTi (∨→ s) (∨→ b) | no ¬p = no (λ {(≤ᵢ∨→ p) → ¬p p })
isLTi (s ←∂) ↓ = no (λ ())
isLTi (s ←∂) (b ←∂) with (isLTi s b)
isLTi (s ←∂) (b ←∂) | yes p = yes $ ≤ᵢ←∂ p
isLTi (s ←∂) (b ←∂) | no ¬p = no (λ {(≤ᵢ←∂ p) → ¬p p }) 
isLTi (s ←∂) (∂→ b) = no (λ ())
isLTi (∂→ s) ↓ = no (λ ())
isLTi (∂→ s) (b ←∂) = no (λ ())
isLTi (∂→ s) (∂→ b) with (isLTi s b)
isLTi (∂→ s) (∂→ b) | yes p = yes (≤ᵢ∂→ p)
isLTi (∂→ s) (∂→ b) | no ¬p = no (λ {(≤ᵢ∂→ p) → ¬p p })

isEqᵢ : ∀{u i ll rll} → (a : IndexLL {i} {u} rll ll) → (b : IndexLL rll ll) → Dec (a ≡ b)
isEqᵢ ↓ ↓ = yes refl
isEqᵢ ↓ (b ←∧) = no (λ ())
isEqᵢ ↓ (∧→ b) = no (λ ())
isEqᵢ ↓ (b ←∨) = no (λ ())
isEqᵢ ↓ (∨→ b) = no (λ ())
isEqᵢ ↓ (b ←∂) = no (λ ())
isEqᵢ ↓ (∂→ b) = no (λ ())
isEqᵢ (a ←∧) ↓ = no (λ ())
isEqᵢ (a ←∧) (b ←∧) with isEqᵢ a b
isEqᵢ (a ←∧) (.a ←∧) | yes refl = yes refl
isEqᵢ (a ←∧) (b ←∧) | no ¬p = no hf where
  hf : ¬ ((a ←∧) ≡ (b ←∧))
  hf refl = ¬p refl
isEqᵢ (a ←∧) (∧→ b) = no (λ ())
isEqᵢ (∧→ a) ↓ = no (λ ())
isEqᵢ (∧→ a) (b ←∧) = no (λ ())
isEqᵢ (∧→ a) (∧→ b)  with isEqᵢ a b
isEqᵢ (∧→ a) (∧→ .a) | yes refl = yes refl
isEqᵢ (∧→ a) (∧→ b) | no ¬p = no hf where
  hf : ¬ ((∧→ a) ≡ (∧→ b))
  hf refl = ¬p refl
isEqᵢ (a ←∨) ↓ = no (λ ())
isEqᵢ (a ←∨) (b ←∨) with isEqᵢ a b
isEqᵢ (a ←∨) (.a ←∨) | yes refl = yes refl
isEqᵢ (a ←∨) (b ←∨) | no ¬p = no hf where
  hf : ¬ ((a ←∨) ≡ (b ←∨))
  hf refl = ¬p refl
isEqᵢ (a ←∨) (∨→ b) = no (λ ())
isEqᵢ (∨→ a) ↓ = no (λ ())
isEqᵢ (∨→ a) (b ←∨) = no (λ ())
isEqᵢ (∨→ a) (∨→ b)  with isEqᵢ a b
isEqᵢ (∨→ a) (∨→ .a) | yes refl = yes refl
isEqᵢ (∨→ a) (∨→ b) | no ¬p = no hf where
  hf : ¬ ((∨→ a) ≡ (∨→ b))
  hf refl = ¬p refl
isEqᵢ (a ←∂) ↓ = no (λ ())
isEqᵢ (a ←∂) (b ←∂) with isEqᵢ a b
isEqᵢ (a ←∂) (.a ←∂) | yes refl = yes refl
isEqᵢ (a ←∂) (b ←∂) | no ¬p = no hf where
  hf : ¬ ((a ←∂) ≡ (b ←∂))
  hf refl = ¬p refl
isEqᵢ (a ←∂) (∂→ b) = no (λ ())
isEqᵢ (∂→ a) ↓ = no (λ ())
isEqᵢ (∂→ a) (b ←∂) = no (λ ())
isEqᵢ (∂→ a) (∂→ b)  with isEqᵢ a b
isEqᵢ (∂→ a) (∂→ .a) | yes refl = yes refl
isEqᵢ (∂→ a) (∂→ b) | no ¬p = no hf where
  hf : ¬ ((∂→ a) ≡ (∂→ b))
  hf refl = ¬p refl





module _ where

  open import Data.Vec

-- Is there a better way to express that?
  indτ⇒¬le : ∀{i u rll ll n dt df} → (ind : IndexLL {i} {u} (τ {i} {u} {n} {dt} df) ll) → (ind2 : IndexLL rll ll) → ¬ (ind2 ≅ᵢ ind) → ¬ (ind ≤ᵢ ind2)
  indτ⇒¬le ↓ ↓ neq = λ _ → neq ≅ᵢ↓
  indτ⇒¬le (x ←∧) ↓ neq = λ ()
  indτ⇒¬le (x ←∧) (y ←∧) neq with indτ⇒¬le x y ineq where
    ineq : ¬ (y ≅ᵢ x)
    ineq z = neq (≅ᵢ←∧ z)
  ... | r = λ { (≤ᵢ←∧ x) → r x}
  indτ⇒¬le (x ←∧) (∧→ y) neq = λ ()
  indτ⇒¬le (∧→ x) ↓ neq = λ ()
  indτ⇒¬le (∧→ x) (y ←∧) neq = λ ()
  indτ⇒¬le (∧→ x) (∧→ y) neq with indτ⇒¬le x y ineq where
    ineq : ¬ (y ≅ᵢ x)
    ineq z = neq (≅ᵢ∧→ z)
  ... | r = λ { (≤ᵢ∧→ x) → r x}
  indτ⇒¬le (x ←∨) ↓ neq = λ ()
  indτ⇒¬le (x ←∨) (y ←∨) neq with indτ⇒¬le x y ineq where
    ineq : ¬ (y ≅ᵢ x)
    ineq z = neq (≅ᵢ←∨ z)
  ... | r = λ { (≤ᵢ←∨ x) → r x}
  indτ⇒¬le (x ←∨) (∨→ y) neq = λ ()
  indτ⇒¬le (∨→ x) ↓ neq = λ ()
  indτ⇒¬le (∨→ x) (y ←∨) neq = λ ()
  indτ⇒¬le (∨→ x) (∨→ y) neq with indτ⇒¬le x y ineq where
    ineq : ¬ (y ≅ᵢ x)
    ineq z = neq (≅ᵢ∨→ z)
  ... | r = λ { (≤ᵢ∨→ x) → r x}
  indτ⇒¬le (x ←∂) ↓ neq = λ ()
  indτ⇒¬le (x ←∂) (y ←∂) neq with indτ⇒¬le x y ineq where
    ineq : ¬ (y ≅ᵢ x)
    ineq z = neq (≅ᵢ←∂ z)
  ... | r = λ { (≤ᵢ←∂ x) → r x}
  indτ⇒¬le (x ←∂) (∂→ y) neq = λ ()
  indτ⇒¬le (∂→ x) ↓ neq = λ ()
  indτ⇒¬le (∂→ x) (y ←∂) neq = λ ()
  indτ⇒¬le (∂→ x) (∂→ y) neq with indτ⇒¬le x y ineq where
    ineq : ¬ (y ≅ᵢ x)
    ineq z = neq (≅ᵢ∂→ z)
  ... | r = λ { (≤ᵢ∂→ x) → r x}
  


indτ&¬ge⇒¬≅ : ∀{i u rll ll n dt df} → (ind : IndexLL (τ {i} {u} {n} {dt} df) ll)
                          (lind : IndexLL rll ll) → ¬ (lind ≤ᵢ ind) → ¬ (lind ≅ᵢ ind)
indτ&¬ge⇒¬≅ ↓ ↓ neq = λ _ → neq ≤ᵢ↓
indτ&¬ge⇒¬≅ (ind ←∧) ↓ neq = λ ()
indτ&¬ge⇒¬≅ (ind ←∧) (lind ←∧) neq = λ {(≅ᵢ←∧ x) → r x} where
  r = indτ&¬ge⇒¬≅ ind lind (λ z → neq (≤ᵢ←∧ z))
indτ&¬ge⇒¬≅ (ind ←∧) (∧→ lind) neq = λ ()
indτ&¬ge⇒¬≅ (∧→ ind) ↓ neq = λ ()
indτ&¬ge⇒¬≅ (∧→ ind) (lind ←∧) neq = λ ()
indτ&¬ge⇒¬≅ (∧→ ind) (∧→ lind) neq  = λ {(≅ᵢ∧→ x) → r x} where
  r = indτ&¬ge⇒¬≅ ind lind (λ z → neq (≤ᵢ∧→ z))
indτ&¬ge⇒¬≅ (ind ←∨) ↓ neq = λ ()
indτ&¬ge⇒¬≅ (ind ←∨) (lind ←∨) neq = λ {(≅ᵢ←∨ x) → r x} where
  r = indτ&¬ge⇒¬≅ ind lind (λ z → neq (≤ᵢ←∨ z))
indτ&¬ge⇒¬≅ (ind ←∨) (∨→ lind) neq = λ ()
indτ&¬ge⇒¬≅ (∨→ ind) ↓ neq = λ ()
indτ&¬ge⇒¬≅ (∨→ ind) (lind ←∨) neq = λ ()
indτ&¬ge⇒¬≅ (∨→ ind) (∨→ lind) neq  = λ {(≅ᵢ∨→ x) → r x} where
  r = indτ&¬ge⇒¬≅ ind lind (λ z → neq (≤ᵢ∨→ z))
indτ&¬ge⇒¬≅ (ind ←∂) ↓ neq = λ ()
indτ&¬ge⇒¬≅ (ind ←∂) (lind ←∂) neq = λ {(≅ᵢ←∂ x) → r x} where
  r = indτ&¬ge⇒¬≅ ind lind (λ z → neq (≤ᵢ←∂ z))
indτ&¬ge⇒¬≅ (ind ←∂) (∂→ lind) neq = λ ()
indτ&¬ge⇒¬≅ (∂→ ind) ↓ neq = λ ()
indτ&¬ge⇒¬≅ (∂→ ind) (lind ←∂) neq = λ ()
indτ&¬ge⇒¬≅ (∂→ ind) (∂→ lind) neq  = λ {(≅ᵢ∂→ x) → r x} where
  r = indτ&¬ge⇒¬≅ ind lind (λ z → neq (≤ᵢ∂→ z))

 

data Orderedᵢ {i u gll fll ll} (a : IndexLL {i} {u} gll ll) (b : IndexLL {i} {u} fll ll) : Set where
  a≤ᵢb : a ≤ᵢ b → Orderedᵢ a b
  b≤ᵢa : b ≤ᵢ a → Orderedᵢ a b

isOrdᵢ : ∀{i u gll fll ll} → (a : IndexLL {i} {u} gll ll) → (b : IndexLL {i} {u} fll ll)
         → Dec (Orderedᵢ a b)
isOrdᵢ a b with (isLTi a b) | (isLTi b a)
isOrdᵢ a b | yes p | r = yes (a≤ᵢb p)
isOrdᵢ a b | no ¬p | (yes p) = yes (b≤ᵢa p)
isOrdᵢ a b | no ¬p | (no ¬p₁) = no ((λ { (a≤ᵢb p) → ¬p p
                                       ; (b≤ᵢa p) → ¬p₁ p }))



flipOrdᵢ : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
           → Orderedᵢ a b → Orderedᵢ b a
flipOrdᵢ (a≤ᵢb x) = b≤ᵢa x
flipOrdᵢ (b≤ᵢa x) = a≤ᵢb x

flipNotOrdᵢ : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
              → ¬ Orderedᵢ a b → ¬ Orderedᵢ b a
flipNotOrdᵢ nord = λ x → nord (flipOrdᵢ x) 


¬lt¬gt⇒¬Ord : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
              → ¬ (a ≤ᵢ b) → ¬ (b ≤ᵢ a) → ¬(Orderedᵢ a b)
¬lt¬gt⇒¬Ord nlt ngt (a≤ᵢb x) = nlt x
¬lt¬gt⇒¬Ord nlt ngt (b≤ᵢa x) = ngt x

¬ord-spec : ∀{i u rll ll fll} → {emi : IndexLL {i} {u} fll ll}
            → {ind : IndexLL rll ll} → {ict : IndexLLCT} → ∀ {tll} → (nord : ¬ Orderedᵢ (expInd ict tll ind) (expInd ict tll emi)) → ¬ Orderedᵢ ind emi
¬ord-spec {ict = ic←∧ } nord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ←∧ x))
¬ord-spec {ict = ic←∧ } nord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ←∧ x))
¬ord-spec {ict = ic∧→ } nord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ∧→ x))
¬ord-spec {ict = ic∧→ } nord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ∧→ x))
¬ord-spec {ict = ic←∨ } nord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ←∨ x))
¬ord-spec {ict = ic←∨ } nord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ←∨ x))
¬ord-spec {ict = ic∨→ } nord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ∨→ x))
¬ord-spec {ict = ic∨→ } nord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ∨→ x))
¬ord-spec {ict = ic←∂ } nord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ←∂ x))
¬ord-spec {ict = ic←∂ } nord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ←∂ x))
¬ord-spec {ict = ic∂→ } nord (a≤ᵢb x) = nord (a≤ᵢb (≤ᵢ∂→ x))
¬ord-spec {ict = ic∂→ } nord (b≤ᵢa x) = nord (b≤ᵢa (≤ᵢ∂→ x))



indτ&¬ge⇒¬Ord : ∀{i u rll ll n dt df} → (ind : IndexLL (τ {i} {u} {n} {dt} df) ll)
                          (lind : IndexLL rll ll) → ¬ (lind ≤ᵢ ind) → ¬ Orderedᵢ ind lind
indτ&¬ge⇒¬Ord ind lind neq (a≤ᵢb x) = indτ⇒¬le ind lind (indτ&¬ge⇒¬≅ ind lind neq) x
indτ&¬ge⇒¬Ord ind lind neq (b≤ᵢa x) = neq x                        


a,c≤ᵢb⇒ordac : ∀{i u gll fll mll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL fll ll} → {c : IndexLL mll ll} → (a ≤ᵢ b) → (c ≤ᵢ b) → Orderedᵢ a c
a,c≤ᵢb⇒ordac ltab ≤ᵢ↓ = b≤ᵢa ≤ᵢ↓
a,c≤ᵢb⇒ordac ≤ᵢ↓ (≤ᵢ←∧ ltac) = a≤ᵢb ≤ᵢ↓
a,c≤ᵢb⇒ordac (≤ᵢ←∧ ltab) (≤ᵢ←∧ ltac) with (a,c≤ᵢb⇒ordac ltab ltac)
a,c≤ᵢb⇒ordac (≤ᵢ←∧ ltab) (≤ᵢ←∧ ltac) | a≤ᵢb x = a≤ᵢb (≤ᵢ←∧ x)
a,c≤ᵢb⇒ordac (≤ᵢ←∧ ltab) (≤ᵢ←∧ ltac) | b≤ᵢa x = b≤ᵢa (≤ᵢ←∧ x)
a,c≤ᵢb⇒ordac ≤ᵢ↓ (≤ᵢ∧→ ltac) = a≤ᵢb ≤ᵢ↓
a,c≤ᵢb⇒ordac (≤ᵢ∧→ ltab) (≤ᵢ∧→ ltac) with (a,c≤ᵢb⇒ordac ltab ltac)
a,c≤ᵢb⇒ordac (≤ᵢ∧→ ltab) (≤ᵢ∧→ ltac) | a≤ᵢb x = a≤ᵢb (≤ᵢ∧→ x)
a,c≤ᵢb⇒ordac (≤ᵢ∧→ ltab) (≤ᵢ∧→ ltac) | b≤ᵢa x = b≤ᵢa (≤ᵢ∧→ x)
a,c≤ᵢb⇒ordac ≤ᵢ↓ (≤ᵢ←∨ ltac) = a≤ᵢb ≤ᵢ↓
a,c≤ᵢb⇒ordac (≤ᵢ←∨ ltab) (≤ᵢ←∨ ltac) with (a,c≤ᵢb⇒ordac ltab ltac)
a,c≤ᵢb⇒ordac (≤ᵢ←∨ ltab) (≤ᵢ←∨ ltac) | a≤ᵢb x = a≤ᵢb (≤ᵢ←∨ x)
a,c≤ᵢb⇒ordac (≤ᵢ←∨ ltab) (≤ᵢ←∨ ltac) | b≤ᵢa x = b≤ᵢa (≤ᵢ←∨ x)
a,c≤ᵢb⇒ordac ≤ᵢ↓ (≤ᵢ∨→ ltac) = a≤ᵢb ≤ᵢ↓
a,c≤ᵢb⇒ordac (≤ᵢ∨→ ltab) (≤ᵢ∨→ ltac) with (a,c≤ᵢb⇒ordac ltab ltac)
a,c≤ᵢb⇒ordac (≤ᵢ∨→ ltab) (≤ᵢ∨→ ltac) | a≤ᵢb x = a≤ᵢb (≤ᵢ∨→ x)
a,c≤ᵢb⇒ordac (≤ᵢ∨→ ltab) (≤ᵢ∨→ ltac) | b≤ᵢa x = b≤ᵢa (≤ᵢ∨→ x)
a,c≤ᵢb⇒ordac ≤ᵢ↓ (≤ᵢ←∂ ltac) = a≤ᵢb ≤ᵢ↓
a,c≤ᵢb⇒ordac (≤ᵢ←∂ ltab) (≤ᵢ←∂ ltac) with (a,c≤ᵢb⇒ordac ltab ltac)
a,c≤ᵢb⇒ordac (≤ᵢ←∂ ltab) (≤ᵢ←∂ ltac) | a≤ᵢb x = a≤ᵢb (≤ᵢ←∂ x)
a,c≤ᵢb⇒ordac (≤ᵢ←∂ ltab) (≤ᵢ←∂ ltac) | b≤ᵢa x = b≤ᵢa (≤ᵢ←∂ x)
a,c≤ᵢb⇒ordac ≤ᵢ↓ (≤ᵢ∂→ ltac) = a≤ᵢb ≤ᵢ↓
a,c≤ᵢb⇒ordac (≤ᵢ∂→ ltab) (≤ᵢ∂→ ltac) with (a,c≤ᵢb⇒ordac ltab ltac)
a,c≤ᵢb⇒ordac (≤ᵢ∂→ ltab) (≤ᵢ∂→ ltac) | a≤ᵢb x = a≤ᵢb (≤ᵢ∂→ x)
a,c≤ᵢb⇒ordac (≤ᵢ∂→ ltab) (≤ᵢ∂→ ltac) | b≤ᵢa x = b≤ᵢa (≤ᵢ∂→ x)



a≤ᵢb&¬ordac⇒¬ordbc : ∀{i u gll fll mll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL fll ll} → {c : IndexLL mll ll} → (a ≤ᵢ b) → ¬ Orderedᵢ a c → ¬ Orderedᵢ b c
a≤ᵢb&¬ordac⇒¬ordbc lt nord (a≤ᵢb x) = ⊥-elim (nord (a≤ᵢb (≤ᵢ-transitive lt x)))
a≤ᵢb&¬ordac⇒¬ordbc lt nord (b≤ᵢa x) = ⊥-elim (nord (a,c≤ᵢb⇒ordac lt x))


_-ᵢ_ : ∀ {i u pll cll ll} → (bind : IndexLL {i} {u} cll ll) → (sind : IndexLL pll ll) → (sind ≤ᵢ bind)
       → IndexLL cll pll
(bind -ᵢ .↓) ≤ᵢ↓ = bind
((bind ←∧) -ᵢ (sind ←∧)) (≤ᵢ←∧ eq) = (bind -ᵢ sind) eq
((∧→ bind) -ᵢ (∧→ sind)) (≤ᵢ∧→ eq) = (bind -ᵢ sind) eq
((bind ←∨) -ᵢ (sind ←∨)) (≤ᵢ←∨ eq) = (bind -ᵢ sind) eq
((∨→ bind) -ᵢ (∨→ sind)) (≤ᵢ∨→ eq) = (bind -ᵢ sind) eq
((bind ←∂) -ᵢ (sind ←∂)) (≤ᵢ←∂ eq) = (bind -ᵢ sind) eq
((∂→ bind) -ᵢ (∂→ sind)) (≤ᵢ∂→ eq) = (bind -ᵢ sind) eq


replLL-↓ : ∀{i u pll ell ll} → ∀(ind : IndexLL {i} {u} pll ll)
           → replLL pll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) ell ≡ ell
replLL-↓ ↓ = refl
replLL-↓ (ind ←∧) = replLL-↓ ind
replLL-↓ (∧→ ind) = replLL-↓ ind
replLL-↓ (ind ←∨) = replLL-↓ ind
replLL-↓ (∨→ ind) = replLL-↓ ind
replLL-↓ (ind ←∂) = replLL-↓ ind
replLL-↓ (∂→ ind) = replLL-↓ ind


ind-rpl↓ : ∀{i u ll pll cll ell} → (ind : IndexLL {i} {u} pll ll)
        → IndexLL cll (replLL pll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) ell) → IndexLL cll ell
ind-rpl↓ {_} {_} {_} {pll} {cll} {ell} ind x
  =  subst (λ x → x) (cong (λ x → IndexLL cll x) (replLL-↓ {ell = ell} ind)) x 



a≤ᵢb-morph : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll)
             → (ind : IndexLL rll ll) → ∀ frll → (lt : emi ≤ᵢ ind)
             → IndexLL (replLL fll ((ind -ᵢ emi) lt) frll) (replLL ll ind frll) 
a≤ᵢb-morph ↓ ind frll ≤ᵢ↓ = ↓
a≤ᵢb-morph (emi ←∧) (ind ←∧) frll (≤ᵢ←∧ lt) = a≤ᵢb-morph emi ind frll lt ←∧
a≤ᵢb-morph (∧→ emi) (∧→ ind) frll (≤ᵢ∧→ lt) = ∧→ a≤ᵢb-morph emi ind frll lt
a≤ᵢb-morph (emi ←∨) (ind ←∨) frll (≤ᵢ←∨ lt) = a≤ᵢb-morph emi ind frll lt ←∨
a≤ᵢb-morph (∨→ emi) (∨→ ind) frll (≤ᵢ∨→ lt) = ∨→ a≤ᵢb-morph emi ind frll lt
a≤ᵢb-morph (emi ←∂) (ind ←∂) frll (≤ᵢ←∂ lt) = a≤ᵢb-morph emi ind frll lt ←∂
a≤ᵢb-morph (∂→ emi) (∂→ ind) frll (≤ᵢ∂→ lt) = ∂→ a≤ᵢb-morph emi ind frll lt



a≤ᵢb-morph-id : ∀{i u ll rll}
             → (ind : IndexLL {i} {u} rll ll)
             → subst₂ (λ x y → IndexLL x y) (replLL-↓ {ell = rll} ind) (replLL-id ll ind rll refl) (a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind)) ≡ ind
a≤ᵢb-morph-id {i} {u} {ll} {.ll} ↓ = refl
a≤ᵢb-morph-id {i} {u} {(li ∧ _)} {rll} (ind ←∧) with replLL rll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | replLL li ind rll | replLL-id li ind rll refl | a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind) | a≤ᵢb-morph-id ind
a≤ᵢb-morph-id {i} {u} {li ∧ _} {.h} (ind ←∧) | h | refl | .li | refl | .ind | refl = refl
a≤ᵢb-morph-id {i} {u} {(_ ∧ ri)} {rll} (∧→ ind) with replLL rll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | replLL ri ind rll | replLL-id ri ind rll refl | a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind) | a≤ᵢb-morph-id ind
a≤ᵢb-morph-id {i} {u} {_ ∧ ri} {.h} (∧→ ind) | h | refl | .ri | refl | .ind | refl = refl
a≤ᵢb-morph-id {i} {u} {(li ∨ _)} {rll} (ind ←∨) with replLL rll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | replLL li ind rll | replLL-id li ind rll refl | a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind) | a≤ᵢb-morph-id ind
a≤ᵢb-morph-id {i} {u} {li ∨ _} {.h} (ind ←∨) | h | refl | .li | refl | .ind | refl = refl
a≤ᵢb-morph-id {i} {u} {(_ ∨ ri)} {rll} (∨→ ind) with replLL rll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | replLL ri ind rll | replLL-id ri ind rll refl | a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind) | a≤ᵢb-morph-id ind
a≤ᵢb-morph-id {i} {u} {_ ∨ ri} {.h} (∨→ ind) | h | refl | .ri | refl | .ind | refl = refl
a≤ᵢb-morph-id {i} {u} {(li ∂ _)} {rll} (ind ←∂) with replLL rll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | replLL li ind rll | replLL-id li ind rll refl | a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind) | a≤ᵢb-morph-id ind
a≤ᵢb-morph-id {i} {u} {li ∂ _} {.h} (ind ←∂) | h | refl | .li | refl | .ind | refl = refl
a≤ᵢb-morph-id {i} {u} {(_ ∂ ri)} {rll} (∂→ ind) with replLL rll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | replLL ri ind rll | replLL-id ri ind rll refl | a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind) | a≤ᵢb-morph-id ind
a≤ᵢb-morph-id {i} {u} {_ ∂ ri} {.h} (∂→ ind) | h | refl | .ri | refl | .ind | refl = refl


module _ where

  open Relation.Binary.HeterogeneousEquality

  a≤ᵢb-morph-hid : ∀{i u ll rll}
               → (ind : IndexLL {i} {u} rll ll)
               → (a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind)) ≅ ind
  a≤ᵢb-morph-hid {ll = ll} {rll = rll} ind with replLL rll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll | replLL-↓ {ell = rll} ind | replLL ll ind rll | replLL-id ll ind rll refl | (a≤ᵢb-morph ind ind rll (≤ᵢ-reflexive ind)) | a≤ᵢb-morph-id ind
  a≤ᵢb-morph-hid {_} {_} {.r} {.q} .y | q | refl | r | refl | y | refl = refl



replLL-a≤b≡a : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll) → ∀ gll
               → (ind : IndexLL rll ll) → ∀ frll → (lt : emi ≤ᵢ ind)
               → replLL (replLL ll ind frll) (a≤ᵢb-morph emi ind frll lt) gll ≡ replLL ll emi gll
replLL-a≤b≡a ↓ gll ind frll ≤ᵢ↓ = refl
replLL-a≤b≡a {ll = li ∧ ri} (emi ←∧) gll (ind ←∧) frll (≤ᵢ←∧ lt)
  with (replLL (replLL li ind frll) (a≤ᵢb-morph emi ind frll lt) gll)
       | (replLL-a≤b≡a emi gll ind frll lt)
replLL-a≤b≡a {ll = li ∧ ri} (emi ←∧) gll (ind ←∧) frll (≤ᵢ←∧ lt) | .(replLL li emi gll) | refl = refl
replLL-a≤b≡a {ll = li ∧ ri} (∧→ emi) gll (∧→ ind) frll (≤ᵢ∧→ lt)
  with (replLL (replLL ri ind frll) (a≤ᵢb-morph emi ind frll lt) gll)
       | (replLL-a≤b≡a emi gll ind frll lt)
replLL-a≤b≡a {ll = li ∧ ri} (∧→ emi) gll (∧→ ind) frll (≤ᵢ∧→ lt) | .(replLL ri emi gll) | refl = refl
replLL-a≤b≡a {ll = li ∨ ri} (emi ←∨) gll (ind ←∨) frll (≤ᵢ←∨ lt)
  with (replLL (replLL li ind frll) (a≤ᵢb-morph emi ind frll lt) gll)
       | (replLL-a≤b≡a emi gll ind frll lt)
replLL-a≤b≡a {ll = li ∨ ri} (emi ←∨) gll (ind ←∨) frll (≤ᵢ←∨ lt) | .(replLL li emi gll) | refl = refl
replLL-a≤b≡a {ll = li ∨ ri} (∨→ emi) gll (∨→ ind) frll (≤ᵢ∨→ lt)
  with (replLL (replLL ri ind frll) (a≤ᵢb-morph emi ind frll lt) gll)
       | (replLL-a≤b≡a emi gll ind frll lt)
replLL-a≤b≡a {ll = li ∨ ri} (∨→ emi) gll (∨→ ind) frll (≤ᵢ∨→ lt) | .(replLL ri emi gll) | refl = refl
replLL-a≤b≡a {ll = li ∂ ri} (emi ←∂) gll (ind ←∂) frll (≤ᵢ←∂ lt)
  with (replLL (replLL li ind frll) (a≤ᵢb-morph emi ind frll lt) gll)
       | (replLL-a≤b≡a emi gll ind frll lt)
replLL-a≤b≡a {ll = li ∂ ri} (emi ←∂) gll (ind ←∂) frll (≤ᵢ←∂ lt) | .(replLL li emi gll) | refl = refl
replLL-a≤b≡a {ll = li ∂ ri} (∂→ emi) gll (∂→ ind) frll (≤ᵢ∂→ lt)
  with (replLL (replLL ri ind frll) (a≤ᵢb-morph emi ind frll lt) gll)
       | (replLL-a≤b≡a emi gll ind frll lt)
replLL-a≤b≡a {ll = li ∂ ri} (∂→ emi) gll (∂→ ind) frll (≤ᵢ∂→ lt) | .(replLL ri emi gll) | refl = refl



¬ord-morph : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll)
             → (ind : IndexLL rll ll) → ∀ frll → (nord : ¬ Orderedᵢ ind emi)
             → IndexLL fll (replLL ll ind frll)
¬ord-morph ↓ ind frll nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
¬ord-morph (emi ←∧) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓)) 
¬ord-morph (emi ←∧) (ind ←∧) frll nord =
            (¬ord-morph emi ind frll (¬ord-spec nord)) ←∧
¬ord-morph (emi ←∧) (∧→ ind) frll nord = emi ←∧
¬ord-morph (∧→ emi) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
¬ord-morph (∧→ emi) (ind ←∧) frll nord = ∧→ emi
¬ord-morph (∧→ emi) (∧→ ind) frll nord = 
           ∧→ (¬ord-morph emi ind frll (¬ord-spec nord))
¬ord-morph (emi ←∨) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓)) 
¬ord-morph (emi ←∨) (ind ←∨) frll nord = 
           (¬ord-morph emi ind frll (¬ord-spec nord)) ←∨
¬ord-morph (emi ←∨) (∨→ ind) frll nord = emi ←∨
¬ord-morph (∨→ emi) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
¬ord-morph (∨→ emi) (ind ←∨) frll nord = ∨→ emi
¬ord-morph (∨→ emi) (∨→ ind) frll nord = 
           ∨→ (¬ord-morph emi ind frll (¬ord-spec nord))
¬ord-morph (emi ←∂) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓) )
¬ord-morph (emi ←∂) (ind ←∂) frll nord =
           (¬ord-morph emi ind frll (¬ord-spec nord)) ←∂
¬ord-morph (emi ←∂) (∂→ ind) frll nord = emi ←∂
¬ord-morph (∂→ emi) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
¬ord-morph (∂→ emi) (ind ←∂) frll nord = ∂→ emi
¬ord-morph (∂→ emi) (∂→ ind) frll nord = 
           ∂→ (¬ord-morph emi ind frll (¬ord-spec nord))

module _ where

  replLL-¬ordab≡ba' : ∀{i u rll ll fll}
    → (emi : IndexLL {i} {u} fll ll) → ∀ gll
    → (ind : IndexLL rll ll) → ∀ frll
    → (nord : ¬ Orderedᵢ ind emi)
    → (fnord : ¬ Orderedᵢ emi ind)
    → replLL (replLL ll ind frll) (¬ord-morph emi ind frll nord) gll ≡ replLL (replLL ll emi gll) (¬ord-morph ind emi gll fnord) frll
  replLL-¬ordab≡ba' ↓ gll ind frll nord _ = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
  replLL-¬ordab≡ba' (emi ←∧) gll ↓ frll nord _ = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
  replLL-¬ordab≡ba' {ll = li ∧ ri} (emi ←∧) gll (ind ←∧) frll nord fnord
    with replLL-¬ordab≡ba' emi gll ind frll (¬ord-spec nord) (¬ord-spec fnord) where
  ... | r = cong (λ x → x ∧ ri) r 
  replLL-¬ordab≡ba' (emi ←∧) gll (∧→ ind) frll nord _ = refl
  replLL-¬ordab≡ba' (∧→ emi) gll ↓ frll nord _ = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
  replLL-¬ordab≡ba' {ll = li ∧ ri} (∧→ emi) gll (∧→ ind) frll nord fnord
    with replLL-¬ordab≡ba' emi gll ind frll (¬ord-spec nord) (¬ord-spec fnord) where
  ... | r = cong (λ x → li ∧ x) r
  replLL-¬ordab≡ba' (∧→ emi) gll (ind ←∧) frll nord _ = refl
  replLL-¬ordab≡ba' (emi ←∨) gll ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
  replLL-¬ordab≡ba' {ll = li ∨ ri} (emi ←∨) gll (ind ←∨) frll nord fnord
    with replLL-¬ordab≡ba' emi gll ind frll (¬ord-spec nord) (¬ord-spec fnord) where
  ... | r = cong (λ x → x ∨ ri) r
  replLL-¬ordab≡ba' (emi ←∨) gll (∨→ ind) frll nord _ = refl
  replLL-¬ordab≡ba' (∨→ emi) gll ↓ frll nord _ = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
  replLL-¬ordab≡ba' {ll = li ∨ ri} (∨→ emi) gll (∨→ ind) frll nord fnord
    with replLL-¬ordab≡ba' emi gll ind frll (¬ord-spec nord) (¬ord-spec fnord) where
  ... | r = cong (λ x → li ∨ x) r
  replLL-¬ordab≡ba' (∨→ emi) gll (ind ←∨) frll nord _ = refl
  replLL-¬ordab≡ba' (emi ←∂) gll ↓ frll nord _ = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
  replLL-¬ordab≡ba' {ll = li ∂ ri} (emi ←∂) gll (ind ←∂) frll nord fnord
    with replLL-¬ordab≡ba' emi gll ind frll (¬ord-spec nord) (¬ord-spec fnord) where
  ... | r = cong (λ x → x ∂ ri) r
  replLL-¬ordab≡ba' (emi ←∂) gll (∂→ ind) frll nord _ = refl
  replLL-¬ordab≡ba' (∂→ emi) gll ↓ frll nord _ = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
  replLL-¬ordab≡ba' {ll = li ∂ ri} (∂→ emi) gll (∂→ ind) frll nord fnord
    with replLL-¬ordab≡ba' emi gll ind frll (¬ord-spec nord) (¬ord-spec fnord) where
  ... | r = cong (λ x → li ∂ x) r
  replLL-¬ordab≡ba' (∂→ emi) gll (ind ←∂) frll nord _ = refl
   
  replLL-¬ordab≡ba : ∀{i u rll ll fll}
    → (emi : IndexLL {i} {u} fll ll) → ∀ gll
    → (ind : IndexLL rll ll) → ∀ frll
    → (nord : ¬ Orderedᵢ ind emi)
    → replLL (replLL ll ind frll) (¬ord-morph emi ind frll nord) gll ≡ replLL (replLL ll emi gll) (¬ord-morph ind emi gll (flipNotOrdᵢ nord)) frll
  replLL-¬ordab≡ba emi gll ind frll nord = replLL-¬ordab≡ba' emi gll ind frll nord (flipNotOrdᵢ nord)
  

lemma₁-¬ord-a≤ᵢb : ∀{i u ll pll rll fll}
      → (emi : IndexLL {i} {u} fll ll)
      → (ind : IndexLL rll ll) → ∀ ell → (lt : emi ≤ᵢ ind)
      → (omi : IndexLL pll (replLL ll ind ell))
      → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind ell lt) omi)
      → IndexLL pll ll
lemma₁-¬ord-a≤ᵢb ↓ ind ell ≤ᵢ↓ omi nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
lemma₁-¬ord-a≤ᵢb (emi ←∧) (ind ←∧) ell (≤ᵢ←∧ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
lemma₁-¬ord-a≤ᵢb (emi ←∧) (ind ←∧) ell (≤ᵢ←∧ lt) (omi ←∧) nord
     = (lemma₁-¬ord-a≤ᵢb emi ind ell lt omi (¬ord-spec nord)) ←∧
lemma₁-¬ord-a≤ᵢb (emi ←∧) (ind ←∧) ell (≤ᵢ←∧ lt) (∧→ omi) nord = ∧→ omi
lemma₁-¬ord-a≤ᵢb (∧→ emi) (∧→ ind) ell (≤ᵢ∧→ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
lemma₁-¬ord-a≤ᵢb (∧→ emi) (∧→ ind) ell (≤ᵢ∧→ lt) (omi ←∧) nord = omi ←∧
lemma₁-¬ord-a≤ᵢb (∧→ emi) (∧→ ind) ell (≤ᵢ∧→ lt) (∧→ omi) nord
     = ∧→ (lemma₁-¬ord-a≤ᵢb emi ind ell lt omi (¬ord-spec nord)) 
lemma₁-¬ord-a≤ᵢb (emi ←∨) (ind ←∨) ell (≤ᵢ←∨ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
lemma₁-¬ord-a≤ᵢb (emi ←∨) (ind ←∨) ell (≤ᵢ←∨ lt) (omi ←∨) nord
     = (lemma₁-¬ord-a≤ᵢb emi ind ell lt omi (¬ord-spec nord)) ←∨
lemma₁-¬ord-a≤ᵢb (emi ←∨) (ind ←∨) ell (≤ᵢ←∨ lt) (∨→ omi) nord = ∨→ omi
lemma₁-¬ord-a≤ᵢb (∨→ emi) (∨→ ind) ell (≤ᵢ∨→ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
lemma₁-¬ord-a≤ᵢb (∨→ emi) (∨→ ind) ell (≤ᵢ∨→ lt) (omi ←∨) nord = omi ←∨
lemma₁-¬ord-a≤ᵢb (∨→ emi) (∨→ ind) ell (≤ᵢ∨→ lt) (∨→ omi) nord
     = ∨→ (lemma₁-¬ord-a≤ᵢb emi ind ell lt omi (¬ord-spec nord)) 
lemma₁-¬ord-a≤ᵢb (emi ←∂) (ind ←∂) ell (≤ᵢ←∂ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
lemma₁-¬ord-a≤ᵢb (emi ←∂) (ind ←∂) ell (≤ᵢ←∂ lt) (omi ←∂) nord
     = (lemma₁-¬ord-a≤ᵢb emi ind ell lt omi (¬ord-spec nord)) ←∂
lemma₁-¬ord-a≤ᵢb (emi ←∂) (ind ←∂) ell (≤ᵢ←∂ lt) (∂→ omi) nord = ∂→ omi
lemma₁-¬ord-a≤ᵢb (∂→ emi) (∂→ ind) ell (≤ᵢ∂→ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
lemma₁-¬ord-a≤ᵢb (∂→ emi) (∂→ ind) ell (≤ᵢ∂→ lt) (omi ←∂) nord = omi ←∂
lemma₁-¬ord-a≤ᵢb (∂→ emi) (∂→ ind) ell (≤ᵢ∂→ lt) (∂→ omi) nord
     = ∂→ (lemma₁-¬ord-a≤ᵢb emi ind ell lt omi (¬ord-spec nord)) 



¬ord-morph⇒¬ord : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll)
      → (ind : IndexLL rll ll) → ∀ frll → (nord : ¬ Orderedᵢ ind emi)
      → ¬ Orderedᵢ (a≤ᵢb-morph ind ind frll (≤ᵢ-reflexive ind)) (¬ord-morph emi ind frll nord)
¬ord-morph⇒¬ord ↓ ind frll nord = λ _ → nord (b≤ᵢa ≤ᵢ↓)
¬ord-morph⇒¬ord (emi ←∧) ↓ frll nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
¬ord-morph⇒¬ord (emi ←∧) (ind ←∧) frll nord x with ¬ord-morph⇒¬ord emi ind frll (¬ord-spec nord) where
¬ord-morph⇒¬ord (emi ←∧) (ind ←∧) frll nord (a≤ᵢb (≤ᵢ←∧ x)) | r = r (a≤ᵢb x)
¬ord-morph⇒¬ord (emi ←∧) (ind ←∧) frll nord (b≤ᵢa (≤ᵢ←∧ x)) | r = r (b≤ᵢa x)
¬ord-morph⇒¬ord (emi ←∧) (∧→ ind) frll nord (a≤ᵢb ())
¬ord-morph⇒¬ord (emi ←∧) (∧→ ind) frll nord (b≤ᵢa ())
¬ord-morph⇒¬ord (∧→ emi) ↓ frll nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
¬ord-morph⇒¬ord (∧→ emi) (ind ←∧) frll nord (a≤ᵢb ())
¬ord-morph⇒¬ord (∧→ emi) (ind ←∧) frll nord (b≤ᵢa ())
¬ord-morph⇒¬ord (∧→ emi) (∧→ ind) frll nord x with ¬ord-morph⇒¬ord emi ind frll (¬ord-spec nord) where
¬ord-morph⇒¬ord (∧→ emi) (∧→ ind) frll nord (a≤ᵢb (≤ᵢ∧→ x)) | r = r (a≤ᵢb x)
¬ord-morph⇒¬ord (∧→ emi) (∧→ ind) frll nord (b≤ᵢa (≤ᵢ∧→ x)) | r = r (b≤ᵢa x)
¬ord-morph⇒¬ord (emi ←∨) ↓ frll nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
¬ord-morph⇒¬ord (emi ←∨) (ind ←∨) frll nord x with ¬ord-morph⇒¬ord emi ind frll (¬ord-spec nord) where
¬ord-morph⇒¬ord (emi ←∨) (ind ←∨) frll nord (a≤ᵢb (≤ᵢ←∨ x)) | r = r (a≤ᵢb x)
¬ord-morph⇒¬ord (emi ←∨) (ind ←∨) frll nord (b≤ᵢa (≤ᵢ←∨ x)) | r = r (b≤ᵢa x)
¬ord-morph⇒¬ord (emi ←∨) (∨→ ind) frll nord (a≤ᵢb ())
¬ord-morph⇒¬ord (emi ←∨) (∨→ ind) frll nord (b≤ᵢa ())
¬ord-morph⇒¬ord (∨→ emi) ↓ frll nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
¬ord-morph⇒¬ord (∨→ emi) (ind ←∨) frll nord (a≤ᵢb ())
¬ord-morph⇒¬ord (∨→ emi) (ind ←∨) frll nord (b≤ᵢa ())
¬ord-morph⇒¬ord (∨→ emi) (∨→ ind) frll nord x with ¬ord-morph⇒¬ord emi ind frll (¬ord-spec nord) where
¬ord-morph⇒¬ord (∨→ emi) (∨→ ind) frll nord (a≤ᵢb (≤ᵢ∨→ x)) | r = r (a≤ᵢb x)
¬ord-morph⇒¬ord (∨→ emi) (∨→ ind) frll nord (b≤ᵢa (≤ᵢ∨→ x)) | r = r (b≤ᵢa x)
¬ord-morph⇒¬ord (emi ←∂) ↓ frll nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
¬ord-morph⇒¬ord (emi ←∂) (ind ←∂) frll nord x with ¬ord-morph⇒¬ord emi ind frll (¬ord-spec nord) where
¬ord-morph⇒¬ord (emi ←∂) (ind ←∂) frll nord (a≤ᵢb (≤ᵢ←∂ x)) | r = r (a≤ᵢb x)
¬ord-morph⇒¬ord (emi ←∂) (ind ←∂) frll nord (b≤ᵢa (≤ᵢ←∂ x)) | r = r (b≤ᵢa x)
¬ord-morph⇒¬ord (emi ←∂) (∂→ ind) frll nord (a≤ᵢb ())
¬ord-morph⇒¬ord (emi ←∂) (∂→ ind) frll nord (b≤ᵢa ())
¬ord-morph⇒¬ord (∂→ emi) ↓ frll nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
¬ord-morph⇒¬ord (∂→ emi) (ind ←∂) frll nord (a≤ᵢb ())
¬ord-morph⇒¬ord (∂→ emi) (ind ←∂) frll nord (b≤ᵢa ())
¬ord-morph⇒¬ord (∂→ emi) (∂→ ind) frll nord x with ¬ord-morph⇒¬ord emi ind frll (¬ord-spec nord) where
¬ord-morph⇒¬ord (∂→ emi) (∂→ ind) frll nord (a≤ᵢb (≤ᵢ∂→ x)) | r = r (a≤ᵢb x)
¬ord-morph⇒¬ord (∂→ emi) (∂→ ind) frll nord (b≤ᵢa (≤ᵢ∂→ x)) | r = r (b≤ᵢa x)



rlemma₁⇒¬ord : ∀{i u ll pll rll fll}
      → (emi : IndexLL {i} {u} fll ll)
      → (ind : IndexLL rll ll) → ∀ ell → (lt : emi ≤ᵢ ind)
      → (omi : IndexLL pll (replLL ll ind ell))
      → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind ell lt) omi)
      → ¬ Orderedᵢ emi (lemma₁-¬ord-a≤ᵢb emi ind ell lt omi nord)
rlemma₁⇒¬ord ↓ ind ell ≤ᵢ↓ omi nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
rlemma₁⇒¬ord (emi ←∧) (ind ←∧) ell (≤ᵢ←∧ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
rlemma₁⇒¬ord (emi ←∧) (ind ←∧) ell (≤ᵢ←∧ lt) (omi ←∧) nord
  = λ { (a≤ᵢb (≤ᵢ←∧ x)) → n (a≤ᵢb x)
      ; (b≤ᵢa (≤ᵢ←∧ x)) → n (b≤ᵢa x) } where
  n = (rlemma₁⇒¬ord emi ind ell lt omi (¬ord-spec nord))
rlemma₁⇒¬ord {i} {u} {pll = pll} {fll = fll} (emi ←∧) (ind ←∧) ell (≤ᵢ←∧ lt) (∧→ omi) nord = hf emi omi  where
  hf : ∀{li ri} → (emi : IndexLL {i} {u} fll li)
       → (omi : IndexLL pll ri)
       → ¬ Orderedᵢ (emi ←∧) (∧→ omi)
  hf emi omi (a≤ᵢb ())
  hf emi omi (b≤ᵢa ())
rlemma₁⇒¬ord (∧→ emi) (∧→ ind) ell (≤ᵢ∧→ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
rlemma₁⇒¬ord (∧→ emi) (∧→ ind) ell (≤ᵢ∧→ lt) (∧→ omi) nord
  = λ { (a≤ᵢb (≤ᵢ∧→ x)) → n (a≤ᵢb x)
      ; (b≤ᵢa (≤ᵢ∧→ x)) → n (b≤ᵢa x) } where
  n = (rlemma₁⇒¬ord emi ind ell lt omi (¬ord-spec nord))
rlemma₁⇒¬ord {i} {u} {pll = pll} {fll = fll} (∧→ emi) (∧→ ind) ell (≤ᵢ∧→ lt) (omi ←∧) nord = hf emi omi  where
  hf : ∀{li ri} → (emi : IndexLL {i} {u} fll ri)
       → (omi : IndexLL pll li)
       → ¬ Orderedᵢ (∧→ emi) (omi ←∧)
  hf emi omi (a≤ᵢb ())
  hf emi omi (b≤ᵢa ())
rlemma₁⇒¬ord (emi ←∨) (ind ←∨) ell (≤ᵢ←∨ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
rlemma₁⇒¬ord (emi ←∨) (ind ←∨) ell (≤ᵢ←∨ lt) (omi ←∨) nord
  = λ { (a≤ᵢb (≤ᵢ←∨ x)) → n (a≤ᵢb x)
      ; (b≤ᵢa (≤ᵢ←∨ x)) → n (b≤ᵢa x) } where
  n = (rlemma₁⇒¬ord emi ind ell lt omi (¬ord-spec nord))
rlemma₁⇒¬ord {i} {u} {pll = pll} {fll = fll} (emi ←∨) (ind ←∨) ell (≤ᵢ←∨ lt) (∨→ omi) nord = hf emi omi  where
  hf : ∀{li ri} → (emi : IndexLL {i} {u} fll li)
       → (omi : IndexLL pll ri)
       → ¬ Orderedᵢ (emi ←∨) (∨→ omi)
  hf emi omi (a≤ᵢb ())
  hf emi omi (b≤ᵢa ())
rlemma₁⇒¬ord (∨→ emi) (∨→ ind) ell (≤ᵢ∨→ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
rlemma₁⇒¬ord (∨→ emi) (∨→ ind) ell (≤ᵢ∨→ lt) (∨→ omi) nord
  = λ { (a≤ᵢb (≤ᵢ∨→ x)) → n (a≤ᵢb x)
      ; (b≤ᵢa (≤ᵢ∨→ x)) → n (b≤ᵢa x) } where
  n = (rlemma₁⇒¬ord emi ind ell lt omi (¬ord-spec nord))
rlemma₁⇒¬ord {i} {u} {pll = pll} {fll = fll} (∨→ emi) (∨→ ind) ell (≤ᵢ∨→ lt) (omi ←∨) nord = hf emi omi  where
  hf : ∀{li ri} → (emi : IndexLL {i} {u} fll ri)
       → (omi : IndexLL pll li)
       → ¬ Orderedᵢ (∨→ emi) (omi ←∨)
  hf emi omi (a≤ᵢb ())
  hf emi omi (b≤ᵢa ())
rlemma₁⇒¬ord (emi ←∂) (ind ←∂) ell (≤ᵢ←∂ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
rlemma₁⇒¬ord (emi ←∂) (ind ←∂) ell (≤ᵢ←∂ lt) (omi ←∂) nord
  = λ { (a≤ᵢb (≤ᵢ←∂ x)) → n (a≤ᵢb x)
      ; (b≤ᵢa (≤ᵢ←∂ x)) → n (b≤ᵢa x) } where
  n = (rlemma₁⇒¬ord emi ind ell lt omi (¬ord-spec nord))
rlemma₁⇒¬ord {i} {u} {pll = pll} {fll = fll} (emi ←∂) (ind ←∂) ell (≤ᵢ←∂ lt) (∂→ omi) nord = hf emi omi  where
  hf : ∀{li ri} → (emi : IndexLL {i} {u} fll li)
       → (omi : IndexLL pll ri)
       → ¬ Orderedᵢ (emi ←∂) (∂→ omi)
  hf emi omi (a≤ᵢb ())
  hf emi omi (b≤ᵢa ())
rlemma₁⇒¬ord (∂→ emi) (∂→ ind) ell (≤ᵢ∂→ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
rlemma₁⇒¬ord (∂→ emi) (∂→ ind) ell (≤ᵢ∂→ lt) (∂→ omi) nord
  = λ { (a≤ᵢb (≤ᵢ∂→ x)) → n (a≤ᵢb x)
      ; (b≤ᵢa (≤ᵢ∂→ x)) → n (b≤ᵢa x) } where
  n = (rlemma₁⇒¬ord emi ind ell lt omi (¬ord-spec nord))
rlemma₁⇒¬ord {i} {u} {pll = pll} {fll = fll} (∂→ emi) (∂→ ind) ell (≤ᵢ∂→ lt) (omi ←∂) nord = hf emi omi  where
  hf : ∀{li ri} → (emi : IndexLL {i} {u} fll ri)
       → (omi : IndexLL pll li)
       → ¬ Orderedᵢ (∂→ emi) (omi ←∂)
  hf emi omi (a≤ᵢb ())
  hf emi omi (b≤ᵢa ())


module _ where

  ¬ord-morph$lemma₁≡I' : ∀{i u pll ll cll fll} → ∀ ell → (emi : IndexLL {i} {u} fll ll) → (ind : IndexLL {i} {u} pll ll) → (lt : emi ≤ᵢ ind) → (lind : IndexLL cll (replLL ll ind ell)) → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind ell lt) lind) → (lnord : ¬ Orderedᵢ ind (lemma₁-¬ord-a≤ᵢb emi ind ell lt lind nord))
         → (¬ord-morph (lemma₁-¬ord-a≤ᵢb emi ind ell lt lind nord) ind ell lnord ≡ lind)
  ¬ord-morph$lemma₁≡I' ell ↓ ind ≤ᵢ↓ lind nord _ = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
  ¬ord-morph$lemma₁≡I' ell (emi ←∧) (ind ←∧) (≤ᵢ←∧ lt) ↓ nord _ = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
  ¬ord-morph$lemma₁≡I' ell (emi ←∧) (ind ←∧) (≤ᵢ←∧ lt) (lind ←∧) nord lnord = cong (λ x → x ←∧) r where
    r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
  ¬ord-morph$lemma₁≡I' ell (emi ←∧) (ind ←∧) (≤ᵢ←∧ lt) (∧→ lind) nord _ = refl
  ¬ord-morph$lemma₁≡I' ell (∧→ emi) (∧→ ind) (≤ᵢ∧→ lt) ↓ nord _ = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
  ¬ord-morph$lemma₁≡I' ell (∧→ emi) (∧→ ind) (≤ᵢ∧→ lt) (lind ←∧) nord _ = refl
  ¬ord-morph$lemma₁≡I' ell (∧→ emi) (∧→ ind) (≤ᵢ∧→ lt) (∧→ lind) nord lnord = cong (λ x → ∧→ x) r where
    r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
  ¬ord-morph$lemma₁≡I' ell (emi ←∨) (ind ←∨) (≤ᵢ←∨ lt) ↓ nord _ = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
  ¬ord-morph$lemma₁≡I' ell (emi ←∨) (ind ←∨) (≤ᵢ←∨ lt) (lind ←∨) nord lnord = cong (λ x → x ←∨) r where
    r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
  ¬ord-morph$lemma₁≡I' ell (emi ←∨) (ind ←∨) (≤ᵢ←∨ lt) (∨→ lind) nord _ = refl
  ¬ord-morph$lemma₁≡I' ell (∨→ emi) (∨→ ind) (≤ᵢ∨→ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
  ¬ord-morph$lemma₁≡I' ell (∨→ emi) (∨→ ind) (≤ᵢ∨→ lt) (lind ←∨) nord _ = refl
  ¬ord-morph$lemma₁≡I' ell (∨→ emi) (∨→ ind) (≤ᵢ∨→ lt) (∨→ lind) nord lnord = cong (λ x → ∨→ x) r where
    r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
  ¬ord-morph$lemma₁≡I' ell (emi ←∂) (ind ←∂) (≤ᵢ←∂ lt) ↓ nord _ = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
  ¬ord-morph$lemma₁≡I' ell (emi ←∂) (ind ←∂) (≤ᵢ←∂ lt) (lind ←∂) nord lnord = cong (λ x → x ←∂) r where
    r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
  ¬ord-morph$lemma₁≡I' ell (emi ←∂) (ind ←∂) (≤ᵢ←∂ lt) (∂→ lind) nord _ = refl
  ¬ord-morph$lemma₁≡I' ell (∂→ emi) (∂→ ind) (≤ᵢ∂→ lt) ↓ nord _ = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
  ¬ord-morph$lemma₁≡I' ell (∂→ emi) (∂→ ind) (≤ᵢ∂→ lt) (lind ←∂) nord _ = refl
  ¬ord-morph$lemma₁≡I' ell (∂→ emi) (∂→ ind) (≤ᵢ∂→ lt) (∂→ lind) nord lnord = cong (λ x → ∂→ x) r where
    r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
    
  ¬ord-morph$lemma₁≡I : ∀{i u pll ll cll fll} → ∀ ell → (emi : IndexLL {i} {u} fll ll) → (ind : IndexLL {i} {u} pll ll) → (lt : emi ≤ᵢ ind) → (lind : IndexLL cll (replLL ll ind ell)) → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind ell lt) lind)
       → (¬ord-morph (lemma₁-¬ord-a≤ᵢb emi ind ell lt lind nord) ind ell (a≤ᵢb&¬ordac⇒¬ordbc lt (rlemma₁⇒¬ord emi ind ell lt lind nord)) ≡ lind)
  ¬ord-morph$lemma₁≡I ell emi ind lt lind nord = ¬ord-morph$lemma₁≡I' ell emi ind lt lind nord (a≤ᵢb&¬ordac⇒¬ordbc lt (rlemma₁⇒¬ord emi ind ell lt lind nord))



_+ᵢ_ : ∀{i u pll cll ll} → IndexLL {i} {u} pll ll → IndexLL cll pll → IndexLL cll ll
_+ᵢ_ ↓ is = is
_+ᵢ_ (if ←∧) is = (_+ᵢ_ if is) ←∧
_+ᵢ_ (∧→ if) is = ∧→ (_+ᵢ_ if is)
_+ᵢ_ (if ←∨) is = (_+ᵢ_ if is) ←∨
_+ᵢ_ (∨→ if) is = ∨→ (_+ᵢ_ if is)
_+ᵢ_ (if ←∂) is = (_+ᵢ_ if is) ←∂
_+ᵢ_ (∂→ if) is = ∂→ (_+ᵢ_ if is)




+ᵢ⇒l≤ᵢ+ᵢ : ∀{i u pll cll ll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll)
           → ind ≤ᵢ (ind +ᵢ lind)
+ᵢ⇒l≤ᵢ+ᵢ ↓ lind = ≤ᵢ↓
+ᵢ⇒l≤ᵢ+ᵢ (ind ←∧) lind = ≤ᵢ←∧ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
+ᵢ⇒l≤ᵢ+ᵢ (∧→ ind) lind = ≤ᵢ∧→ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
+ᵢ⇒l≤ᵢ+ᵢ (ind ←∨) lind = ≤ᵢ←∨ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
+ᵢ⇒l≤ᵢ+ᵢ (∨→ ind) lind = ≤ᵢ∨→ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
+ᵢ⇒l≤ᵢ+ᵢ (ind ←∂) lind = ≤ᵢ←∂ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
+ᵢ⇒l≤ᵢ+ᵢ (∂→ ind) lind = ≤ᵢ∂→ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)


a+↓≡a : ∀{i u pll ll} → (a : IndexLL {i} {u} pll ll) → a +ᵢ ↓ ≡ a
a+↓≡a ↓ = refl
a+↓≡a (a ←∧) with (a +ᵢ ↓) | (a+↓≡a a)
a+↓≡a (a ←∧) | .a | refl = refl
a+↓≡a (∧→ a) with (a +ᵢ ↓) | (a+↓≡a a)
a+↓≡a (∧→ a) | .a | refl = refl
a+↓≡a (a ←∨) with (a +ᵢ ↓) | (a+↓≡a a)
a+↓≡a (a ←∨) | .a | refl = refl
a+↓≡a (∨→ a) with (a +ᵢ ↓) | (a+↓≡a a)
a+↓≡a (∨→ a) | .a | refl = refl
a+↓≡a (a ←∂) with (a +ᵢ ↓) | (a+↓≡a a)
a+↓≡a (a ←∂) | .a | refl = refl
a+↓≡a (∂→ a) with (a +ᵢ ↓) | (a+↓≡a a)
a+↓≡a (∂→ a) | .a | refl = refl


[a+b]-a=b : ∀{i u rll ll fll} → (a : IndexLL {i} {u} fll ll)
          → (b : IndexLL rll fll)
          → ((a +ᵢ b) -ᵢ a) (+ᵢ⇒l≤ᵢ+ᵢ a b) ≡ b
[a+b]-a=b ↓ b = refl
[a+b]-a=b (a ←∧) b = [a+b]-a=b a b
[a+b]-a=b (∧→ a) b = [a+b]-a=b a b
[a+b]-a=b (a ←∨) b = [a+b]-a=b a b
[a+b]-a=b (∨→ a) b = [a+b]-a=b a b
[a+b]-a=b (a ←∂) b = [a+b]-a=b a b
[a+b]-a=b (∂→ a) b = [a+b]-a=b a b

a+[b-a]=b : ∀{i u rll ll fll} → (a : IndexLL {i} {u} fll ll)
            → (b : IndexLL rll ll)
            → (lt : a ≤ᵢ b)
            → (a +ᵢ (b -ᵢ a) lt) ≡ b
a+[b-a]=b ↓ b ≤ᵢ↓ = refl
a+[b-a]=b (a ←∧) (b ←∧) (≤ᵢ←∧ lt) with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
a+[b-a]=b (a ←∧) (b ←∧) (≤ᵢ←∧ lt) | .b | refl = refl
a+[b-a]=b (∧→ a) (∧→ b) (≤ᵢ∧→ lt) with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
a+[b-a]=b (∧→ a) (∧→ b) (≤ᵢ∧→ lt) | .b | refl = refl
a+[b-a]=b (a ←∨) (b ←∨) (≤ᵢ←∨ lt) with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
a+[b-a]=b (a ←∨) (b ←∨) (≤ᵢ←∨ lt) | .b | refl = refl
a+[b-a]=b (∨→ a) (∨→ b) (≤ᵢ∨→ lt)with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
a+[b-a]=b (∨→ a) (∨→ b) (≤ᵢ∨→ lt) | .b | refl = refl
a+[b-a]=b (a ←∂) (b ←∂) (≤ᵢ←∂ lt) with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
a+[b-a]=b (a ←∂) (b ←∂) (≤ᵢ←∂ lt) | .b | refl = refl
a+[b-a]=b (∂→ a) (∂→ b) (≤ᵢ∂→ lt) with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
a+[b-a]=b (∂→ a) (∂→ b) (≤ᵢ∂→ lt) | .b | refl = refl



-- A predicate that is true if pll is not transformed by ltr.

data UpTran {i u} : ∀ {ll pll rll} → IndexLL pll ll → LLTr {i} {u} rll ll → Set u where
  indI : ∀{pll ll} → {ind : IndexLL pll ll} → UpTran ind I
  ←∂∂c : ∀{pll li ri rll ltr} → {ind : IndexLL pll ri} → UpTran {ll = li ∂ ri} {rll = rll} (∂→ ind) ltr
         → UpTran (ind ←∂) (∂c ltr)
  ∂→∂c : ∀{pll li ri rll ltr} → {ind : IndexLL pll li} → UpTran {ll = li ∂ ri} {rll = rll} (ind ←∂) ltr
         → UpTran (∂→ ind) (∂c ltr)
  ←∨∨c : ∀{pll li ri rll ltr} → {ind : IndexLL pll ri} → UpTran {ll = li ∨ ri} {rll = rll} (∨→ ind) ltr
         → UpTran (ind ←∨) (∨c ltr)
  ∨→∨c : ∀{pll li ri rll ltr} → {ind : IndexLL pll li} → UpTran {ll = li ∨ ri} {rll = rll} (ind ←∨) ltr
         → UpTran (∨→ ind) (∨c ltr)
  ←∧∧c : ∀{pll li ri rll ltr} → {ind : IndexLL pll ri} → UpTran {ll = li ∧ ri} {rll = rll} (∧→ ind) ltr
         → UpTran (ind ←∧) (∧c ltr)
  ∧→∧c : ∀{pll li ri rll ltr} → {ind : IndexLL pll li} → UpTran {ll = li ∧ ri} {rll = rll} (ind ←∧) ltr
         → UpTran (∧→ ind) (∧c ltr)
  ←∧]←∧∧∧d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lli}
            → UpTran {rll = rll} (ind ←∧) ltr → UpTran {ll = (lli ∧ lri) ∧ ri} ((ind ←∧) ←∧) (∧∧d ltr)
  ∧→]←∧∧∧d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lri}
            → UpTran {rll = rll} (∧→ (ind ←∧)) ltr
            → UpTran {ll = (lli ∧ lri) ∧ ri} ((∧→ ind) ←∧) (∧∧d ltr)
  ∧→∧∧d    : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll ri}
            → UpTran {rll = rll} (∧→ (∧→ ind)) ltr
            → UpTran {ll = ((lli ∧ lri) ∧ ri)} (∧→ ind) (∧∧d ltr)
  ←∧¬∧∧d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll li}
            → UpTran {rll = rll} ((ind ←∧) ←∧) ltr
            → UpTran {ll = li ∧ (rli ∧ rri)} (ind ←∧) (¬∧∧d ltr)
  ∧→[←∧¬∧∧d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} ((∧→ ind) ←∧) ltr
            → UpTran {ll = li ∧ (rli ∧ rri)} (∧→ (ind ←∧)) (¬∧∧d ltr)
  ∧→[∧→¬∧∧d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∧→ ind) ltr
            → UpTran {ll = li ∧ (rli ∧ rri)} (∧→ (∧→ ind)) (¬∧∧d ltr)
  ←∨]←∨∨∨d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lli}
            → UpTran {rll = rll} (ind ←∨) ltr → UpTran {ll = (lli ∨ lri) ∨ ri} ((ind ←∨) ←∨) (∨∨d ltr)
  ∨→]←∨∨∨d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lri}
            → UpTran {rll = rll} (∨→ (ind ←∨)) ltr
            → UpTran {ll = (lli ∨ lri) ∨ ri} ((∨→ ind) ←∨) (∨∨d ltr)
  ∨→∨∨d    : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll ri}
            → UpTran {rll = rll} (∨→ (∨→ ind)) ltr
            → UpTran {ll = (lli ∨ lri) ∨ ri} (∨→ ind) (∨∨d ltr)
  ←∨¬∨∨d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll li}
            → UpTran {rll = rll} ((ind ←∨) ←∨) ltr
            → UpTran {ll = li ∨ (rli ∨ rri)} (ind ←∨) (¬∨∨d ltr)
  ∨→[←∨¬∨∨d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} ((∨→ ind) ←∨) ltr
            → UpTran {ll = li ∨ (rli ∨ rri)} (∨→ (ind ←∨)) (¬∨∨d ltr)
  ∨→[∨→¬∨∨d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∨→ ind) ltr
            → UpTran {ll = li ∨ (rli ∨ rri)} (∨→ (∨→ ind)) (¬∨∨d ltr)
  ←∂]←∂∂∂d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lli}
            → UpTran {rll = rll} (ind ←∂) ltr → UpTran {ll = (lli ∂ lri) ∂ ri} ((ind ←∂) ←∂) (∂∂d ltr)
  ∂→]←∂∂∂d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lri}
            → UpTran {rll = rll} (∂→ (ind ←∂)) ltr
            → UpTran {ll = (lli ∂ lri) ∂ ri} ((∂→ ind) ←∂) (∂∂d ltr)
  ∂→∂∂d    : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll ri}
            → UpTran {rll = rll} (∂→ (∂→ ind)) ltr
            → UpTran {ll = (lli ∂ lri) ∂ ri} (∂→ ind) (∂∂d ltr)
  ←∂¬∂∂d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll li}
            → UpTran {rll = rll} ((ind ←∂) ←∂) ltr
            → UpTran {ll = li ∂ (rli ∂ rri)} (ind ←∂) (¬∂∂d ltr)
  ∂→[←∂¬∂∂d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} ((∂→ ind) ←∂) ltr
            → UpTran {ll = li ∂ (rli ∂ rri)} (∂→ (ind ←∂)) (¬∂∂d ltr)
  ∂→[∂→¬∂∂d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∂→ ind) ltr
            → UpTran {ll = li ∂ (rli ∂ rri)} (∂→ (∂→ ind)) (¬∂∂d ltr)

isUpTran : ∀ {i u ll pll rll} → (ind : IndexLL pll ll) → (ltr : LLTr {i} {u} rll ll) → Dec (UpTran ind ltr)
isUpTran ind I = yes indI
isUpTran ↓ (∂c ltr) = no (λ ())
isUpTran (ind ←∂) (∂c ltr) with (isUpTran (∂→ ind) ltr)
isUpTran (ind ←∂) (∂c ltr) | yes ut = yes (←∂∂c ut)
isUpTran (ind ←∂) (∂c ltr) | no ¬ut = no (λ {(←∂∂c ut) → ¬ut ut})
isUpTran (∂→ ind) (∂c ltr)  with (isUpTran (ind ←∂) ltr)
isUpTran (∂→ ind) (∂c ltr) | yes ut = yes (∂→∂c ut)
isUpTran (∂→ ind) (∂c ltr) | no ¬ut = no (λ {(∂→∂c ut) → ¬ut ut})
isUpTran ↓ (∨c ltr) = no (λ ())
isUpTran (ind ←∨) (∨c ltr) with (isUpTran (∨→ ind) ltr)
isUpTran (ind ←∨) (∨c ltr) | yes p = yes (←∨∨c p)
isUpTran (ind ←∨) (∨c ltr) | no ¬p = no (λ {(←∨∨c p) → ¬p p}) 
isUpTran (∨→ ind) (∨c ltr) with (isUpTran (ind ←∨) ltr)
isUpTran (∨→ ind) (∨c ltr) | yes p = yes (∨→∨c p)
isUpTran (∨→ ind) (∨c ltr) | no ¬p = no (λ {(∨→∨c ut) → ¬p ut})
isUpTran ↓ (∧c ltr) = no (λ ())
isUpTran (ind ←∧) (∧c ltr) with (isUpTran (∧→ ind) ltr)
isUpTran (ind ←∧) (∧c ltr) | yes p = yes (←∧∧c p)
isUpTran (ind ←∧) (∧c ltr) | no ¬p = no (λ {(←∧∧c ut) → ¬p ut}) 
isUpTran (∧→ ind) (∧c ltr) with (isUpTran (ind ←∧) ltr)
isUpTran (∧→ ind) (∧c ltr) | yes p = yes (∧→∧c p)
isUpTran (∧→ ind) (∧c ltr) | no ¬p = no (λ {(∧→∧c ut) → ¬p ut})
isUpTran ↓ (∧∧d ltr) = no (λ ())
isUpTran (↓ ←∧) (∧∧d ltr) = no (λ ())
isUpTran ((ind ←∧) ←∧) (∧∧d ltr) with (isUpTran (ind ←∧) ltr)
isUpTran ((ind ←∧) ←∧) (∧∧d ltr) | yes p = yes (←∧]←∧∧∧d p)
isUpTran ((ind ←∧) ←∧) (∧∧d ltr) | no ¬p = no (λ {(←∧]←∧∧∧d ut) → ¬p ut}) 
isUpTran ((∧→ ind) ←∧) (∧∧d ltr) with (isUpTran (∧→ (ind ←∧)) ltr)
isUpTran ((∧→ ind) ←∧) (∧∧d ltr) | yes p = yes (∧→]←∧∧∧d p)
isUpTran ((∧→ ind) ←∧) (∧∧d ltr) | no ¬p = no (λ {(∧→]←∧∧∧d ut) → ¬p ut}) 
isUpTran (∧→ ind) (∧∧d ltr) with (isUpTran (∧→ (∧→ ind)) ltr)
isUpTran (∧→ ind) (∧∧d ltr) | yes p = yes (∧→∧∧d p)
isUpTran (∧→ ind) (∧∧d ltr) | no ¬p = no (λ {(∧→∧∧d ut) → ¬p ut})
isUpTran ↓ (¬∧∧d ltr) = no (λ ())
isUpTran (ind ←∧) (¬∧∧d ltr) with (isUpTran ((ind ←∧) ←∧) ltr)
isUpTran (ind ←∧) (¬∧∧d ltr) | yes p = yes (←∧¬∧∧d p)
isUpTran (ind ←∧) (¬∧∧d ltr) | no ¬p = no (λ {(←∧¬∧∧d ut) → ¬p ut})
isUpTran (∧→ ↓) (¬∧∧d ltr) = no (λ ())
isUpTran (∧→ (ind ←∧)) (¬∧∧d ltr) with (isUpTran ((∧→ ind) ←∧) ltr)
isUpTran (∧→ (ind ←∧)) (¬∧∧d ltr) | yes p = yes (∧→[←∧¬∧∧d p)
isUpTran (∧→ (ind ←∧)) (¬∧∧d ltr) | no ¬p = no (λ {(∧→[←∧¬∧∧d ut) → ¬p ut})
isUpTran (∧→ (∧→ ind)) (¬∧∧d ltr) with (isUpTran (∧→ ind) ltr)
isUpTran (∧→ (∧→ ind)) (¬∧∧d ltr) | yes p = yes (∧→[∧→¬∧∧d p)
isUpTran (∧→ (∧→ ind)) (¬∧∧d ltr) | no ¬p = no (λ {(∧→[∧→¬∧∧d ut) → ¬p ut})
isUpTran ↓ (∨∨d ltr) = no (λ ())
isUpTran (↓ ←∨) (∨∨d ltr) = no (λ ())
isUpTran ((ind ←∨) ←∨) (∨∨d ltr) with (isUpTran (ind ←∨) ltr)
isUpTran ((ind ←∨) ←∨) (∨∨d ltr) | yes p = yes (←∨]←∨∨∨d p)
isUpTran ((ind ←∨) ←∨) (∨∨d ltr) | no ¬p = no (λ {(←∨]←∨∨∨d ut) → ¬p ut}) 
isUpTran ((∨→ ind) ←∨) (∨∨d ltr) with (isUpTran (∨→ (ind ←∨)) ltr)
isUpTran ((∨→ ind) ←∨) (∨∨d ltr) | yes p = yes (∨→]←∨∨∨d p)
isUpTran ((∨→ ind) ←∨) (∨∨d ltr) | no ¬p = no (λ {(∨→]←∨∨∨d ut) → ¬p ut}) 
isUpTran (∨→ ind) (∨∨d ltr) with (isUpTran (∨→ (∨→ ind)) ltr)
isUpTran (∨→ ind) (∨∨d ltr) | yes p = yes (∨→∨∨d p)
isUpTran (∨→ ind) (∨∨d ltr) | no ¬p = no (λ {(∨→∨∨d ut) → ¬p ut})
isUpTran ↓ (¬∨∨d ltr) = no (λ ())
isUpTran (ind ←∨) (¬∨∨d ltr) with (isUpTran ((ind ←∨) ←∨) ltr)
isUpTran (ind ←∨) (¬∨∨d ltr) | yes p = yes (←∨¬∨∨d p)
isUpTran (ind ←∨) (¬∨∨d ltr) | no ¬p = no (λ {(←∨¬∨∨d ut) → ¬p ut})
isUpTran (∨→ ↓) (¬∨∨d ltr) = no (λ ())
isUpTran (∨→ (ind ←∨)) (¬∨∨d ltr) with (isUpTran ((∨→ ind) ←∨) ltr)
isUpTran (∨→ (ind ←∨)) (¬∨∨d ltr) | yes p = yes (∨→[←∨¬∨∨d p)
isUpTran (∨→ (ind ←∨)) (¬∨∨d ltr) | no ¬p = no (λ {(∨→[←∨¬∨∨d ut) → ¬p ut})
isUpTran (∨→ (∨→ ind)) (¬∨∨d ltr) with (isUpTran (∨→ ind) ltr)
isUpTran (∨→ (∨→ ind)) (¬∨∨d ltr) | yes p = yes (∨→[∨→¬∨∨d p)
isUpTran (∨→ (∨→ ind)) (¬∨∨d ltr) | no ¬p = no (λ {(∨→[∨→¬∨∨d ut) → ¬p ut})
isUpTran ↓ (∂∂d ltr) = no (λ ())
isUpTran (↓ ←∂) (∂∂d ltr) = no (λ ())
isUpTran ((ind ←∂) ←∂) (∂∂d ltr) with (isUpTran (ind ←∂) ltr)
isUpTran ((ind ←∂) ←∂) (∂∂d ltr) | yes p = yes (←∂]←∂∂∂d p)
isUpTran ((ind ←∂) ←∂) (∂∂d ltr) | no ¬p = no (λ {(←∂]←∂∂∂d ut) → ¬p ut})
isUpTran ((∂→ ind) ←∂) (∂∂d ltr) with (isUpTran (∂→ (ind ←∂)) ltr)
isUpTran ((∂→ ind) ←∂) (∂∂d ltr) | yes p = yes (∂→]←∂∂∂d p)
isUpTran ((∂→ ind) ←∂) (∂∂d ltr) | no ¬p = no (λ {(∂→]←∂∂∂d ut) → ¬p ut})
isUpTran (∂→ ind) (∂∂d ltr) with (isUpTran (∂→ (∂→ ind)) ltr)
isUpTran (∂→ ind) (∂∂d ltr) | yes p = yes (∂→∂∂d p)
isUpTran (∂→ ind) (∂∂d ltr) | no ¬p = no (λ {(∂→∂∂d ut) → ¬p ut})
isUpTran ↓ (¬∂∂d ltr) = no (λ ())
isUpTran (ind ←∂) (¬∂∂d ltr) with (isUpTran ((ind ←∂) ←∂) ltr)
isUpTran (ind ←∂) (¬∂∂d ltr) | yes p = yes (←∂¬∂∂d p)
isUpTran (ind ←∂) (¬∂∂d ltr) | no ¬p = no (λ {(←∂¬∂∂d ut) → ¬p ut})
isUpTran (∂→ ↓) (¬∂∂d ltr) = no (λ ())
isUpTran (∂→ (ind ←∂)) (¬∂∂d ltr) with (isUpTran ((∂→ ind) ←∂) ltr)
isUpTran (∂→ (ind ←∂)) (¬∂∂d ltr) | yes p = yes (∂→[←∂¬∂∂d p)
isUpTran (∂→ (ind ←∂)) (¬∂∂d ltr) | no ¬p = no (λ {(∂→[←∂¬∂∂d ut) → ¬p ut})
isUpTran (∂→ (∂→ ind)) (¬∂∂d ltr) with (isUpTran (∂→ ind) ltr)
isUpTran (∂→ (∂→ ind)) (¬∂∂d ltr) | yes p = yes (∂→[∂→¬∂∂d p)
isUpTran (∂→ (∂→ ind)) (¬∂∂d ltr) | no ¬p = no (λ {(∂→[∂→¬∂∂d ut) → ¬p ut})


indLow⇒UpTran : ∀ {i u rll ll n dt df} → (ind : IndexLL (τ {i} {u} {n} {dt} df) ll)
                → (ltr : LLTr {i} {u} rll ll) → UpTran ind ltr
indLow⇒UpTran ↓ I = indI
indLow⇒UpTran (ind ←∧) I = indI
indLow⇒UpTran (ind ←∧) (∧c ltr) = ←∧∧c r where
  r = indLow⇒UpTran (∧→ ind) ltr
indLow⇒UpTran ((ind ←∧) ←∧) (∧∧d ltr) = ←∧]←∧∧∧d r where
  r = indLow⇒UpTran (ind ←∧) ltr
indLow⇒UpTran ((∧→ ind) ←∧) (∧∧d ltr) = ∧→]←∧∧∧d r where
  r = indLow⇒UpTran (∧→ (ind ←∧)) ltr
indLow⇒UpTran (ind ←∧) (¬∧∧d ltr) = ←∧¬∧∧d r where
  r = indLow⇒UpTran ((ind ←∧) ←∧) ltr
indLow⇒UpTran (∧→ ind) I = indI
indLow⇒UpTran (∧→ ind) (∧c ltr) = ∧→∧c r where
  r = indLow⇒UpTran (ind ←∧) ltr
indLow⇒UpTran (∧→ ind) (∧∧d ltr) = ∧→∧∧d r where
  r = indLow⇒UpTran (∧→ (∧→ ind)) ltr
indLow⇒UpTran (∧→ (ind ←∧)) (¬∧∧d ltr) = ∧→[←∧¬∧∧d r where
  r = indLow⇒UpTran ((∧→ ind) ←∧) ltr
indLow⇒UpTran (∧→ (∧→ ind)) (¬∧∧d ltr) = ∧→[∧→¬∧∧d r where
  r = indLow⇒UpTran (∧→ ind) ltr
indLow⇒UpTran (ind ←∨) I = indI
indLow⇒UpTran (ind ←∨) (∨c ltr) = ←∨∨c r where
  r = indLow⇒UpTran (∨→ ind) ltr
indLow⇒UpTran ((ind ←∨) ←∨) (∨∨d ltr) = ←∨]←∨∨∨d r where
  r = indLow⇒UpTran (ind ←∨) ltr
indLow⇒UpTran ((∨→ ind) ←∨) (∨∨d ltr) = ∨→]←∨∨∨d r where
  r = indLow⇒UpTran (∨→ (ind ←∨)) ltr
indLow⇒UpTran (ind ←∨) (¬∨∨d ltr) = ←∨¬∨∨d r where
  r = indLow⇒UpTran ((ind ←∨) ←∨) ltr
indLow⇒UpTran (∨→ ind) I = indI
indLow⇒UpTran (∨→ ind) (∨c ltr) = ∨→∨c r where
  r = indLow⇒UpTran (ind ←∨) ltr
indLow⇒UpTran (∨→ ind) (∨∨d ltr) = ∨→∨∨d r where
  r = indLow⇒UpTran (∨→ (∨→ ind)) ltr
indLow⇒UpTran (∨→ (ind ←∨)) (¬∨∨d ltr) = ∨→[←∨¬∨∨d r where
  r = indLow⇒UpTran ((∨→ ind) ←∨) ltr
indLow⇒UpTran (∨→ (∨→ ind)) (¬∨∨d ltr) = ∨→[∨→¬∨∨d r where
  r = indLow⇒UpTran (∨→ ind) ltr
indLow⇒UpTran (ind ←∂) I = indI
indLow⇒UpTran (ind ←∂) (∂c ltr) = ←∂∂c r where
  r = indLow⇒UpTran (∂→ ind) ltr
indLow⇒UpTran ((ind ←∂) ←∂) (∂∂d ltr) = ←∂]←∂∂∂d r where
  r = indLow⇒UpTran (ind ←∂) ltr
indLow⇒UpTran ((∂→ ind) ←∂) (∂∂d ltr) = ∂→]←∂∂∂d r where
  r = indLow⇒UpTran (∂→ (ind ←∂)) ltr
indLow⇒UpTran (ind ←∂) (¬∂∂d ltr) = ←∂¬∂∂d r where
  r = indLow⇒UpTran ((ind ←∂) ←∂) ltr
indLow⇒UpTran (∂→ ind) I = indI
indLow⇒UpTran (∂→ ind) (∂c ltr) = ∂→∂c r where
  r = indLow⇒UpTran (ind ←∂) ltr
indLow⇒UpTran (∂→ ind) (∂∂d ltr) = ∂→∂∂d r where
  r = indLow⇒UpTran (∂→ (∂→ ind)) ltr
indLow⇒UpTran (∂→ (ind ←∂)) (¬∂∂d ltr) = ∂→[←∂¬∂∂d r where
  r = indLow⇒UpTran ((∂→ ind) ←∂) ltr
indLow⇒UpTran (∂→ (∂→ ind)) (¬∂∂d ltr) = ∂→[∂→¬∂∂d r where
  r = indLow⇒UpTran (∂→ ind) ltr



tran : ∀ {i u ll pll rll} → (ind : IndexLL pll ll) → (ltr : LLTr {i} {u} rll ll) → UpTran ind ltr
       → IndexLL pll rll
tran ind I indI = ind 
tran ↓ (∂c ltr) () 
tran (ind ←∂) (∂c ltr) (←∂∂c ut) = tran (∂→ ind) ltr ut
tran (∂→ ind) (∂c ltr) (∂→∂c ut) =  tran (ind ←∂) ltr ut
tran ↓ (∨c ltr) () 
tran (ind ←∨) (∨c ltr) (←∨∨c ut) = tran (∨→ ind) ltr ut
tran (∨→ ind) (∨c ltr) (∨→∨c ut) = tran (ind ←∨) ltr ut
tran ↓ (∧c ltr) () 
tran (ind ←∧) (∧c ltr) (←∧∧c ut) = tran (∧→ ind) ltr ut
tran (∧→ ind) (∧c ltr) (∧→∧c ut) = tran (ind ←∧) ltr ut
tran ↓ (∧∧d ltr) () 
tran (↓ ←∧) (∧∧d ltr) () 
tran ((ind ←∧) ←∧) (∧∧d ltr) (←∧]←∧∧∧d ut) = tran (ind ←∧) ltr ut
tran ((∧→ ind) ←∧) (∧∧d ltr) (∧→]←∧∧∧d ut) = tran (∧→ (ind ←∧)) ltr ut
tran (∧→ ind) (∧∧d ltr) (∧→∧∧d ut) = tran (∧→ (∧→ ind)) ltr ut
tran ↓ (¬∧∧d ltr) () 
tran (ind ←∧) (¬∧∧d ltr) (←∧¬∧∧d ut) = tran ((ind ←∧) ←∧) ltr ut
tran (∧→ ↓) (¬∧∧d ltr) () 
tran (∧→ (ind ←∧)) (¬∧∧d ltr) (∧→[←∧¬∧∧d ut) = tran ((∧→ ind) ←∧) ltr ut
tran (∧→ (∧→ ind)) (¬∧∧d ltr) (∧→[∧→¬∧∧d ut) = tran (∧→ ind) ltr ut
tran ↓ (∨∨d ltr) () 
tran (↓ ←∨) (∨∨d ltr) () 
tran ((ind ←∨) ←∨) (∨∨d ltr) (←∨]←∨∨∨d ut) = tran (ind ←∨) ltr ut
tran ((∨→ ind) ←∨) (∨∨d ltr) (∨→]←∨∨∨d ut) = tran (∨→ (ind ←∨)) ltr ut
tran (∨→ ind) (∨∨d ltr) (∨→∨∨d ut) = tran (∨→ (∨→ ind)) ltr ut
tran ↓ (¬∨∨d ltr) () 
tran (ind ←∨) (¬∨∨d ltr) (←∨¬∨∨d ut) = tran ((ind ←∨) ←∨) ltr ut
tran (∨→ ↓) (¬∨∨d ltr) () 
tran (∨→ (ind ←∨)) (¬∨∨d ltr) (∨→[←∨¬∨∨d ut) = tran ((∨→ ind) ←∨) ltr ut
tran (∨→ (∨→ ind)) (¬∨∨d ltr) (∨→[∨→¬∨∨d ut) = tran (∨→ ind) ltr ut
tran ↓ (∂∂d ltr) () 
tran (↓ ←∂) (∂∂d ltr) () 
tran ((ind ←∂) ←∂) (∂∂d ltr) (←∂]←∂∂∂d ut) = tran (ind ←∂) ltr ut
tran ((∂→ ind) ←∂) (∂∂d ltr) (∂→]←∂∂∂d ut) = tran (∂→ (ind ←∂)) ltr ut
tran (∂→ ind) (∂∂d ltr) (∂→∂∂d ut) = tran (∂→ (∂→ ind)) ltr ut
tran ↓ (¬∂∂d ltr) () 
tran (ind ←∂) (¬∂∂d ltr) (←∂¬∂∂d ut) = tran ((ind ←∂) ←∂) ltr ut
tran (∂→ ↓) (¬∂∂d ltr) () 
tran (∂→ (ind ←∂)) (¬∂∂d ltr) (∂→[←∂¬∂∂d ut) = tran ((∂→ ind) ←∂) ltr ut
tran (∂→ (∂→ ind)) (¬∂∂d ltr) (∂→[∂→¬∂∂d ut) = tran (∂→ ind) ltr ut


tr-ltr-morph : ∀ {i u ll pll orll} → ∀ frll → (ind : IndexLL pll ll) → (ltr : LLTr {i} {u} orll ll) → (rvT : UpTran ind ltr) → LLTr (replLL orll (tran ind ltr rvT) frll) (replLL ll ind frll)
tr-ltr-morph frll ↓ .I indI = I
tr-ltr-morph frll (ind ←∧) I indI = I
tr-ltr-morph frll (ind ←∧) (∧c ltr) (←∧∧c rvT) with tr-ltr-morph frll (∧→ ind) ltr rvT
... | r = ∧c r
tr-ltr-morph frll ((ind ←∧) ←∧) (∧∧d ltr) (←∧]←∧∧∧d rvT) with tr-ltr-morph frll (ind ←∧) ltr rvT
... | r = ∧∧d r
tr-ltr-morph frll ((∧→ ind) ←∧) (∧∧d ltr) (∧→]←∧∧∧d rvT) with tr-ltr-morph frll (∧→ (ind ←∧)) ltr rvT
... | r = ∧∧d r
tr-ltr-morph frll (ind ←∧) (¬∧∧d ltr) (←∧¬∧∧d rvT) with tr-ltr-morph frll ((ind ←∧) ←∧) ltr rvT
... | r = ¬∧∧d r
tr-ltr-morph frll (∧→ ind) I indI = I
tr-ltr-morph frll (∧→ ind) (∧c ltr) (∧→∧c rvT) with tr-ltr-morph frll (ind ←∧) ltr rvT
... | r = ∧c r
tr-ltr-morph frll (∧→ ind) (∧∧d ltr) (∧→∧∧d rvT) with tr-ltr-morph frll (∧→ (∧→ ind)) ltr rvT
... | r = ∧∧d r
tr-ltr-morph frll (∧→ (ind ←∧)) (¬∧∧d ltr) (∧→[←∧¬∧∧d rvT) with tr-ltr-morph frll ((∧→ ind) ←∧) ltr rvT
... | r = ¬∧∧d r
tr-ltr-morph frll (∧→ (∧→ ind)) (¬∧∧d ltr) (∧→[∧→¬∧∧d rvT)  with tr-ltr-morph frll (∧→ ind) ltr rvT
... | r = ¬∧∧d r
tr-ltr-morph frll (ind ←∨) I indI = I
tr-ltr-morph frll (ind ←∨) (∨c ltr) (←∨∨c rvT) with tr-ltr-morph frll (∨→ ind) ltr rvT
... | r = ∨c r
tr-ltr-morph frll ((ind ←∨) ←∨) (∨∨d ltr) (←∨]←∨∨∨d rvT) with tr-ltr-morph frll (ind ←∨) ltr rvT
... | r = ∨∨d r
tr-ltr-morph frll ((∨→ ind) ←∨) (∨∨d ltr) (∨→]←∨∨∨d rvT) with tr-ltr-morph frll (∨→ (ind ←∨)) ltr rvT
... | r = ∨∨d r
tr-ltr-morph frll (ind ←∨) (¬∨∨d ltr) (←∨¬∨∨d rvT) with tr-ltr-morph frll ((ind ←∨) ←∨) ltr rvT
... | r = ¬∨∨d r
tr-ltr-morph frll (∨→ ind) I indI = I
tr-ltr-morph frll (∨→ ind) (∨c ltr) (∨→∨c rvT) with tr-ltr-morph frll (ind ←∨) ltr rvT
... | r = ∨c r
tr-ltr-morph frll (∨→ ind) (∨∨d ltr) (∨→∨∨d rvT) with tr-ltr-morph frll (∨→ (∨→ ind)) ltr rvT
... | r = ∨∨d r
tr-ltr-morph frll (∨→ (ind ←∨)) (¬∨∨d ltr) (∨→[←∨¬∨∨d rvT) with tr-ltr-morph frll ((∨→ ind) ←∨) ltr rvT
... | r = ¬∨∨d r
tr-ltr-morph frll (∨→ (∨→ ind)) (¬∨∨d ltr) (∨→[∨→¬∨∨d rvT)  with tr-ltr-morph frll (∨→ ind) ltr rvT
... | r = ¬∨∨d r
tr-ltr-morph frll (ind ←∂) I indI = I
tr-ltr-morph frll (ind ←∂) (∂c ltr) (←∂∂c rvT) with tr-ltr-morph frll (∂→ ind) ltr rvT
... | r = ∂c r
tr-ltr-morph frll ((ind ←∂) ←∂) (∂∂d ltr) (←∂]←∂∂∂d rvT) with tr-ltr-morph frll (ind ←∂) ltr rvT
... | r = ∂∂d r
tr-ltr-morph frll ((∂→ ind) ←∂) (∂∂d ltr) (∂→]←∂∂∂d rvT) with tr-ltr-morph frll (∂→ (ind ←∂)) ltr rvT
... | r = ∂∂d r
tr-ltr-morph frll (ind ←∂) (¬∂∂d ltr) (←∂¬∂∂d rvT) with tr-ltr-morph frll ((ind ←∂) ←∂) ltr rvT
... | r = ¬∂∂d r
tr-ltr-morph frll (∂→ ind) I indI = I
tr-ltr-morph frll (∂→ ind) (∂c ltr) (∂→∂c rvT) with tr-ltr-morph frll (ind ←∂) ltr rvT
... | r = ∂c r
tr-ltr-morph frll (∂→ ind) (∂∂d ltr) (∂→∂∂d rvT) with tr-ltr-morph frll (∂→ (∂→ ind)) ltr rvT
... | r = ∂∂d r
tr-ltr-morph frll (∂→ (ind ←∂)) (¬∂∂d ltr) (∂→[←∂¬∂∂d rvT) with tr-ltr-morph frll ((∂→ ind) ←∂) ltr rvT
... | r = ¬∂∂d r
tr-ltr-morph frll (∂→ (∂→ ind)) (¬∂∂d ltr) (∂→[∂→¬∂∂d rvT)  with tr-ltr-morph frll (∂→ ind) ltr rvT
... | r = ¬∂∂d r



drepl=>repl+ : ∀{i u pll ll cll frll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll)
               → (replLL ll ind (replLL pll lind frll)) ≡ replLL ll (ind +ᵢ lind) frll
drepl=>repl+ ↓ lind = refl
drepl=>repl+ {pll = pll} {ll = li ∧ ri} {frll = frll} (ind ←∧) lind
             with (replLL li ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∧ ri} {_} {frll} (ind ←∧) lind
             | .(replLL li (ind +ᵢ lind) frll) | refl = refl
drepl=>repl+ {pll = pll} {ll = li ∧ ri} {frll = frll} (∧→ ind) lind
             with (replLL ri ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∧ ri} {_} {frll} (∧→ ind) lind
             | .(replLL ri (ind +ᵢ lind) frll) | refl = refl
drepl=>repl+ {pll = pll} {ll = li ∨ ri} {frll = frll} (ind ←∨) lind
             with (replLL li ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∨ ri} {_} {frll} (ind ←∨) lind
             | .(replLL li (ind +ᵢ lind) frll) | refl = refl
drepl=>repl+ {pll = pll} {ll = li ∨ ri} {frll = frll} (∨→ ind) lind
             with (replLL ri ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∨ ri} {_} {frll} (∨→ ind) lind
             | .(replLL ri (ind +ᵢ lind) frll) | refl = refl
drepl=>repl+ {pll = pll} {ll = li ∂ ri} {frll = frll} (ind ←∂) lind
             with (replLL li ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∂ ri} {_} {frll} (ind ←∂) lind
             | .(replLL li (ind +ᵢ lind) frll) | refl = refl
drepl=>repl+ {pll = pll} {ll = li ∂ ri} {frll = frll} (∂→ ind) lind
             with (replLL ri ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∂ ri} {_} {frll} (∂→ ind) lind
             | .(replLL ri (ind +ᵢ lind) frll) | refl = refl



repl-r=>l : ∀{i u pll ll cll frll} → ∀ ell → (ind : IndexLL {i} {u} pll ll) → (x : IndexLL cll (replLL ll ind ell)) → let uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind)
       in (ltuindx : uind ≤ᵢ x)
       → (replLL ll ind (replLL ell (ind-rpl↓ ind ((x -ᵢ uind) ltuindx)) frll) ≡ replLL (replLL ll ind ell) x frll)
repl-r=>l ell ↓ x ≤ᵢ↓ = refl
repl-r=>l {ll = li ∧ ri} ell (ind ←∧) (x ←∧) (≤ᵢ←∧ ltuindx) = cong (λ x → x ∧ ri) (repl-r=>l ell ind x ltuindx)
repl-r=>l {ll = li ∧ ri} ell (∧→ ind) (∧→ x) (≤ᵢ∧→ ltuindx) = cong (λ x → li ∧ x) (repl-r=>l ell ind x ltuindx)
repl-r=>l {ll = li ∨ ri} ell (ind ←∨) (x ←∨) (≤ᵢ←∨ ltuindx) = cong (λ x → x ∨ ri) (repl-r=>l ell ind x ltuindx)
repl-r=>l {ll = li ∨ ri} ell (∨→ ind) (∨→ x) (≤ᵢ∨→ ltuindx) = cong (λ x → li ∨ x) (repl-r=>l ell ind x ltuindx)
repl-r=>l {ll = li ∂ ri} ell (ind ←∂) (x ←∂) (≤ᵢ←∂ ltuindx) = cong (λ x → x ∂ ri) (repl-r=>l ell ind x ltuindx)
repl-r=>l {ll = li ∂ ri} ell (∂→ ind) (∂→ x) (≤ᵢ∂→ ltuindx) = cong (λ x → li ∂ x) (repl-r=>l ell ind x ltuindx)



-- Deprecated
updInd : ∀{i u rll ll} → ∀ nrll → (ind : IndexLL {i} {u} rll ll)
         → IndexLL {i} {u} nrll (replLL ll ind nrll)
updInd nrll ↓ = ↓
updInd nrll (ind ←∧) = (updInd nrll ind) ←∧
updInd nrll (∧→ ind) = ∧→ (updInd nrll ind)
updInd nrll (ind ←∨) = (updInd nrll ind) ←∨
updInd nrll (∨→ ind) = ∨→ (updInd nrll ind)
updInd nrll (ind ←∂) = (updInd nrll ind) ←∂
updInd nrll (∂→ ind) = ∂→ (updInd nrll ind)

-- Deprecated
-- Maybe instead of this function use a≤ᵢb-morph
updIndGen : ∀{i u pll ll cll} → ∀ nrll → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll)
            → IndexLL {i} {u} (replLL pll lind nrll) (replLL ll (ind +ᵢ lind) nrll)
updIndGen nrll ↓ lind = ↓
updIndGen nrll (ind ←∧) lind = (updIndGen nrll ind lind) ←∧
updIndGen nrll (∧→ ind) lind = ∧→ (updIndGen nrll ind lind)
updIndGen nrll (ind ←∨) lind = (updIndGen nrll ind lind) ←∨
updIndGen nrll (∨→ ind) lind = ∨→ (updIndGen nrll ind lind)
updIndGen nrll (ind ←∂) lind = (updIndGen nrll ind lind) ←∂
updIndGen nrll (∂→ ind) lind = ∂→ (updIndGen nrll ind lind)



-- TODO This negation was writen so as to return nothing if ¬ (b ≤ᵢ a)
_-ₘᵢ_ : ∀ {i u pll cll ll} → IndexLL {i} {u} cll ll → IndexLL pll ll → Maybe $ IndexLL cll pll
a -ₘᵢ ↓ = just a
↓ -ₘᵢ (b ←∧) = nothing
(a ←∧) -ₘᵢ (b ←∧) = a -ₘᵢ b
(∧→ a) -ₘᵢ (b ←∧) = nothing
↓ -ₘᵢ (∧→ b) = nothing
(a ←∧) -ₘᵢ (∧→ b) = nothing
(∧→ a) -ₘᵢ (∧→ b) = a -ₘᵢ b
↓ -ₘᵢ (b ←∨) = nothing
(a ←∨) -ₘᵢ (b ←∨) = a -ₘᵢ b
(∨→ a) -ₘᵢ (b ←∨) = nothing
↓ -ₘᵢ (∨→ b) = nothing
(a ←∨) -ₘᵢ (∨→ b) = nothing
(∨→ a) -ₘᵢ (∨→ b) = a -ₘᵢ b
↓ -ₘᵢ (b ←∂) = nothing
(a ←∂) -ₘᵢ (b ←∂) = a -ₘᵢ b
(∂→ a) -ₘᵢ (b ←∂) = nothing
↓ -ₘᵢ (∂→ b) = nothing
(a ←∂) -ₘᵢ (∂→ b) = nothing
(∂→ a) -ₘᵢ (∂→ b) = a -ₘᵢ b

-- Deprecated
b-s≡j⇒s≤ᵢb : ∀ {i u pll cll ll} → (bind : IndexLL {i} {u} cll ll) → (sind : IndexLL pll ll)
             →  Σ (IndexLL {i} {u} cll pll) (λ x → (bind -ₘᵢ sind) ≡ just x) → sind ≤ᵢ bind
b-s≡j⇒s≤ᵢb bind ↓ (rs , x) = ≤ᵢ↓
b-s≡j⇒s≤ᵢb ↓ (sind ←∧) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∧) (sind ←∧) (rs , x) = ≤ᵢ←∧ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
b-s≡j⇒s≤ᵢb (∧→ bind) (sind ←∧) (rs , ())
b-s≡j⇒s≤ᵢb ↓ (∧→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∧) (∧→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (∧→ bind) (∧→ sind) (rs , x) = ≤ᵢ∧→ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
b-s≡j⇒s≤ᵢb ↓ (sind ←∨) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∨) (sind ←∨) (rs , x) = ≤ᵢ←∨ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
b-s≡j⇒s≤ᵢb (∨→ bind) (sind ←∨) (rs , ())
b-s≡j⇒s≤ᵢb ↓ (∨→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∨) (∨→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (∨→ bind) (∨→ sind) (rs , x) =  ≤ᵢ∨→ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
b-s≡j⇒s≤ᵢb ↓ (sind ←∂) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∂) (sind ←∂) (rs , x) = ≤ᵢ←∂ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
b-s≡j⇒s≤ᵢb (∂→ bind) (sind ←∂) (rs , ())
b-s≡j⇒s≤ᵢb ↓ (∂→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∂) (∂→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (∂→ bind) (∂→ sind) (rs , x) = ≤ᵢ∂→ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)

-- Deprecated
revUpdInd : ∀{i u ll cll ell pll} → (b : IndexLL pll ll) → (a : IndexLL {i} {u} cll (replLL ll b ell))
            → a -ₘᵢ (updInd ell b) ≡ nothing → (updInd ell b) -ₘᵢ a ≡ nothing → IndexLL cll ll
revUpdInd ↓ a () b-a
revUpdInd (b ←∧) ↓ refl ()
revUpdInd (b ←∧) (a ←∧) a-b b-a = revUpdInd b a a-b b-a ←∧
revUpdInd (b ←∧) (∧→ a) a-b b-a = ∧→ a
revUpdInd (∧→ b) ↓ refl ()
revUpdInd (∧→ b) (a ←∧) a-b b-a = a ←∧
revUpdInd (∧→ b) (∧→ a) a-b b-a = ∧→ revUpdInd b a a-b b-a
revUpdInd (b ←∨) ↓ refl ()
revUpdInd (b ←∨) (a ←∨) a-b b-a = revUpdInd b a a-b b-a ←∨
revUpdInd (b ←∨) (∨→ a) a-b b-a = ∨→ a
revUpdInd (∨→ b) ↓ refl ()
revUpdInd (∨→ b) (a ←∨) a-b b-a = a ←∨
revUpdInd (∨→ b) (∨→ a) a-b b-a = ∨→ revUpdInd b a a-b b-a
revUpdInd (b ←∂) ↓ refl ()
revUpdInd (b ←∂) (a ←∂) a-b b-a = revUpdInd b a a-b b-a ←∂
revUpdInd (b ←∂) (∂→ a) a-b b-a = ∂→ a
revUpdInd (∂→ b) ↓ refl ()
revUpdInd (∂→ b) (a ←∂) a-b b-a = a ←∂
revUpdInd (∂→ b) (∂→ a) a-b b-a = ∂→ revUpdInd b a a-b b-a


-- Deprecated
updIndPart : ∀{i u ll cll ell pll} → (b : IndexLL pll ll) → (a : IndexLL {i} {u} cll ll)
             → a -ₘᵢ b ≡ nothing → b -ₘᵢ a ≡ nothing → IndexLL cll (replLL ll b ell)
updIndPart ↓ a () eq2
updIndPart (b ←∧) ↓ refl ()
updIndPart (b ←∧) (a ←∧) eq1 eq2 = updIndPart b a eq1 eq2 ←∧
updIndPart (b ←∧) (∧→ a) eq1 eq2 = ∧→ a
updIndPart (∧→ b) ↓ refl ()
updIndPart (∧→ b) (a ←∧) eq1 eq2 = a ←∧
updIndPart (∧→ b) (∧→ a) eq1 eq2 = ∧→ updIndPart b a eq1 eq2
updIndPart (b ←∨) ↓ refl ()
updIndPart (b ←∨) (a ←∨) eq1 eq2 = updIndPart b a eq1 eq2 ←∨
updIndPart (b ←∨) (∨→ a) eq1 eq2 = ∨→ a
updIndPart (∨→ b) ↓ refl ()
updIndPart (∨→ b) (a ←∨) eq1 eq2 = a ←∨
updIndPart (∨→ b) (∨→ a) eq1 eq2 = ∨→ updIndPart b a eq1 eq2
updIndPart (b ←∂) ↓ refl ()
updIndPart (b ←∂) (a ←∂) eq1 eq2 = updIndPart b a eq1 eq2 ←∂
updIndPart (b ←∂) (∂→ a) eq1 eq2 = ∂→ a
updIndPart (∂→ b) ↓ refl ()
updIndPart (∂→ b) (a ←∂) eq1 eq2 = a ←∂
updIndPart (∂→ b) (∂→ a) eq1 eq2 = ∂→ updIndPart b a eq1 eq2

-- Deprecated
rev⇒rs-i≡n : ∀{i u ll cll ell pll} → (ind : IndexLL pll ll)
             → (lind : IndexLL {i} {u} cll (replLL ll ind ell))
             → (eq₁ : (lind -ₘᵢ (updInd ell ind) ≡ nothing))
             → (eq₂ : ((updInd ell ind) -ₘᵢ lind ≡ nothing))
             → let rs = revUpdInd ind lind eq₁ eq₂ in
                 ((rs -ₘᵢ ind) ≡ nothing) × ((ind -ₘᵢ rs) ≡ nothing)
rev⇒rs-i≡n ↓ lind () eq2
rev⇒rs-i≡n (ind ←∧) ↓ eq1 ()
rev⇒rs-i≡n (ind ←∧) (lind ←∧) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
rev⇒rs-i≡n (ind ←∧) (∧→ lind) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∧→ ind) ↓ eq1 ()
rev⇒rs-i≡n (∧→ ind) (lind ←∧) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∧→ ind) (∧→ lind) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
rev⇒rs-i≡n (ind ←∨) ↓ eq1 ()
rev⇒rs-i≡n (ind ←∨) (lind ←∨) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
rev⇒rs-i≡n (ind ←∨) (∨→ lind) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∨→ ind) ↓ eq1 ()
rev⇒rs-i≡n (∨→ ind) (lind ←∨) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∨→ ind) (∨→ lind) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
rev⇒rs-i≡n (ind ←∂) ↓ eq1 ()
rev⇒rs-i≡n (ind ←∂) (lind ←∂) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
rev⇒rs-i≡n (ind ←∂) (∂→ lind) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∂→ ind) ↓ eq1 ()
rev⇒rs-i≡n (∂→ ind) (lind ←∂) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∂→ ind) (∂→ lind) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2




-- Deprecated
remRepl : ∀{i u ll frll ell pll cll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll)
          → replLL (replLL ll (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell ≡ replLL ll ind ell
remRepl ↓ lind = refl
remRepl {ll = li ∧ ri} {frll = frll} {ell = ell} (ind ←∧) lind
        with (replLL (replLL li (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
        | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∧ ri} {frll} {ell} (ind ←∧) lind | .(replLL li ind ell) | refl = refl
remRepl {ll = li ∧ ri} {frll = frll} {ell = ell} (∧→ ind) lind
        with (replLL (replLL ri (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
        | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∧ ri} {frll} {ell} (∧→ ind) lind | .(replLL ri ind ell) | refl = refl
remRepl {ll = li ∨ ri} {frll = frll} {ell = ell} (ind ←∨) lind
        with (replLL (replLL li (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
        | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∨ ri} {frll} {ell} (ind ←∨) lind | .(replLL li ind ell) | refl = refl
remRepl {ll = li ∨ ri} {frll = frll} {ell = ell} (∨→ ind) lind
        with (replLL (replLL ri (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
        | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∨ ri} {frll} {ell} (∨→ ind) lind | .(replLL ri ind ell) | refl = refl
remRepl {ll = li ∂ ri} {frll = frll} {ell = ell} (ind ←∂) lind
        with (replLL (replLL li (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
        | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∂ ri} {frll} {ell} (ind ←∂) lind | .(replLL li ind ell) | refl = refl
remRepl {ll = li ∂ ri} {frll = frll} {ell = ell} (∂→ ind) lind
        with (replLL (replLL ri (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
        | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∂ ri} {frll} {ell} (∂→ ind) lind | .(replLL ri ind ell) | refl = refl

-- Deprecated
replLL-inv : ∀{i u ll ell pll} → (ind : IndexLL {i} {u} pll ll)
             → replLL (replLL ll ind ell) (updInd ell ind) pll ≡ ll
replLL-inv ↓ = refl
replLL-inv {ll = li ∧ ri} {ell = ell} {pll = pll} (ind ←∧)
           with (replLL (replLL li ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∧ ri} {ell} {pll} (ind ←∧) | .li | refl = refl
replLL-inv {ll = li ∧ ri} {ell = ell} {pll = pll} (∧→ ind)
           with (replLL (replLL ri ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∧ ri} {ell} {pll} (∧→ ind) | .ri | refl = refl
replLL-inv {ll = li ∨ ri} {ell = ell} {pll = pll} (ind ←∨)
           with (replLL (replLL li ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∨ ri} {ell} {pll} (ind ←∨) | .li | refl = refl
replLL-inv {ll = li ∨ ri} {ell = ell} {pll = pll} (∨→ ind)
           with (replLL (replLL ri ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∨ ri} {ell} {pll} (∨→ ind) | .ri | refl = refl
replLL-inv {ll = li ∂ ri} {ell = ell} {pll = pll} (ind ←∂)
           with (replLL (replLL li ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∂ ri} {ell} {pll} (ind ←∂) | .li | refl = refl
replLL-inv {ll = li ∂ ri} {ell = ell} {pll = pll} (∂→ ind)
           with (replLL (replLL ri ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∂ ri} {ell} {pll} (∂→ ind) | .ri | refl = refl


