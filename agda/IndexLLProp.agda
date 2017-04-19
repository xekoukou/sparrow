{-# OPTIONS --exact-split #-}
module IndexLLProp where

open import Common
open import LinLogic
open import Data.Maybe
open import Data.Product




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

data Orderedᵢ {i u gll fll ll} (a : IndexLL {i} {u} gll ll) (b : IndexLL {i} {u} fll ll) : Set where
  a≤ᵢb : a ≤ᵢ b → Orderedᵢ a b
  b≤ᵢa : b ≤ᵢ a → Orderedᵢ a b

flipOrdᵢ : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
           → Orderedᵢ a b → Orderedᵢ b a
flipOrdᵢ (a≤ᵢb x) = b≤ᵢa x
flipOrdᵢ (b≤ᵢa x) = a≤ᵢb x

flipNotOrdᵢ : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
              → ¬ Orderedᵢ a b → ¬ Orderedᵢ b a
flipNotOrdᵢ nord = λ x → nord (flipOrdᵢ x) 




_-ᵢ_ : ∀ {i u pll cll ll} → (bind : IndexLL {i} {u} cll ll) → (sind : IndexLL pll ll) → (sind ≤ᵢ bind)
       → IndexLL cll pll
(bind -ᵢ .↓) ≤ᵢ↓ = bind
((bind ←∧) -ᵢ (sind ←∧)) (≤ᵢ←∧ eq) = (bind -ᵢ sind) eq
((∧→ bind) -ᵢ (∧→ sind)) (≤ᵢ∧→ eq) = (bind -ᵢ sind) eq
((bind ←∨) -ᵢ (sind ←∨)) (≤ᵢ←∨ eq) = (bind -ᵢ sind) eq
((∨→ bind) -ᵢ (∨→ sind)) (≤ᵢ∨→ eq) = (bind -ᵢ sind) eq
((bind ←∂) -ᵢ (sind ←∂)) (≤ᵢ←∂ eq) = (bind -ᵢ sind) eq
((∂→ bind) -ᵢ (∂→ sind)) (≤ᵢ∂→ eq) = (bind -ᵢ sind) eq


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
             → (ind : IndexLL rll ll) → ∀ frll → .(nord : ¬ Orderedᵢ ind emi)
             → IndexLL fll (replLL ll ind frll)
¬ord-morph ↓ ind frll nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
¬ord-morph (emi ←∧) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓)) 
¬ord-morph (emi ←∧) (ind ←∧) frll nord
           with (¬ord-morph emi ind frll
             (λ { (a≤ᵢb lt) → nord (a≤ᵢb (≤ᵢ←∧ lt))
                ; (b≤ᵢa lt) → nord (b≤ᵢa (≤ᵢ←∧ lt))
                }))
... | r = r ←∧
¬ord-morph (emi ←∧) (∧→ ind) frll nord = emi ←∧
¬ord-morph (∧→ emi) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
¬ord-morph (∧→ emi) (ind ←∧) frll nord = ∧→ emi
¬ord-morph (∧→ emi) (∧→ ind) frll nord
           with (¬ord-morph emi ind frll
             (λ { (a≤ᵢb lt) → nord (a≤ᵢb (≤ᵢ∧→ lt))
                ; (b≤ᵢa lt) → nord (b≤ᵢa (≤ᵢ∧→ lt))
                }))
... | r = ∧→ r
¬ord-morph (emi ←∨) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓)) 
¬ord-morph (emi ←∨) (ind ←∨) frll nord
           with (¬ord-morph emi ind frll
             (λ { (a≤ᵢb lt) → nord (a≤ᵢb (≤ᵢ←∨ lt))
                ; (b≤ᵢa lt) → nord (b≤ᵢa (≤ᵢ←∨ lt))
                }))
... | r = r ←∨
¬ord-morph (emi ←∨) (∨→ ind) frll nord = emi ←∨
¬ord-morph (∨→ emi) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
¬ord-morph (∨→ emi) (ind ←∨) frll nord = ∨→ emi
¬ord-morph (∨→ emi) (∨→ ind) frll nord
           with (¬ord-morph emi ind frll
             (λ { (a≤ᵢb lt) → nord (a≤ᵢb (≤ᵢ∨→ lt))
                ; (b≤ᵢa lt) → nord (b≤ᵢa (≤ᵢ∨→ lt))
                }))
... | r = ∨→ r
¬ord-morph (emi ←∂) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓) )
¬ord-morph (emi ←∂) (ind ←∂) frll nord
           with (¬ord-morph emi ind frll
             (λ { (a≤ᵢb lt) → nord (a≤ᵢb (≤ᵢ←∂ lt))
                ; (b≤ᵢa lt) → nord (b≤ᵢa (≤ᵢ←∂ lt))
                }))
... | r = r ←∂
¬ord-morph (emi ←∂) (∂→ ind) frll nord = emi ←∂
¬ord-morph (∂→ emi) ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
¬ord-morph (∂→ emi) (ind ←∂) frll nord = ∂→ emi
¬ord-morph (∂→ emi) (∂→ ind) frll nord
           with (¬ord-morph emi ind frll
             (λ { (a≤ᵢb lt) → nord (a≤ᵢb (≤ᵢ∂→ lt))
                ; (b≤ᵢa lt) → nord (b≤ᵢa (≤ᵢ∂→ lt))
                }))
... | r = ∂→ r

module _ where

  replLL-¬ordab≡ba : ∀{i u rll ll fll}
    → (emi : IndexLL {i} {u} fll ll) → ∀ gll
    → (ind : IndexLL rll ll) → ∀ frll
    → .(nord : ¬ Orderedᵢ ind emi)
    → replLL (replLL ll ind frll) (¬ord-morph emi ind frll nord) gll ≡ replLL (replLL ll emi gll) (¬ord-morph ind emi gll (flipNotOrdᵢ nord)) frll
  replLL-¬ordab≡ba ↓ gll ind frll nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
  replLL-¬ordab≡ba (emi ←∧) gll ↓ frll nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
  replLL-¬ordab≡ba {ll = li ∧ ri} (emi ←∧) gll (ind ←∧) frll nord
    with (replLL (replLL li ind frll) (¬ord-morph emi ind frll hf) gll)
    | replLL-¬ordab≡ba emi gll ind frll hf where
      .hf : (¬ Orderedᵢ ind emi)
      hf = (λ { (a≤ᵢb x) → nord (a≤ᵢb (≤ᵢ←∧ x))
              ; (b≤ᵢa x) → nord (b≤ᵢa (≤ᵢ←∧ x))})
  ... | g | r = {!!}
  replLL-¬ordab≡ba (emi ←∧) gll (∧→ ind) frll nord = {!!}
  replLL-¬ordab≡ba (∧→ emi) gll ind frll nord = {!!}
  replLL-¬ordab≡ba (emi ←∨) gll ind frll nord = {!!}
  replLL-¬ordab≡ba (∨→ emi) gll ind frll nord = {!!}
  replLL-¬ordab≡ba (emi ←∂) gll ind frll nord = {!!}
  replLL-¬ordab≡ba (∂→ emi) gll ind frll nord = {!!}
   

--flipOrdᵢ (a≤ᵢb x) = b≤ᵢa x
--flipOrdᵢ (b≤ᵢa x) = a≤ᵢb x

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



-- A predicate that is true if pll is not transformed by pll.

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
  ∧→[←∧∧∧d : ∀{pll lli lri rri rli rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} (∧→ (∧→ (ind ←∧))) ltr
            → UpTran {ll = (lli ∧ lri) ∧ (rli ∧ rri)} (∧→ (ind ←∧)) (∧∧d ltr)
  ∧→[∧→∧∧d : ∀{pll lli lri rri rli rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∧→ (∧→ (∧→ ind))) ltr
            → UpTran {ll = (lli ∧ lri) ∧ (rli ∧ rri)} (∧→ (∧→ ind)) (∧∧d ltr)
  ∧→[←∨∧∧d : ∀{pll lli lri rri rli rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} (∧→ (∧→ (ind ←∨))) ltr
            → UpTran {ll = (lli ∧ lri) ∧ (rli ∨ rri)} (∧→ (ind ←∨)) (∧∧d ltr)
  ∧→[∨→∧∧d : ∀{pll lli lri rri rli rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∧→ (∧→ (∨→ ind))) ltr
            → UpTran {ll = (lli ∧ lri) ∧ (rli ∨ rri)} (∧→ (∨→ ind)) (∧∧d ltr)
  ∧→[←∂∧∧d : ∀{pll lli lri rri rli rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} (∧→ (∧→ (ind ←∂))) ltr
            → UpTran {ll = (lli ∧ lri) ∧ (rli ∂ rri)} (∧→ (ind ←∂)) (∧∧d ltr)
  ∧→[∂→∧∧d : ∀{pll lli lri rri rli rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∧→ (∧→ (∂→ ind))) ltr
            → UpTran {ll = (lli ∧ lri) ∧ (rli ∂ rri)} (∧→ (∂→ ind)) (∧∧d ltr)
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
  ∨→[←∧∨∨d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} (∨→ (∨→ (ind ←∧))) ltr
            → UpTran {ll = (lli ∨ lri) ∨ (rli ∧ rri)} (∨→ (ind ←∧)) (∨∨d ltr)
  ∨→[∧→∨∨d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∨→ (∨→ (∧→ ind))) ltr
            → UpTran {ll = (lli ∨ lri) ∨ (rli ∧ rri)} (∨→ (∧→ ind)) (∨∨d ltr)
  ∨→[←∨∨∨d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} (∨→ (∨→ (ind ←∨))) ltr
            → UpTran {ll = (lli ∨ lri) ∨ (rli ∨ rri)} (∨→ (ind ←∨)) (∨∨d ltr)
  ∨→[∨→∨∨d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∨→ (∨→ (∨→ ind))) ltr
            → UpTran {ll = (lli ∨ lri) ∨ (rli ∨ rri)} (∨→ (∨→ ind)) (∨∨d ltr)
  ∨→[←∂∨∨d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} (∨→ (∨→ (ind ←∂))) ltr
            → UpTran {ll = (lli ∨ lri) ∨ (rli ∂ rri)} (∨→ (ind ←∂)) (∨∨d ltr)
  ∨→[∂→∨∨d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∨→ (∨→ (∂→ ind))) ltr
            → UpTran {ll = (lli ∨ lri) ∨ (rli ∂ rri)} (∨→ (∂→ ind)) (∨∨d ltr)
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
  ∂→[←∧∂∂d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} (∂→ (∂→ (ind ←∧))) ltr
            → UpTran {ll = (lli ∂ lri) ∂ (rli ∧ rri)} (∂→ (ind ←∧)) (∂∂d ltr)
  ∂→[∧→∂∂d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∂→ (∂→ (∧→ ind))) ltr
            → UpTran {ll = (lli ∂ lri) ∂ (rli ∧ rri)} (∂→ (∧→ ind)) (∂∂d ltr)
  ∂→[←∨∂∂d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} (∂→ (∂→ (ind ←∨))) ltr
            → UpTran {ll = (lli ∂ lri) ∂ (rli ∨ rri)} (∂→ (ind ←∨)) (∂∂d ltr)
  ∂→[∨→∂∂d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∂→ (∂→ (∨→ ind))) ltr
            → UpTran {ll = (lli ∂ lri) ∂ (rli ∨ rri)} (∂→ (∨→ ind)) (∂∂d ltr)
  ∂→[←∂∂∂d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rli}
            → UpTran {rll = rll} (∂→ (∂→ (ind ←∂))) ltr
            → UpTran {ll = (lli ∂ lri) ∂ (rli ∂ rri)} (∂→ (ind ←∂)) (∂∂d ltr)
  ∂→[∂→∂∂d : ∀{pll lli lri rli rri rll ltr} → {ind : IndexLL pll rri}
            → UpTran {rll = rll} (∂→ (∂→ (∂→ ind))) ltr
            → UpTran {ll = (lli ∂ lri) ∂ (rli ∂ rri)} (∂→ (∂→ ind)) (∂∂d ltr)
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
isUpTran (∧→ ↓) (∧∧d ltr) = no (λ ())
isUpTran (∧→ (ind ←∧)) (∧∧d ltr) with (isUpTran (∧→ (∧→ (ind ←∧))) ltr)
isUpTran (∧→ (ind ←∧)) (∧∧d ltr) | yes p = yes (∧→[←∧∧∧d p)
isUpTran (∧→ (ind ←∧)) (∧∧d ltr) | no ¬p =  no (λ {(∧→[←∧∧∧d ut) → ¬p ut})
isUpTran (∧→ (∧→ ind)) (∧∧d ltr) with (isUpTran (∧→ (∧→ (∧→ ind))) ltr)
isUpTran (∧→ (∧→ ind)) (∧∧d ltr) | yes p = yes (∧→[∧→∧∧d p)
isUpTran (∧→ (∧→ ind)) (∧∧d ltr) | no ¬p =  no (λ {(∧→[∧→∧∧d ut) → ¬p ut})
isUpTran (∧→ (ind ←∨)) (∧∧d ltr) with (isUpTran (∧→ (∧→ (ind ←∨))) ltr)
isUpTran (∧→ (ind ←∨)) (∧∧d ltr) | yes p = yes (∧→[←∨∧∧d p)
isUpTran (∧→ (ind ←∨)) (∧∧d ltr) | no ¬p =  no (λ {(∧→[←∨∧∧d ut) → ¬p ut})
isUpTran (∧→ (∨→ ind)) (∧∧d ltr) with (isUpTran (∧→ (∧→ (∨→ ind))) ltr)
isUpTran (∧→ (∨→ ind)) (∧∧d ltr) | yes p = yes (∧→[∨→∧∧d p)
isUpTran (∧→ (∨→ ind)) (∧∧d ltr) | no ¬p =  no (λ {(∧→[∨→∧∧d ut) → ¬p ut})
isUpTran (∧→ (ind ←∂)) (∧∧d ltr) with (isUpTran (∧→ (∧→ (ind ←∂))) ltr)
isUpTran (∧→ (ind ←∂)) (∧∧d ltr) | yes p = yes (∧→[←∂∧∧d p)
isUpTran (∧→ (ind ←∂)) (∧∧d ltr) | no ¬p =  no (λ {(∧→[←∂∧∧d ut) → ¬p ut})
isUpTran (∧→ (∂→ ind)) (∧∧d ltr) with (isUpTran (∧→ (∧→ (∂→ ind))) ltr)
isUpTran (∧→ (∂→ ind)) (∧∧d ltr) | yes p = yes (∧→[∂→∧∧d p)
isUpTran (∧→ (∂→ ind)) (∧∧d ltr) | no ¬p =  no (λ {(∧→[∂→∧∧d ut) → ¬p ut})
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
isUpTran (∨→ ↓) (∨∨d ltr) = no (λ ())
isUpTran (∨→ (ind ←∧)) (∨∨d ltr) with (isUpTran (∨→ (∨→ (ind ←∧))) ltr)
isUpTran (∨→ (ind ←∧)) (∨∨d ltr) | yes p = yes (∨→[←∧∨∨d p)
isUpTran (∨→ (ind ←∧)) (∨∨d ltr) | no ¬p =  no (λ {(∨→[←∧∨∨d ut) → ¬p ut})
isUpTran (∨→ (∧→ ind)) (∨∨d ltr) with (isUpTran (∨→ (∨→ (∧→ ind))) ltr)
isUpTran (∨→ (∧→ ind)) (∨∨d ltr) | yes p = yes (∨→[∧→∨∨d p)
isUpTran (∨→ (∧→ ind)) (∨∨d ltr) | no ¬p =  no (λ {(∨→[∧→∨∨d ut) → ¬p ut})
isUpTran (∨→ (ind ←∨)) (∨∨d ltr) with (isUpTran (∨→ (∨→ (ind ←∨))) ltr)
isUpTran (∨→ (ind ←∨)) (∨∨d ltr) | yes p = yes (∨→[←∨∨∨d p)
isUpTran (∨→ (ind ←∨)) (∨∨d ltr) | no ¬p =  no (λ {(∨→[←∨∨∨d ut) → ¬p ut})
isUpTran (∨→ (∨→ ind)) (∨∨d ltr) with (isUpTran (∨→ (∨→ (∨→ ind))) ltr)
isUpTran (∨→ (∨→ ind)) (∨∨d ltr) | yes p = yes (∨→[∨→∨∨d p)
isUpTran (∨→ (∨→ ind)) (∨∨d ltr) | no ¬p =  no (λ {(∨→[∨→∨∨d ut) → ¬p ut})
isUpTran (∨→ (ind ←∂)) (∨∨d ltr) with (isUpTran (∨→ (∨→ (ind ←∂))) ltr)
isUpTran (∨→ (ind ←∂)) (∨∨d ltr) | yes p = yes (∨→[←∂∨∨d p)
isUpTran (∨→ (ind ←∂)) (∨∨d ltr) | no ¬p =  no (λ {(∨→[←∂∨∨d ut) → ¬p ut})
isUpTran (∨→ (∂→ ind)) (∨∨d ltr) with (isUpTran (∨→ (∨→ (∂→ ind))) ltr)
isUpTran (∨→ (∂→ ind)) (∨∨d ltr) | yes p = yes (∨→[∂→∨∨d p)
isUpTran (∨→ (∂→ ind)) (∨∨d ltr) | no ¬p =  no (λ {(∨→[∂→∨∨d ut) → ¬p ut})
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
isUpTran (∂→ ↓) (∂∂d ltr) = no (λ ())
isUpTran (∂→ (ind ←∧)) (∂∂d ltr) with (isUpTran (∂→ (∂→ (ind ←∧))) ltr)
isUpTran (∂→ (ind ←∧)) (∂∂d ltr) | yes p = yes (∂→[←∧∂∂d p)
isUpTran (∂→ (ind ←∧)) (∂∂d ltr) | no ¬p =  no (λ {(∂→[←∧∂∂d ut) → ¬p ut})
isUpTran (∂→ (∧→ ind)) (∂∂d ltr) with (isUpTran (∂→ (∂→ (∧→ ind))) ltr)
isUpTran (∂→ (∧→ ind)) (∂∂d ltr) | yes p = yes (∂→[∧→∂∂d p)
isUpTran (∂→ (∧→ ind)) (∂∂d ltr) | no ¬p =  no (λ {(∂→[∧→∂∂d ut) → ¬p ut})
isUpTran (∂→ (ind ←∨)) (∂∂d ltr) with (isUpTran (∂→ (∂→ (ind ←∨))) ltr)
isUpTran (∂→ (ind ←∨)) (∂∂d ltr) | yes p = yes (∂→[←∨∂∂d p)
isUpTran (∂→ (ind ←∨)) (∂∂d ltr) | no ¬p =  no (λ {(∂→[←∨∂∂d ut) → ¬p ut})
isUpTran (∂→ (∨→ ind)) (∂∂d ltr) with (isUpTran (∂→ (∂→ (∨→ ind))) ltr)
isUpTran (∂→ (∨→ ind)) (∂∂d ltr) | yes p = yes (∂→[∨→∂∂d p)
isUpTran (∂→ (∨→ ind)) (∂∂d ltr) | no ¬p =  no (λ {(∂→[∨→∂∂d ut) → ¬p ut})
isUpTran (∂→ (ind ←∂)) (∂∂d ltr) with (isUpTran (∂→ (∂→ (ind ←∂))) ltr)
isUpTran (∂→ (ind ←∂)) (∂∂d ltr) | yes p = yes (∂→[←∂∂∂d p)
isUpTran (∂→ (ind ←∂)) (∂∂d ltr) | no ¬p =  no (λ {(∂→[←∂∂∂d ut) → ¬p ut})
isUpTran (∂→ (∂→ ind)) (∂∂d ltr) with (isUpTran (∂→ (∂→ (∂→ ind))) ltr)
isUpTran (∂→ (∂→ ind)) (∂∂d ltr) | yes p = yes (∂→[∂→∂∂d p)
isUpTran (∂→ (∂→ ind)) (∂∂d ltr) | no ¬p =  no (λ {(∂→[∂→∂∂d ut) → ¬p ut})
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
tran (∧→ ↓) (∧∧d ltr) ()
tran (∧→ (ind ←∧)) (∧∧d ltr) (∧→[←∧∧∧d ut) = tran (∧→ (∧→ (ind ←∧))) ltr ut
tran (∧→ (∧→ ind)) (∧∧d ltr) (∧→[∧→∧∧d ut) = tran (∧→ (∧→ (∧→ ind))) ltr ut
tran (∧→ (ind ←∨)) (∧∧d ltr) (∧→[←∨∧∧d ut) = tran (∧→ (∧→ (ind ←∨))) ltr ut
tran (∧→ (∨→ ind)) (∧∧d ltr) (∧→[∨→∧∧d ut) = tran (∧→ (∧→ (∨→ ind))) ltr ut
tran (∧→ (ind ←∂)) (∧∧d ltr) (∧→[←∂∧∧d ut) = tran (∧→ (∧→ (ind ←∂))) ltr ut
tran (∧→ (∂→ ind)) (∧∧d ltr) (∧→[∂→∧∧d ut) = tran (∧→ (∧→ (∂→ ind))) ltr ut
tran ↓ (¬∧∧d ltr) () 
tran (ind ←∧) (¬∧∧d ltr) (←∧¬∧∧d ut) = tran ((ind ←∧) ←∧) ltr ut
tran (∧→ ↓) (¬∧∧d ltr) () 
tran (∧→ (ind ←∧)) (¬∧∧d ltr) (∧→[←∧¬∧∧d ut) = tran ((∧→ ind) ←∧) ltr ut
tran (∧→ (∧→ ind)) (¬∧∧d ltr) (∧→[∧→¬∧∧d ut) = tran (∧→ ind) ltr ut
tran ↓ (∨∨d ltr) () 
tran (↓ ←∨) (∨∨d ltr) () 
tran ((ind ←∨) ←∨) (∨∨d ltr) (←∨]←∨∨∨d ut) = tran (ind ←∨) ltr ut
tran ((∨→ ind) ←∨) (∨∨d ltr) (∨→]←∨∨∨d ut) = tran (∨→ (ind ←∨)) ltr ut
tran (∨→ ↓) (∨∨d ltr) ()
tran (∨→ (ind ←∧)) (∨∨d ltr) (∨→[←∧∨∨d ut) = tran (∨→ (∨→ (ind ←∧))) ltr ut
tran (∨→ (∧→ ind)) (∨∨d ltr) (∨→[∧→∨∨d ut) = tran (∨→ (∨→ (∧→ ind))) ltr ut
tran (∨→ (ind ←∨)) (∨∨d ltr) (∨→[←∨∨∨d ut) = tran (∨→ (∨→ (ind ←∨))) ltr ut
tran (∨→ (∨→ ind)) (∨∨d ltr) (∨→[∨→∨∨d ut) = tran (∨→ (∨→ (∨→ ind))) ltr ut
tran (∨→ (ind ←∂)) (∨∨d ltr) (∨→[←∂∨∨d ut) = tran (∨→ (∨→ (ind ←∂))) ltr ut
tran (∨→ (∂→ ind)) (∨∨d ltr) (∨→[∂→∨∨d ut) = tran (∨→ (∨→ (∂→ ind))) ltr ut
tran ↓ (¬∨∨d ltr) () 
tran (ind ←∨) (¬∨∨d ltr) (←∨¬∨∨d ut) = tran ((ind ←∨) ←∨) ltr ut
tran (∨→ ↓) (¬∨∨d ltr) () 
tran (∨→ (ind ←∨)) (¬∨∨d ltr) (∨→[←∨¬∨∨d ut) = tran ((∨→ ind) ←∨) ltr ut
tran (∨→ (∨→ ind)) (¬∨∨d ltr) (∨→[∨→¬∨∨d ut) = tran (∨→ ind) ltr ut
tran ↓ (∂∂d ltr) () 
tran (↓ ←∂) (∂∂d ltr) () 
tran ((ind ←∂) ←∂) (∂∂d ltr) (←∂]←∂∂∂d ut) = tran (ind ←∂) ltr ut
tran ((∂→ ind) ←∂) (∂∂d ltr) (∂→]←∂∂∂d ut) = tran (∂→ (ind ←∂)) ltr ut
tran (∂→ ↓) (∂∂d ltr) ()
tran (∂→ (ind ←∧)) (∂∂d ltr) (∂→[←∧∂∂d ut) = tran (∂→ (∂→ (ind ←∧))) ltr ut
tran (∂→ (∧→ ind)) (∂∂d ltr) (∂→[∧→∂∂d ut) = tran (∂→ (∂→ (∧→ ind))) ltr ut
tran (∂→ (ind ←∨)) (∂∂d ltr) (∂→[←∨∂∂d ut) = tran (∂→ (∂→ (ind ←∨))) ltr ut
tran (∂→ (∨→ ind)) (∂∂d ltr) (∂→[∨→∂∂d ut) = tran (∂→ (∂→ (∨→ ind))) ltr ut
tran (∂→ (ind ←∂)) (∂∂d ltr) (∂→[←∂∂∂d ut) = tran (∂→ (∂→ (ind ←∂))) ltr ut
tran (∂→ (∂→ ind)) (∂∂d ltr) (∂→[∂→∂∂d ut) = tran (∂→ (∂→ (∂→ ind))) ltr ut
tran ↓ (¬∂∂d ltr) () 
tran (ind ←∂) (¬∂∂d ltr) (←∂¬∂∂d ut) = tran ((ind ←∂) ←∂) ltr ut
tran (∂→ ↓) (¬∂∂d ltr) () 
tran (∂→ (ind ←∂)) (¬∂∂d ltr) (∂→[←∂¬∂∂d ut) = tran ((∂→ ind) ←∂) ltr ut
tran (∂→ (∂→ ind)) (¬∂∂d ltr) (∂→[∂→¬∂∂d ut) = tran (∂→ ind) ltr ut


updInd : ∀{i u rll ll} → ∀ nrll → (ind : IndexLL {i} {u} rll ll)
         → IndexLL {i} {u} nrll (replLL ll ind nrll)
updInd nrll ↓ = ↓
updInd nrll (ind ←∧) = (updInd nrll ind) ←∧
updInd nrll (∧→ ind) = ∧→ (updInd nrll ind)
updInd nrll (ind ←∨) = (updInd nrll ind) ←∨
updInd nrll (∨→ ind) = ∨→ (updInd nrll ind)
updInd nrll (ind ←∂) = (updInd nrll ind) ←∂
updInd nrll (∂→ ind) = ∂→ (updInd nrll ind)

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

