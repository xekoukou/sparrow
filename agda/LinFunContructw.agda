module LinFunContructw where

open import Common
open import LinLogic
open import IndexLLProp
open import LinFun
open import SetLL
open import SetLLProp

open import Relation.Binary.PropositionalEquality
open import Data.Product

open import LinFunContruct

ext⇒¬ho : ∀{i u pll rll ll} → ∀ s → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL rll ll)
          → ¬ Orderedᵢ lind ind → ¬ hitsAtLeastOnce (extend ind s) lind
ext⇒¬ho s ↓ lind ¬ord x = ¬ord (b≤ᵢa ≤ᵢ↓)
ext⇒¬ho s (ind ←∧) ↓ ¬ord x = ¬ord (a≤ᵢb ≤ᵢ↓)
ext⇒¬ho {pll = pll} {_} {ll = li ∧ _} s (ind ←∧) (lind ←∧) ¬ord
      with replLL li ind pll | replLL-id li ind pll refl | extendg ind s | ext⇒¬ho s ind lind hf where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x₁) = ¬ord (a≤ᵢb (≤ᵢ←∧ x₁))
  hf (b≤ᵢa x₁) = ¬ord (b≤ᵢa (≤ᵢ←∧ x₁))
ext⇒¬ho {pll = pll} {_} {li ∧ _} s (ind ←∧) (lind ←∧) ¬ord | .li | refl | t | e = {!!} where
  hf : ¬ hitsAtLeastOnce (t ←∧) (lind ←∧)
  hf (hitsAtLeastOnce←∧←∧ x) = {!!}
ext⇒¬ho {pll = pll} {_} {ll = li ∧ _} s (ind ←∧) (∧→ lind) ¬ord x with replLL li ind pll | replLL-id li ind pll refl | extendg ind s
ext⇒¬ho {_} {_} {pll} {_} {li ∧ _} s (ind ←∧) (∧→ lind) ¬ord () | .li | refl | t
ext⇒¬ho s (∧→ ind) ↓ ¬ord x = ¬ord (a≤ᵢb ≤ᵢ↓)
ext⇒¬ho s (∧→ ind) (lind ←∧) ¬ord x = {!!}
ext⇒¬ho s (∧→ ind) (∧→ lind) ¬ord x = {!!}
ext⇒¬ho s (ind ←∨) lind ¬ord x = {!!}
ext⇒¬ho s (∨→ ind) lind ¬ord x = {!!}
ext⇒¬ho s (ind ←∂) lind ¬ord x = {!!}
ext⇒¬ho s (∂→ ind) lind ¬ord x = {!!}

goo : ∀{i u rll pll ll tll} → (lind : IndexLL {i} {u} rll ll) → (s : SetLL ll) → ∀{rs : SetLL tll}
      → ¬ (hitsAtLeastOnce s lind) → (ind : IndexLL pll ll)
      → (nord : ¬ Orderedᵢ lind ind)
      → ¬ (hitsAtLeastOnce (replacePartOf s to rs at ind) (¬ord-morph lind ind tll (flipNotOrdᵢ nord)))
goo ↓ s ¬ho ind ¬ord = λ _ → ¬ord (a≤ᵢb ≤ᵢ↓)
goo (lind ←∧) ↓ ¬ho ind ¬ord = λ _ → ¬ho hitsAtLeastOnce↓
goo (lind ←∧) (s ←∧) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
goo (lind ←∧) (s ←∧) {rs} ¬ho (ind ←∧) ¬ord x
                                 with goo lind s {rs} (λ z → ¬ho (hitsAtLeastOnce←∧←∧ z)) ind hf where
  hf : ¬ Orderedᵢ lind ind
  hf (a≤ᵢb x) = ¬ord (a≤ᵢb (≤ᵢ←∧ x))
  hf (b≤ᵢa x) = ¬ord (b≤ᵢa (≤ᵢ←∧ x))
goo (lind ←∧) (s ←∧) {rs} ¬ho (ind ←∧) ¬ord (hitsAtLeastOnce←∧←∧ x) | r = ⊥-elim (r x)
goo (lind ←∧) (s ←∧) ¬ho (∧→ ind) ¬ord (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ x)
goo (lind ←∧) (∧→ s) ¬ho ↓ ¬ord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
goo (lind ←∧) (∧→ s) ¬ho (ind ←∧) ¬ord = {!!}
goo (lind ←∧) (∧→ s) ¬ho (∧→ ind) ¬ord = λ ()
goo (lind ←∧) (s ←∧→ s₁) ¬ho ind ¬ord = {!!}
goo (∧→ lind) s ¬ho ind ¬ord = {!!}
goo (lind ←∨) s ¬ho ind ¬ord = {!!}
goo (∨→ lind) s ¬ho ind ¬ord = {!!}
goo (lind ←∂) s ¬ho ind ¬ord = {!!}
goo (∂→ lind) s ¬ho ind ¬ord = {!!}




gest : ∀{i u rll ll n dt df tind ts} → (lf : LFun ll rll)
       → (ind : IndexLL (τ {i} {u} {n} {dt} df) ll) → (s : SetLL ll) → ¬ (hitsAtLeastOnce s ind)
       → ¬∅ tind ≡ tranLFMIndexLL lf (¬∅ ind) → ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)
       → ¬ (hitsAtLeastOnce ts tind) 
gest I ind s ¬ho refl refl = ¬ho
gest (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi eqs with isOrdᵢ lind ind
... | no ¬p = {!!} where
  is = gest lf {!!} {!!} -- (¬∅ (truncSetLL s ind))
... | yes p = {!!}
gest {tind = tind} {ts} (tr ltr lf) ind s ¬ho eqi eqs = gest lf (IndexLLProp.tran ind ltr ut) (SetLL.tran s ltr) ¬tho eqi eqs  where
  ut = indLow⇒UpTran ind ltr 
  ¬tho = ¬trho ltr s ind ¬ho ut
gest (com df₁ lf) ind s ¬ho () eqs
gest (call x) ind s ¬ho () eqs




module _ where

  

  private
    data M¬ho {i u ll n dt df} (s : SetLL ll) : MIndexLL (τ {i} {u} {n} {dt} df) ll → Set where
      ∅ : M¬ho s ∅
      ¬∅ : {ind : IndexLL (τ {i} {u} {n} {dt} df) ll} → (¬ho : ¬ (hitsAtLeastOnce s ind))
           → M¬ho s (¬∅ ind)

    hf : ∀{i u n dt df} → ∀ ll → ∀{cs} → (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll)
         → (s : SetLL ll) → (ceq : complLₛ s ≡ ¬∅ cs) → (m¬ho : M¬ho s ind) → LinLogic i {u}
         → LinLogic i {u}
    hf ll {cs} ∅ s ceq mnho cll = shrinkcms ll s cs ceq
    hf ll {cs} (¬∅ x) s ceq (¬∅ ¬ho) cll = replLL (shrinkcms ll s cs ceq) (¬ho-shr-morph s ceq x ¬ho) cll
-- (shrinkcms ll s cs ceqi)
  data MLFun {i u ll rll n dt df} (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll)
             (s : SetLL ll) (m¬ho : M¬ho s ind) (lf : LFun {i} {u} ll rll) : Set (lsuc u) where
    ∅ : MLFun ind s m¬ho lf
    ¬∅¬∅ : ∀ {cs ts cts} → (ceqi : complLₛ s ≡ ¬∅ cs)
           → let tind = tranLFMIndexLL lf ind in
           ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s) → (ceqo : complLₛ ts ≡ ¬∅ cts)
           → ((cll : LinLogic i {u}) → LFun (hf ll ind s ceqi m¬ho cll) (hf rll tind ts ceqo {!!} cll))
           → MLFun ind s m¬ho lf
           -- We will never reach to a point where complLₛ ts ≡ ∅ because
           -- the input would have the same fate. ( s becomes smaller as we go forward, thus complLₛ increases. Here we take the case where s is not ∅.
  
  
    -- s here does contain the ind.
  test : ∀{i u rll ll n dt df} → (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll) → (s : SetLL ll)
         → ∀ m¬ho → (lf : LFun ll rll) → MLFun ind s m¬ho lf
  test ind s lf = {!!}
  
  
  
  
  
  
  
