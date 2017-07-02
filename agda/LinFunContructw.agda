-- {-# OPTIONS --show-implicit #-}

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

too : {i : Size} {u : Level} (li : LinLogic i) {pll tll : LinLogic i} (lind : IndexLL {i} {u} pll li) (w : LinLogic i) (w₁ : IndexLL (replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll) w) (ri : LinLogic i) (r : Reveal del ↓ lind · tll is ∅) (y : hitsAtLeastOnce ((SetLL (w ∧ ri)) ∋ (∧→ ↓)) (w₁ ←∧)) → ⊥
too = {!!}

foo : ∀{i u pll ll tll} → (s : SetLL ll)
    → (lind : IndexLL {i} {u} pll ll) → ∀{ds}
    → ¬∅ ds ≡ del s lind tll
    → ¬ (hitsAtLeastOnce ds (a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)))
foo {tll = tll} s ↓ {ds} ()
foo {ll = li ∧ ri} {tll} ↓ (lind ←∧) {↓} eq with del ↓ lind tll
foo {pll = _} {li ∧ ri} {tll} ↓ (lind ←∧) {↓} () | ∅
foo {pll = _} {li ∧ ri} {tll} ↓ (lind ←∧) {↓} () | ¬∅ x
foo {ll = li ∧ ri} {tll} (s ←∧) (lind ←∧) {↓} eq with del s lind tll
foo {pll = _} {li ∧ ri} {tll} (s ←∧) (lind ←∧) {↓} () | ∅
foo {pll = _} {li ∧ ri} {tll} (s ←∧) (lind ←∧) {↓} () | ¬∅ x
foo {ll = li ∧ ri} {tll} (∧→ s) (lind ←∧) {↓} ()
foo {ll = li ∧ ri} {tll} (s ←∧→ s₁) (lind ←∧) {↓} eq with del s lind tll
foo {pll = _} {li ∧ ri} {tll} (s ←∧→ s₁) (lind ←∧) {↓} () | ∅
foo {pll = _} {li ∧ ri} {tll} (s ←∧→ s₁) (lind ←∧) {↓} () | ¬∅ x
foo {ll = li ∧ ri} {tll} ↓ (lind ←∧) {ds ←∧} eq with del ↓ lind tll
foo {pll = _} {li ∧ ri} {tll} ↓ (lind ←∧) {ds ←∧} () | ∅
foo {pll = _} {li ∧ ri} {tll} ↓ (lind ←∧) {ds ←∧} () | ¬∅ x
foo {ll = li ∧ ri} {tll} (s ←∧) (lind ←∧) {ds ←∧} eq y with del s lind tll | inspect (del s lind) tll
foo {pll = _} {li ∧ ri} {tll} (s ←∧) (lind ←∧) {ds ←∧} () y | ∅ | r 
foo {pll = pll} {li ∧ ri} {tll} (s ←∧) (lind ←∧) {.x ←∧} refl y | ¬∅ x | [ eq ] = {!!} -- with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | foo s lind {x} (sym eq)
-- foo {pll = _} {li ∧ ri} {tll} (s ←∧) (lind ←∧) {.x ←∧} refl (hitsAtLeastOnce←∧←∧ y) | ¬∅ x | [ eq ] | g | r | e = e y
foo {ll = li ∧ ri} {tll} (∧→ s) (lind ←∧) {ds ←∧} eq = {!!}
foo {ll = li ∧ ri} {tll} (s ←∧→ s₁) (lind ←∧) {ds ←∧} eq = {!!}
foo {ll = li ∧ ri} {tll} s (lind ←∧) {∧→ ds} eq = {!!}
foo {ll = li ∧ ri} {tll} s (lind ←∧) {ds ←∧→ ds₁} eq = {!!}
foo {ll = (li ∧ ri)} {tll} s (∧→ lind) {ds} eq = {!!}
foo {ll = (li ∨ ri)} {tll} s (lind ←∨) {ds} eq = {!!}
foo {ll = (li ∨ ri)} {tll} s (∨→ lind) {ds} eq = {!!}
foo {ll = (li ∂ ri)} {tll} s (lind ←∂) {ds} eq = {!!}
foo {ll = (li ∂ ri)} {tll} s (∂→ lind) {ds} eq = {!!}



gest : ∀{i u rll ll n dt df tind ts} → (lf : LFun ll rll)
       → (ind : IndexLL (τ {i} {u} {n} {dt} df) ll) → (s : SetLL ll) → ¬ (hitsAtLeastOnce s ind)
       → ¬∅ tind ≡ tranLFMIndexLL lf (¬∅ ind) → ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)
       → ¬ (hitsAtLeastOnce ts tind) 
gest I ind s ¬ho refl refl = ¬ho
gest (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi eqs with truncSetLL s lind | isLTi lind ind
gest (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ∅ | yes p with del s lind ell | inspect (del s ind) ell
gest (_⊂_ {ind = ind} lf lf₁) ind₁ s ¬ho eqi () | ∅ | yes p | ∅ | [ eq ]
gest (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ∅ | yes p | ¬∅ x | [ eq ] = {!!} 
gest (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ∅ | no ¬p
                                                        with del s lind ell | inspect (del s lind) ell
gest (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi () | ∅ | no ¬p | ∅ | r
gest (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ∅ | no ¬p | ¬∅ x | [ eq ] = is where
  n¬ord = indτ&¬ge⇒¬Ord ind lind ¬p
  hf = ¬ord&¬ho-del⇒¬ho ind s ¬ho lind {x} n¬ord (sym eq)
  is = gest lf₁ (¬ord-morph ind lind ell (flipNotOrdᵢ n¬ord)) x hf eqi eqs
gest (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x | yes p = {!!}
gest (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x | no ¬p with tranLFMSetLL lf (¬∅ x)
gest (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x | no ¬p | ∅
                                                     with del s lind ell | inspect (del s lind) ell
gest (_⊂_ {ind = lind} lf lf₁) ind s ¬ho eqi () | ¬∅ x | no ¬p | ∅ | ∅ | r
gest (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ x₁ | no ¬p | ∅ | ¬∅ x | [ eq ] = is where
  n¬ord = indτ&¬ge⇒¬Ord ind lind ¬p
  hf = ¬ord&¬ho-del⇒¬ho ind s ¬ho lind {x} n¬ord (sym eq)
  is = gest lf₁ (¬ord-morph ind lind ell (flipNotOrdᵢ n¬ord)) x hf eqi eqs
gest (_⊂_ {ell = ell} {ind = lind} lf lf₁) ind s ¬ho eqi eqs | ¬∅ _ | no ¬p | ¬∅ x = gest lf₁ nind (replacePartOf s to x at lind) hf eqi eqs where
  n¬ord = indτ&¬ge⇒¬Ord ind lind ¬p
  nind = ¬ord-morph ind lind ell (flipNotOrdᵢ n¬ord)
  hf = ¬ord&¬ho-repl⇒¬ho ind s {x} ¬ho lind n¬ord
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
  
  
  
  
  
  
  
