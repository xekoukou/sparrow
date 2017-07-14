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

    hf2 : ∀{i u ll rll n dt df ts} → (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll)
          → (s : SetLL ll) → (m¬ho : M¬ho s ind) → (lf : LFun {i} {u} ll rll)
          → ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)
          → M¬ho ts (tranLFMIndexLL lf ind)
    hf2 ∅ mnho s lf eqs = ∅
    hf2 (¬∅ x) s mnho lf eqs with tranLFMIndexLL lf (¬∅ x) | inspect (tranLFMIndexLL lf) (¬∅ x)
    hf2 (¬∅ x) s mnho lf eqs | ∅ | [ eq ] = ∅
    hf2 (¬∅ x) s (¬∅ ¬ho) lf eqs | ¬∅ _ | [ eq ] = ¬∅ (tranLF-preserves-¬ho lf x s ¬ho (sym eq) eqs)
      
  data MLFun {i u ll rll n dt df} (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll)
             (s : SetLL ll) (m¬ho : M¬ho s ind) (lf : LFun {i} {u} ll rll) : Set (lsuc u) where
    ∅ : MLFun ind s m¬ho lf
    ¬∅ : ∀ {cs ts cts} → (ceqi : complLₛ s ≡ ¬∅ cs)
           → let tind = tranLFMIndexLL lf ind in
           (eqs : ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)) → (ceqo : complLₛ ts ≡ ¬∅ cts)
           → ((cll : LinLogic i {u}) → LFun (hf ll ind s ceqi m¬ho cll) (hf rll tind ts ceqo (hf2 ind s m¬ho lf eqs) cll))
           → MLFun ind s m¬ho lf 
           -- We will never reach to a point where complLₛ ts ≡ ∅ because
           -- the input would have the same fate. ( s becomes smaller as we go forward, thus complLₛ increases. Here we take the case where s is not ∅.
  
  
    -- s here does contain the ind.
  test : ∀{i u rll ll n dt df} → (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll) → (s : SetLL ll)
         → ∀ m¬ho → (lf : LFun ll rll) → MLFun ind s m¬ho lf
  test ∅ s ∅ lf with complLₛ s | inspect complLₛ s
  test ∅ s ∅ lf | ∅ | r = ∅
  test ∅ s ∅ I | ¬∅ x | [ eq ] = ¬∅ eq refl eq (λ cll → I)
  test ∅ s ∅ (lf ⊂ lf₁) | ¬∅ x | [ eq ] = {!!}
  test ∅ s ∅ (tr ltr lf) | ¬∅ x | [ eq ] = {!!}
  test ∅ s ∅ (com df₁ lf) | ¬∅ x | [ eq ] = {!!}
  test ∅ s ∅ (call x₁) | ¬∅ x | [ eq ] = IMPOSSIBLE
  test (¬∅ x) s (¬∅ ¬ho) lf = {!!}
  
  
  
  
  
  
  
