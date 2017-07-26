-- {-# OPTIONS --show-implicit #-}

module LinFunContructw where

open import Common
open import LinLogic
import IndexLLProp 
open import LinFun
open import SetLL
open import SetLLProp

open import Relation.Binary.PropositionalEquality
open import Data.Product

open import LinFunContruct





module _ where

  open IndexLLProp 

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
    I : (complLₛ s ≡ ∅) →  MLFun ind s m¬ho lf
    -- ∀{ts} → 
    --  → (eqs : ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)) → (ceqo : complLₛ ts ≡ ∅)
    -- The above cannot be proved because we haven't told the function that s is special, its transformation will eventually go into a specific com except one input.
    -- thus for the I constructor to be, lf should not contain com or calls.
    ¬I∅ : ∀ {cs} → (ceqi : complLₛ s ≡ ¬∅ cs)
          → let tind = tranLFMIndexLL lf ind in
          (eqs : ∅ ≡ tranLFMSetLL lf (¬∅ s))
          → ((cll : LinLogic i {u}) → LFun (hf ll ind s ceqi m¬ho cll) rll)
          → MLFun ind s m¬ho lf 
    ¬I¬∅ : ∀ {cs ts cts} → (ceqi : complLₛ s ≡ ¬∅ cs)
           → let tind = tranLFMIndexLL lf ind in
           (eqs : ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)) → (ceqo : complLₛ ts ≡ ¬∅ cts)
           → ((cll : LinLogic i {u}) → LFun (hf ll ind s ceqi m¬ho cll) (hf rll tind ts ceqo (hf2 ind s m¬ho lf eqs) cll))
           → MLFun ind s m¬ho lf 
           -- We will never reach to a point where complLₛ ts ≡ ∅ because
           -- the input would have the same fate. ( s becomes smaller as we go forward, thus complLₛ increases. Here we take the case where s is not ∅.
           -- Correction : In fact , the ordinal remains the same since all the points of the set need to to end at the same com by design. (but we might not be able to prove this now and thus need to go with the weaker argument.)
  
  
    -- s here does contain the ind.
  test : ∀{i u rll ll n dt df} → (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll) → (s : SetLL ll)
         → ∀ m¬ho → (lf : LFun ll rll) → MLFun ind s m¬ho lf
  test ∅ s ∅ lf with complLₛ s | inspect complLₛ s
  test ∅ s ∅ lf | ∅ | [ eq ] = I eq
  test ∅ s ∅ I | ¬∅ x | [ eq ] = ¬I¬∅ eq refl eq (λ cll → I)
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] with truncSetLL s lind | inspect (truncSetLL s) lind
  ... | ∅ | [ teq ] with (mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at lind) | inspect (λ z → mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at z) lind
  ... | ∅ | [ meq ] = ⊥-elim ((trunc≡∅⇒¬mrpls≡∅ s lind teq) meq)
  ... | ¬∅ mx | [ meq ] with tranLFMSetLL lf₁ (¬∅ mx) | inspect (λ z → tranLFMSetLL lf₁ (¬∅ z)) mx | test {n = n} {dt} {df} ∅ mx ∅ lf₁
  ... | ¬∅ ts1 | [ ts1eq ] | I ceq = ⊥-elim ((del⇒¬ho s lind (sym meq)) (compl≡∅⇒ho mx ceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  ... | ¬∅ ts1 | [ ts1eq ] | ¬I∅ ceqi eqs t = ⊥-elim (r (trans eqs ts1eq)) where
    r : ¬ (∅ ≡ ((MSetLL rll) ∋ (¬∅ ts1)))
    r ()
  ... | ¬∅ ts1 | [ ts1eq ] | ¬I¬∅ {ts = ts} {cts} ceqi eqs ceqo t = ¬I¬∅ eq tseq (subst (λ z → complLₛ z ≡ ¬∅ cts) (sym r) ceqo) ((λ z → _⊂_ {ind = ¬ho-shr-morph s eq lind (trunc≡∅⇒¬ho s lind teq)} lf (g (t z)))) where
    r : ts1 ≡ ts
    r with trans eqs ts1eq
    r | refl = refl
    tseq =  sym (trans (cong (λ z → tranLFMSetLL lf₁ z) (trans (cong (λ z → mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) teq) meq)) ts1eq)
    g = subst (λ a → LFun a (shrink rll cts)) (shrink-repl-comm s lind eq teq meq ceqi)
  ... | ∅ | [ ts1eq ] | I ceq = ⊥-elim ((del⇒¬ho s lind (sym meq)) (compl≡∅⇒ho mx ceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  ... | ∅ | [ ts1eq ] | ¬I∅ ceqi eqs t = ¬I∅ eq tseq (λ z → _⊂_ {ind = ¬ho-shr-morph s eq lind (trunc≡∅⇒¬ho s lind teq)} lf (subst (λ a → LFun a rll) (shrink-repl-comm s lind eq teq meq ceqi) (t z))) where 
    tseq =  sym (trans (cong (λ z → tranLFMSetLL lf₁ z) (trans (cong (λ z → mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) teq) meq)) ts1eq)
  ... | ∅ | [ ts1eq ] | ¬I¬∅ ceqi eqs ceqo t with tranLFMSetLL lf₁ (¬∅ mx)
  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x | [ eq ] | ∅ | [ teq ] | ¬∅ mx | [ meq ] | ∅ | [ () ] | ¬I¬∅ ceqi refl ceqo t | .(¬∅ _)



  test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] with tranLFMSetLL lf (¬∅ trs) | inspect (λ z → tranLFMSetLL lf (¬∅ z)) trs | test {n = n} {dt} {df} ∅ trs ∅ lf
  ... | ∅ | tseq = {!!}
  ... | ¬∅ ts | tseq = {!!}


-- with test {n = n} {dt} {df} ∅ trs ∅ lf
--   ... | I ceq with mreplacePartOf (¬∅ s) to tlf at lind | inspect (λ z → mreplacePartOf (¬∅ s) to tlf at z) lind where -- tranLFMSetLL lf₁ nmx | inspect (tranLFMSetLL lf₁) nmx | test ∅ {!nmx!} ∅ lf₁ where
--     tlf = tranLFMSetLL lf (¬∅ trs)
-- --    is = test ∅ {!!} ∅ lf₁
--   ... | ∅ | [ meq ] = IMPOSSIBLE -- Since we have I, lf cannot contain com or call, thus tlf is not ∅.
--   ... | ¬∅ mx | [ meq ] with test {n = n} {dt} {df} ∅ mx ∅ lf₁
--   ... | I ceq1 = IMPOSSIBLE -- TODO This is impossible because eq assures us that complLₛ s ≡ ¬∅ x but complLₛ of both ceq and ceq1 are ∅.
--   ... | ¬I∅ ceqi1 eqs1 t1 = ¬I∅ eq tseq {!!} where
--     meeq = subst (λ z → (mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) ≡ ¬∅ mx) (sym teq) meq
--     tseq = subst (λ z → ∅ ≡ tranLFMSetLL lf₁ z) (sym meeq) eqs1
--   ... | ¬I¬∅ ceqi1 eqs1 ceqo1 t1 = {!!} 
--   test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬I∅ ceqi eqs q = {!!}
--   test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬I¬∅ ceqi eqs ceqo q = {!!} where
  test ∅ s ∅ (tr ltr lf) | ¬∅ x | [ eq ] = {!!}
  test ∅ s ∅ (com df₁ lf) | ¬∅ x | [ eq ] = IMPOSSIBLE -- Since ind is ∅, this is impossible.
  test ∅ s ∅ (call x₁) | ¬∅ x | [ eq ] = IMPOSSIBLE
  test (¬∅ x) s (¬∅ ¬ho) lf = {!!}
  
  
  
  
  
  
  
