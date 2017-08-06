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
    hf2 (¬∅ x) s mnho lf eqs with tranLFMIndexLL lf (¬∅ x) | inspect (λ z → tranLFMIndexLL lf (¬∅ z)) x
    hf2 (¬∅ x) s mnho lf eqs | ∅ | [ eq ] = ∅
    hf2 (¬∅ x) s (¬∅ ¬ho) lf eqs | ¬∅ _ | [ eq ] = ¬∅ (tranLF-preserves-¬ho lf x s ¬ho (sym eq) eqs)


  data MLFun {i u ll rll n dt df} (mind : MIndexLL (τ {i} {u} {n} {dt} df) ll)
             (s : SetLL ll) (m¬ho : M¬ho s mind) (lf : LFun {i} {u} ll rll) : Set (lsuc u) where
    ∅ : ∀{ts} → (complLₛ s ≡ ∅)
        → (eqs : ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)) → (ceqo : complLₛ ts ≡ ∅) → MLFun mind s m¬ho lf
    ¬∅∅ : ∀ {ind cs} → (¬∅ ind ≡ mind) → (ceqi : complLₛ s ≡ ¬∅ cs)
          → let tind = tranLFMIndexLL lf mind in
          (eqs : ∅ ≡ tranLFMSetLL lf (¬∅ s))
          → ((cll : LinLogic i {u}) → LFun (hf ll mind s ceqi m¬ho cll) rll)
          → MLFun mind s m¬ho lf 
    ¬∅¬∅ : ∀ {cs ts cts} → (ceqi : complLₛ s ≡ ¬∅ cs)
           → let tind = tranLFMIndexLL lf mind in
           (eqs : ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)) → (ceqo : complLₛ ts ≡ ¬∅ cts)
           → ((cll : LinLogic i {u}) → LFun (hf ll mind s ceqi m¬ho cll) (hf rll tind ts ceqo (hf2 mind s m¬ho lf eqs) cll))
           → MLFun mind s m¬ho lf 
           --???  We will never reach to a point where complLₛ ts ≡ ∅ because
           -- the input would have the same fate. ( s becomes smaller as we go forward, thus complLₛ increases. Here we take the case where s is not ∅.
           -- Correction : In fact , the ordinal remains the same since all the points of the set need to to end at the same com by design. (but we might not be able to prove this now and thus need to go with the weaker argument.)
  



-- s is special, all of the input points eventually will be consumed by a single com + the point from the index. Thus if complLₛ s ≡ ∅, this means that lf does not contain coms or calls.
-- Maybe one day, we will provide a datatype that contains that information, for the time being, we use IMPOSSIBLE where necessary.

    -- s here does contain the ind.
  -- TODO IMPORTANT After test , we need to remove ⊂ that contain I in the first place.
  test : ∀{i u rll ll n dt df} → (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll) → (s : SetLL ll)
         → ∀ m¬ho → (lf : LFun ll rll) → MLFun ind s m¬ho lf
  test ind s mnho lf with complLₛ s | inspect complLₛ s
  test ∅ s ∅ lf | ∅ | [ e ] with tranLFMSetLL lf (¬∅ s) | inspect (λ z → tranLFMSetLL lf (¬∅ z)) s
  test ∅ s ∅ lf | ∅ | [ e ] | ∅ | [ r ] = IMPOSSIBLE
  test ∅ s ∅ lf | ∅ | [ e ] | ¬∅ x | [ r ] with complLₛ x | inspect complLₛ x
  test ∅ s ∅ lf | ∅ | [ e ] | ¬∅ x | [ r ] | ∅ | [ t ] = ∅ e (sym r) t
  test ∅ s ∅ lf | ∅ | [ e ] | ¬∅ x | [ r ] | ¬∅ x₁ | t = IMPOSSIBLE
  test (¬∅ x) s (¬∅ ¬ho) lf | ∅ | [ e ] = ⊥-elim (¬ho (compl≡∅⇒ho s e x)) 

  test ∅ s mnho I | ¬∅ x | [ eq ] = ¬∅¬∅ eq refl eq (λ cll → I)
  test (¬∅ x₁) s (¬∅ ¬ho) I | ¬∅ x | [ eq ] = ¬∅¬∅ eq refl eq (λ cll → I)

  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] with truncSetLL s lind | inspect (truncSetLL s) lind
  ... | ∅ | [ teq ] with (mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at lind) | inspect (λ z → mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at z) lind
  ... | ∅ | [ meq ] = ⊥-elim ((trunc≡∅⇒¬mrpls≡∅ s lind teq) meq)
  ... | ¬∅ mx | [ meq ] with test {n = n} {dt} {df} ∅ mx ∅ lf₁
  ... | ∅ ceq eqs ceqo = ⊥-elim ((del⇒¬ho s lind (sym meq)) (compl≡∅⇒ho mx ceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x | [ eq ] | ∅ | [ teq ] | ¬∅ mx | [ meq ] | ¬∅∅ () ceqi eqs t
  ... | ¬∅¬∅ {ts = ts} {cts} ceqi eqs ceqo t = ¬∅¬∅ eq tseq ceqo ((λ z → _⊂_ {ind = ¬ho-shr-morph s eq lind (trunc≡∅⇒¬ho s lind teq)} lf (g (t z)))) where
    tseq =  sym (trans (cong (λ z → tranLFMSetLL lf₁ z) (trans (cong (λ z → mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) teq) meq)) (sym eqs))
    g = subst (λ a → LFun a (shrink rll cts)) (shrink-repl-comm s lind eq teq meq ceqi)
  test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] with test {n = n} {dt} {df} ∅ trs ∅ lf
  ... | ∅ ceq eqs ceqo with (mreplacePartOf (¬∅ s) to (tranLFMSetLL lf (¬∅ trs)) at lind) | inspect (λ z → mreplacePartOf (¬∅ s) to (tranLFMSetLL lf (¬∅ trs)) at z) lind
  ... | ¬∅ mx | r with test {n = n} {dt} {df} ∅ mx ∅ lf₁
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ ceq eqs ceqo | ¬∅ mx | [ meq ] | ∅ ceq1 eqs1 ceqo1 with tranLFMSetLL lf (¬∅ trs)
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ ceq eqs ceqo | ¬∅ mx | [ meq ] | ∅ ceq1 eqs1 ceqo1 | ∅ = IMPOSSIBLE -- IMPOSSIBLE and not provable with the current information we have.
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ ceq eqs ceqo | ¬∅ mx | [ meq ] | ∅ ceq1 eqs1 ceqo1 | ¬∅ x with compl≡¬∅⇒replace-compl≡¬∅ s lind eq teq ceq x
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ ceq eqs ceqo | ¬∅ .(replacePartOf s to x at ind) | [ refl ] | ∅ ceq1 eqs1 ceqo1 | ¬∅ x | proj₃ , proj₄ with complLₛ (replacePartOf s to x at ind)
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ ceq eqs ceqo | ¬∅ .(replacePartOf s to x at ind) | [ refl ] | ∅ refl eqs1 ceqo1 | ¬∅ x | proj₃ , () | .∅
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ ceq eqs ceqo | ¬∅ mx | [ meq ] | ¬∅∅ () ceqi1 eqs1 t1
  test {rll = rll} {ll = ll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ {ts = ts} ceq eqs ceqo | ¬∅ mx | [ meq ] | ¬∅¬∅ {cs} ceqi1 eqs1 ceqo1 t1
    = ¬∅¬∅ eq tseq ceqo1 ((λ cll → subst (λ z → LFun z (shrink rll _)) (shrink-repl≡∅ s lind eq teq ceq _ ceqo t) (t1 cll))) where
    tseq =  sym (trans (cong (λ z → tranLFMSetLL lf₁ z) (trans (cong (λ z → mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) teq) meq)) (sym eqs1))
    t : complLₛ (replacePartOf s to ts at lind) ≡ ¬∅ cs
    t with trans (cong (λ z → mreplacePartOf ¬∅ s to z at lind) eqs) meq
    ... | g with replacePartOf s to ts at lind
    t | refl | e = ceqi1
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ ceq eqs ceqo | ∅ | [ meq ] with tranLFMSetLL lf (¬∅ trs)
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ ceq refl ceqo | ∅ | [ () ] | .(¬∅ _)
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind₁} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅∅ () ceqi eqs t
  test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t
       with (mreplacePartOf (¬∅ s) to (tranLFMSetLL lf (¬∅ trs)) at lind) | inspect (λ z → mreplacePartOf (¬∅ s) to (tranLFMSetLL lf (¬∅ trs)) at z) lind
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ∅ | [ meq ] with tranLFMSetLL lf (¬∅ trs)
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi () ceqo t | ∅ | [ meq ] | ∅
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ∅ | [ () ] | ¬∅ _
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ¬∅ mx | [ meq ] with test {n = n} {dt} {df} ∅ mx ∅ lf₁
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ¬∅ mx | [ meq ] | ∅ ceq1 eqs1 ceqo1 with tranLFMSetLL lf (¬∅ trs)
  test {rll = rll} {ll = ll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ {ts = ts} ceqi refl ceqo t | ¬∅ .(replacePartOf s to _ at lind) | [ refl ] | ∅ ceq1 eqs1 ceqo1 | .(¬∅ _) with complLₛ ts | ct where
    m = replacePartOf s to ts at lind
    mind = subst (λ z → IndexLL z (replLL ll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
    ct = compl≡∅⇒compltr≡∅ m ceq1 mind (sym (tr-repl⇒id s lind ts))
  test {rll = rll} {ll} {n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ {ts = ts} ceqi refl () t | ¬∅ .(replacePartOf s to ts at ind) | [ refl ] | ∅ ceq1 eqs1 ceqo1 | .(¬∅ ts) | .∅ | refl
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ¬∅ mx | [ meq ] | ¬∅∅ () ceqi₁ eqs₁ x₁
  test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ¬∅ mx | [ meq ] | ¬∅¬∅ ceqi1 eqs1 ceqo1 t1
      = ¬∅¬∅ eq tseq ceqo1 (λ cll → _⊂_ {ind = hind} (t cll) (subst (λ z → LFun z _) (sym (ho-shrink-repl-comm s lind eq teq ceqi ceqo w ceqi1)) (t1 cll))) where
    w = trans (cong (λ z → mreplacePartOf ¬∅ s to z at lind) eqs) meq
    tseq =  sym (trans (cong (λ z → tranLFMSetLL lf₁ z) (trans (cong (λ z → mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) teq) meq)) (sym eqs1))
    hind = ho-shr-morph s eq lind (sym teq) ceqi
  test (¬∅ x₁) s mnho (_⊂_ {ind = ind} lf lf₁) | ¬∅ x | [ eq ] = {!!}
  test ind s mnho (tr ltr lf) | ¬∅ x | eq = {!!}
  test ind s mnho (com df₁ lf) | ¬∅ x | eq = {!!}
  test ind s mnho (call x₁) | ¬∅ x | eq = {!!}





--  test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] with tranLFMSetLL lf (¬∅ trs) | inspect (λ z → tranLFMSetLL lf (¬∅ z)) trs | test {n = n} {dt} {df} ∅ trs ∅ lf
--  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ | [ tseq ] | I x eqs ceqo with tranLFMSetLL lf (¬∅ trs)
--  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ | [ refl ] | I x () ceqo | .∅
--  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ | tseq | ¬I∅ ceqi eqs x = {!!}
--  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ | [ tseq ] | ¬I¬∅ ceqi eqs ceqo x with tranLFMSetLL lf (¬∅ trs)
--  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ | [ refl ] | ¬I¬∅ ceqi () ceqo x | .(¬∅ _)
--
--  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ¬∅ ts | tseq | I x eqs ceqo = {!!}
--  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ¬∅ ts | tseq | ¬I∅ ceqi eqs x = {!!}
--  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ¬∅ ts | tseq | ¬I¬∅ ceqi eqs ceqo x = {!!}
--
--
---- with test {n = n} {dt} {df} ∅ trs ∅ lf
----   ... | I ceq with mreplacePartOf (¬∅ s) to tlf at lind | inspect (λ z → mreplacePartOf (¬∅ s) to tlf at z) lind where -- tranLFMSetLL lf₁ nmx | inspect (tranLFMSetLL lf₁) nmx | test ∅ {!nmx!} ∅ lf₁ where
----     tlf = tranLFMSetLL lf (¬∅ trs)
---- --    is = test ∅ {!!} ∅ lf₁
----   ... | ∅ | [ meq ] = IMPOSSIBLE -- Since we have I, lf cannot contain com or call, thus tlf is not ∅.
----   ... | ¬∅ mx | [ meq ] with test {n = n} {dt} {df} ∅ mx ∅ lf₁
----   ... | I ceq1 = IMPOSSIBLE -- TODO This is impossible because eq assures us that complLₛ s ≡ ¬∅ x but complLₛ of both ceq and ceq1 are ∅.
----   ... | ¬I∅ ceqi1 eqs1 t1 = ¬I∅ eq tseq {!!} where
----     meeq = subst (λ z → (mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) ≡ ¬∅ mx) (sym teq) meq
----     tseq = subst (λ z → ∅ ≡ tranLFMSetLL lf₁ z) (sym meeq) eqs1
----   ... | ¬I¬∅ ceqi1 eqs1 ceqo1 t1 = {!!} 
----   test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬I∅ ceqi eqs q = {!!}
----   test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬I¬∅ ceqi eqs ceqo q = {!!} where
--  test ∅ s ∅ (tr ltr lf) | ¬∅ x | [ eq ] = {!!}
--  test ∅ s ∅ (com df₁ lf) | ¬∅ x | [ eq ] = IMPOSSIBLE -- Since ind is ∅, this is impossible.
--  test ∅ s ∅ (call x₁) | ¬∅ x | [ eq ] = IMPOSSIBLE
--  test (¬∅ x) s (¬∅ ¬ho) lf = {!!}
--  
--  
  
  
  
  
  
