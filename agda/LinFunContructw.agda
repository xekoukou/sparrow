-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS --show-irrelevant #-}
-- {-# OPTIONS -v tc.meta:40 #-}
-- {-# OPTIONS --verbose tc.conv.term:40 #-}
-- {-# OPTIONS --verbose tc.conv.level:40 #-}
-- {-# OPTIONS --verbose tc.conv.atom:50 #-}
-- {-# OPTIONS --verbose tc.conv.elim:50 #-}

module LinFunContructw where

open import Common
open import LinLogic
import IndexLLProp 
open import LinFun
open import SetLL
open import SetLLProp
open import CTT

open import Relation.Binary.PropositionalEquality
open import Data.Product


open import LinFunContruct



module _ where

  private
    module _ where
    
      open import PathPrelude hiding (_≡_)
    
      lem1 : ∀{i u ll ell pll x} → (s : SetLL ll) → (lind : IndexLL {i} {u} pll ll)
            → (eq : complLₛ s ≡ ¬∅ x)
            → (¬ho : ¬ hitsAtLeastOnce s lind)
            → (teq : truncSetLL s lind ≡ ∅)
            → ∀{mx}
            → del s lind ell ≡ ¬∅ mx
            → ∀{cs}
            → complLₛ mx ≡ ¬∅ cs
            → (shrink (replLL ll lind ell) cs) ≡ replLL (shrink ll x) (¬ho-shr-morph s eq lind (trunc≡∅⇒¬ho s lind (¬ho⇒trunc≡∅ s lind ¬ho))) ell
            → (shrink (replLL ll lind ell) cs) ≡ replLL (shrink ll x) (¬ho-shr-morph s eq lind ¬ho) ell
      lem1 {ll = ll} {ell} {_} {x} s lind eq ¬ho _ _ {cs} _ req = PathPrelude.subst {P = λ x → x} w req where
        w = PathPrelude.cong (λ z → (shrink (replLL ll lind ell) cs) ≡ replLL (shrink ll x) (¬ho-shr-morph s eq lind z) ell) (¬fun-eq (trunc≡∅⇒¬ho s lind (¬ho⇒trunc≡∅ s lind ¬ho)) ¬ho) 
     
    
    
  open IndexLLProp

  roo : ∀{i u ll ell pll x} → (s : SetLL ll) → (lind : IndexLL {i} {u} pll ll)
        → (eq : complLₛ s ≡ ¬∅ x)
        → (¬ho : ¬ hitsAtLeastOnce s lind)
        → let mx = proj₁ (¬ho⇒del≡¬∅ s lind ¬ho) in
          ∀{cs}
          → complLₛ mx ≡ ¬∅ cs
          → (shrink (replLL ll lind ell) cs) ≡ replLL (shrink ll x) (¬ho-shr-morph s eq lind ¬ho) ell
  roo {ell = ell} s lind eq ¬ho cmeq with smx | mx | meq where
    smx = ¬ho⇒del≡¬∅ {fll = ell} s lind ¬ho
    mx = proj₁ smx
    meq = proj₂ smx
  ... | g | mx | meq = lem1 s lind eq ¬ho ((¬ho⇒trunc≡∅ s lind ¬ho)) meq cmeq r where
    r = shrink-repl-comm s lind eq (¬ho⇒trunc≡∅ s lind ¬ho) meq cmeq





  woo : {i : Size} {u : Level} (ls : LinLogic i {u}) (s : SetLL ls) (w : MSetLL ls) (w₁ : Reveal complLₛ · s is w)
        (rs : LinLogic i) {ell pll tll : LinLogic i} {cs : SetLL (ls ∧ rs)} (eq : (complLₛ (s ←∧) ) ≡ ¬∅ cs)
        (ind : IndexLL pll ls) (lind : IndexLL tll ls) (¬hob : hitsAtLeastOnce (s ←∧) (ind ←∧) → ⊥) (¬hoh : hitsAtLeastOnce (s ←∧) (lind ←∧) → ⊥)
        {mcs : SetLL (replLL ls lind ell ∧ rs)} (ceqi : complLₛ   (proj₁    (¬ho⇒del≡¬∅ (s ←∧) (lind ←∧) ¬hoh )) ≡ ¬∅ mcs)
        (nord : Orderedᵢ (ind ←∧) (lind ←∧) → ⊥) →
--        let mx = proj₁ (¬ho⇒del≡¬∅ {fll = ell} (s ←∧) (lind ←∧) ¬hoh)
--            nind = ¬ord-morph (ind ←∧) (lind ←∧) ell (flipNotOrdᵢ nord) 
--            rgeq = subst (λ z → IndexLL pll z) (roo {ell = ell} (s ←∧) (lind ←∧) eq ¬hoh ceqi) (¬ho-shr-morph mx ceqi nind (¬ord&¬ho-del⇒¬ho (ind ←∧) (s ←∧) ¬hob (lind ←∧) nord (sym (proj₂ (¬ho⇒del≡¬∅ (s ←∧) (lind ←∧) ¬hoh))))) in
        ¬ord-morph (¬ho-shr-morph (s ←∧) eq (ind ←∧) ¬hob) (¬ho-shr-morph (s ←∧) eq (lind ←∧) ¬hoh ) ell (λ z → nord   (¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh    (flipOrdᵢ z)))
        ≡ {!!}
  woo = {!!}


  boo : {i : Size} {u : Level} (ls : LinLogic i) (s : SetLL ls) (w : MSetLL ls) (w₁ : Reveal complLₛ · s is w)
        (rs : LinLogic i) {ell pll tll : LinLogic i} {cs : SetLL (ls ∧ rs)} (eq : (complLₛ (s ←∧)) ≡ ¬∅ cs)
        (ind : IndexLL pll ls) (lind : IndexLL tll ls) (¬hob : hitsAtLeastOnce (s ←∧) (ind ←∧) → ⊥) (¬hoh : hitsAtLeastOnce (s ←∧) (lind ←∧) → ⊥)
        {mcs : SetLL (replLL ls lind ell ∧ rs)} (ceqi : complLₛ   (proj₁    (¬ho⇒del≡¬∅ (s ←∧) (lind ←∧) ¬hoh )) ≡ ¬∅ mcs)
        (nord : Orderedᵢ (ind ←∧) (lind ←∧) → ⊥) →
        ¬ord-morph (¬ho-shr-morph (s ←∧) eq (ind ←∧) ¬hob )(¬ho-shr-morph (s ←∧) eq (lind ←∧) ¬hoh ) ell (λ z →   nord   (¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh    (flipOrdᵢ z)))
        ≡ {!!}
  boo = {!!}




  poo : ∀ {i u ll ell pll tll cs} → (s : SetLL ll) → (eq : complLₛ s ≡ ¬∅ cs) → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL tll ll)
        → (¬hob : ¬ hitsAtLeastOnce s ind)
        → (¬hoh : ¬ hitsAtLeastOnce s lind)
        → let mx = proj₁ (¬ho⇒del≡¬∅ {fll = ell} s lind ¬hoh) in
        ∀{mcs}
        → (ceqi : complLₛ mx ≡ ¬∅ mcs)
        → let hind = ¬ho-shr-morph s eq lind ¬hoh
              bind = ¬ho-shr-morph s eq ind ¬hob in
        (nord : ¬ Orderedᵢ ind lind) →
        let nind = ¬ord-morph ind lind ell (flipNotOrdᵢ nord)
            hnord : ¬ (Orderedᵢ hind bind)
            hnord = ( λ z → nord (¬ho-shr-morph-pres-¬ord s eq ind lind ¬hob ¬hoh (flipOrdᵢ z))) in
        ¬ord-morph bind hind ell hnord ≡ {!!} -- subst (λ z → IndexLL pll z) (roo {ell = ell} s lind eq ¬hoh ceqi) (¬ho-shr-morph mx ceqi nind (¬ord&¬ho-del⇒¬ho ind s ¬hob lind nord (sym (proj₂ (¬ho⇒del≡¬∅ s lind ¬hoh)))))  
  poo ↓ () ind lind ¬hob ¬hoh ceqi nord
  poo (s ←∧) eq ↓ lind ¬hob ¬hoh ceqi nord = ⊥-elim (¬hob hitsAtLeastOnce←∧↓)
  poo {ell = ell} (s ←∧) eq (ind ←∧) ↓ ¬hob ¬hoh ceqi nord = ⊥-elim (¬hoh hitsAtLeastOnce←∧↓)
  poo {ll = ls ∧ rs} {ell = ell} {pll} {tll} {cs} (s ←∧) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh ceqi nord = {!!} where -- with complLₛ s | inspect complLₛ s where
    hind = ¬ho-shr-morph (s ←∧) eq (lind ←∧) ¬hoh
    bind = ¬ho-shr-morph (s ←∧) eq (ind ←∧) ¬hob
    hnord : ¬ (Orderedᵢ hind bind)
    hnord z = nord (¬ho-shr-morph-pres-¬ord (s ←∧) eq (ind ←∧) (lind ←∧) ¬hob ¬hoh (flipOrdᵢ z))
    lgeq = ¬ord-morph bind hind ell hnord
    mx = proj₁ (¬ho⇒del≡¬∅ {fll = ell} (s ←∧) (lind ←∧) ¬hoh)
    nind = ¬ord-morph (ind ←∧) (lind ←∧) ell (flipNotOrdᵢ nord)
    rgeq = subst (λ z → IndexLL pll z) (roo {ell = ell} (s ←∧) (lind ←∧) eq ¬hoh ceqi) (¬ho-shr-morph mx ceqi nind (¬ord&¬ho-del⇒¬ho (ind ←∧) (s ←∧) ¬hob (lind ←∧) nord (sym (proj₂ (¬ho⇒del≡¬∅ (s ←∧) (lind ←∧) ¬hoh)))))
--  ... | g | e = ?
  poo {ell = ell} (s ←∧) eq (ind ←∧) (∧→ lind) ¬hob ¬hoh ceqi nord = {!!} -- with complLₛ s | inspect complLₛ s
--  ... | g | e = {!!}
  poo (s ←∧) eq (∧→ ind) ↓ ¬hob ¬hoh ceqi nord = ⊥-elim (¬hoh hitsAtLeastOnce←∧↓)
  poo (s ←∧) eq (∧→ ind) (lind ←∧) ¬hob ¬hoh ceqi nord = {!!}
  poo (s ←∧) eq (∧→ ind) (∧→ lind) ¬hob ¬hoh ceqi nord = {!!}
  poo (∧→ s) eq ↓ lind ¬hob ¬hoh ceqi nord = ⊥-elim (¬hob hitsAtLeastOnce∧→↓)
  poo (∧→ s) eq (ind ←∧) lind ¬hob ¬hoh ceqi nord = {!!}
  poo (∧→ s) eq (∧→ ind) lind ¬hob ¬hoh ceqi nord = {!!}
  poo (s ←∧→ s₁) eq ind lind ¬hob ¬hoh ceqi nord = {!!}
  poo (s ←∨) eq ind lind ¬hob ¬hoh ceqi nord = {!!}
  poo (∨→ s) eq ind lind ¬hob ¬hoh ceqi nord = {!!}
  poo (s ←∨→ s₁) eq ind lind ¬hob ¬hoh ceqi nord = {!!}
  poo (s ←∂) eq ind lind ¬hob ¬hoh ceqi nord = {!!}
  poo (∂→ s) eq ind lind ¬hob ¬hoh ceqi nord = {!!}
  poo (s ←∂→ s₁) eq ind lind ¬hob ¬hoh ceqi nord = {!!}



--   private
--     data M¬ho {i u ll n dt df} (s : SetLL ll) : MIndexLL (τ {i} {u} {n} {dt} df) ll → Set where
--       ∅ : M¬ho s ∅
--       ¬∅ : {ind : IndexLL (τ {i} {u} {n} {dt} df) ll} → (¬ho : ¬ (hitsAtLeastOnce s ind))
--            → M¬ho s (¬∅ ind)

--     hf : ∀{i u n dt df} → ∀ ll → ∀{cs} → (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll)
--          → (s : SetLL ll) → (ceq : complLₛ s ≡ ¬∅ cs) → (m¬ho : M¬ho s ind) → LinLogic i {u}
--          → LinLogic i {u}
--     hf ll {cs} ∅ s ceq mnho cll = shrinkcms ll s cs ceq
--     hf ll {cs} (¬∅ x) s ceq (¬∅ ¬ho) cll = replLL (shrinkcms ll s cs ceq) (¬ho-shr-morph s ceq x ¬ho) cll

--     hf2 : ∀{i u ll rll n dt df ts} → (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll)
--           → (s : SetLL ll) → (m¬ho : M¬ho s ind) → (lf : LFun {i} {u} ll rll)
--           → ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)
--           → M¬ho ts (tranLFMIndexLL lf ind)
--     hf2 ∅ mnho s lf eqs = ∅
--     hf2 (¬∅ x) s mnho lf eqs with tranLFMIndexLL lf (¬∅ x) | inspect (λ z → tranLFMIndexLL lf (¬∅ z)) x
--     hf2 (¬∅ x) s mnho lf eqs | ∅ | [ eq ] = ∅
--     hf2 (¬∅ x) s (¬∅ ¬ho) lf eqs | ¬∅ _ | [ eq ] = ¬∅ (tranLF-preserves-¬ho lf x s ¬ho (sym eq) eqs)


--   data MLFun {i u ll rll n dt df} (mind : MIndexLL (τ {i} {u} {n} {dt} df) ll)
--              (s : SetLL ll) (m¬ho : M¬ho s mind) (lf : LFun {i} {u} ll rll) : Set (lsuc u) where
--     ∅ : ∀{ts} → (∅ ≡ mind) → (complLₛ s ≡ ∅)
--         → (eqs : ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)) → (ceqo : complLₛ ts ≡ ∅) → MLFun mind s m¬ho lf
--     ¬∅∅ : ∀ {ind cs} → (¬∅ ind ≡ mind) → (ceqi : complLₛ s ≡ ¬∅ cs)
--           → (eqs : ∅ ≡ tranLFMSetLL lf (¬∅ s))
--           → (cll : LinLogic i {u}) → LFun (hf ll mind s ceqi m¬ho cll) rll
--           → MLFun mind s m¬ho lf 
--     ¬∅¬∅ : ∀ {cs ts cts} → (ceqi : complLₛ s ≡ ¬∅ cs)
--            → let tind = tranLFMIndexLL lf mind in
--            (eqs : ¬∅ ts ≡ tranLFMSetLL lf (¬∅ s)) → (ceqo : complLₛ ts ≡ ¬∅ cts)
--            → ((cll : LinLogic i {u}) → LFun (hf ll mind s ceqi m¬ho cll) (hf rll tind ts ceqo (hf2 mind s m¬ho lf eqs) cll))
--            → MLFun mind s m¬ho lf 
--            --???  We will never reach to a point where complLₛ ts ≡ ∅ because
--            -- the input would have the same fate. ( s becomes smaller as we go forward, thus complLₛ increases. Here we take the case where s is not ∅.
--            -- Correction : In fact , the ordinal remains the same since all the points of the set need to to end at the same com by design. (but we might not be able to prove this now and thus need to go with the weaker argument.)
  



-- -- s is special, all of the input points eventually will be consumed by a single com + the point from the index. Thus if complLₛ s ≡ ∅, this means that lf does not contain coms or calls.
-- -- Maybe one day, we will provide a datatype that contains that information, for the time being, we use IMPOSSIBLE where necessary.

--     -- s here does contain the ind.
--   -- TODO IMPORTANT After test , we need to remove ⊂ that contain I in the first place.
--   test : ∀{i u rll ll n dt df} → (ind : MIndexLL (τ {i} {u} {n} {dt} df) ll) → (s : SetLL ll)
--          → ∀ m¬ho → (lf : LFun ll rll) → MLFun ind s m¬ho lf
--   test ind s mnho lf with complLₛ s | inspect complLₛ s
--   test ∅ s ∅ lf | ∅ | [ e ] with tranLFMSetLL lf (¬∅ s) | inspect (λ z → tranLFMSetLL lf (¬∅ z)) s
--   test ∅ s ∅ lf | ∅ | [ e ] | ∅ | [ r ] = IMPOSSIBLE
--   test ∅ s ∅ lf | ∅ | [ e ] | ¬∅ x | [ r ] with complLₛ x | inspect complLₛ x
--   test ∅ s ∅ lf | ∅ | [ e ] | ¬∅ x | [ r ] | ∅ | [ t ] = ∅ refl e (sym r) t
--   test ∅ s ∅ lf | ∅ | [ e ] | ¬∅ x | [ r ] | ¬∅ x₁ | t = IMPOSSIBLE
--   test (¬∅ x) s (¬∅ ¬ho) lf | ∅ | [ e ] = ⊥-elim (¬ho (compl≡∅⇒ho s e x)) 

--   test ∅ s mnho I | ¬∅ x | [ eq ] = ¬∅¬∅ eq refl eq (λ cll → I)
--   test (¬∅ x₁) s (¬∅ ¬ho) I | ¬∅ x | [ eq ] = ¬∅¬∅ eq refl eq (λ cll → I)

--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] with truncSetLL s lind | inspect (truncSetLL s) lind
--   ... | ∅ | [ teq ] with (mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at lind) | inspect (λ z → mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at z) lind
--   ... | ∅ | [ meq ] = ⊥-elim ((trunc≡∅⇒¬mrpls≡∅ s lind teq) meq)
--   ... | ¬∅ mx | [ meq ] with test {n = n} {dt} {df} ∅ mx ∅ lf₁
--   ... | ∅ indeq ceq eqs ceqo = ⊥-elim ((del⇒¬ho s lind (sym meq)) (compl≡∅⇒ho mx ceq (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind))))
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x | [ eq ] | ∅ | [ teq ] | ¬∅ mx | [ meq ] | ¬∅∅ () ceqi eqs cll t
--   ... | ¬∅¬∅ {ts = ts} {cts} ceqi eqs ceqo t = ¬∅¬∅ eq tseq ceqo ((λ z → _⊂_ {ind = ¬ho-shr-morph s eq lind (trunc≡∅⇒¬ho s lind teq)} lf (g (t z)))) where
--     tseq =  sym (trans (cong (λ z → tranLFMSetLL lf₁ z) (trans (cong (λ z → mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) teq) meq)) (sym eqs))
--     g = subst (λ a → LFun a (shrink rll cts)) (shrink-repl-comm s lind eq teq meq ceqi)
--   test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] with test {n = n} {dt} {df} ∅ trs ∅ lf
--   ... | ∅ indeq ceq eqs ceqo with (mreplacePartOf (¬∅ s) to (tranLFMSetLL lf (¬∅ trs)) at lind) | inspect (λ z → mreplacePartOf (¬∅ s) to (tranLFMSetLL lf (¬∅ trs)) at z) lind
--   ... | ¬∅ mx | r with test {n = n} {dt} {df} ∅ mx ∅ lf₁
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ indeq ceq eqs ceqo | ¬∅ mx | [ meq ] | ∅ indeq1 ceq1 eqs1 ceqo1 with tranLFMSetLL lf (¬∅ trs)
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ indeq ceq eqs ceqo | ¬∅ mx | [ meq ] | ∅ indeq1 ceq1 eqs1 ceqo1 | ∅ = IMPOSSIBLE -- IMPOSSIBLE and not provable with the current information we have.
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ indeq ceq eqs ceqo | ¬∅ mx | [ meq ] | ∅ indeq1 ceq1 eqs1 ceqo1 | ¬∅ x with compl≡¬∅⇒replace-compl≡¬∅ s lind eq teq ceq x
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ indeq ceq eqs ceqo | ¬∅ .(replacePartOf s to x at ind) | [ refl ] | ∅ indeq1 ceq1 eqs1 ceqo1 | ¬∅ x | proj₃ , proj₄ with complLₛ (replacePartOf s to x at ind)
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ indeq ceq eqs ceqo | ¬∅ .(replacePartOf s to x at ind) | [ refl ] | ∅ indeq1 refl eqs1 ceqo1 | ¬∅ x | proj₃ , () | .∅
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ indeq ceq eqs ceqo | ¬∅ mx | [ meq ] | ¬∅∅ () ceqi1 eqs1 cll1 t1
--   test {rll = rll} {ll = ll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ {ts = ts} indeq ceq eqs ceqo | ¬∅ mx | [ meq ] | ¬∅¬∅ {cs} ceqi1 eqs1 ceqo1 t1
--     = ¬∅¬∅ eq tseq ceqo1 ((λ cll → subst (λ z → LFun z (shrink rll _)) (shrink-repl≡∅ s lind eq teq ceq _ ceqo t) (t1 cll))) where
--     tseq =  sym (trans (cong (λ z → tranLFMSetLL lf₁ z) (trans (cong (λ z → mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) teq) meq)) (sym eqs1))
--     t : complLₛ (replacePartOf s to ts at lind) ≡ ¬∅ cs
--     t with trans (cong (λ z → mreplacePartOf ¬∅ s to z at lind) eqs) meq
--     ... | g with replacePartOf s to ts at lind
--     t | refl | e = ceqi1
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ indeq ceq eqs ceqo | ∅ | [ meq ] with tranLFMSetLL lf (¬∅ trs)
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ∅ indeq ceq refl ceqo | ∅ | [ () ] | .(¬∅ _)
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind₁} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅∅ () ceqi eqs cll t
--   test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t
--        with (mreplacePartOf (¬∅ s) to (tranLFMSetLL lf (¬∅ trs)) at lind) | inspect (λ z → mreplacePartOf (¬∅ s) to (tranLFMSetLL lf (¬∅ trs)) at z) lind
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ∅ | [ meq ] with tranLFMSetLL lf (¬∅ trs)
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi () ceqo t | ∅ | [ meq ] | ∅
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ∅ | [ () ] | ¬∅ _
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ¬∅ mx | [ meq ] with test {n = n} {dt} {df} ∅ mx ∅ lf₁
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ¬∅ mx | [ meq ] | ∅ indeq ceq1 eqs1 ceqo1 with tranLFMSetLL lf (¬∅ trs)
--   test {rll = rll} {ll = ll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ {ts = ts} ceqi refl ceqo t | ¬∅ .(replacePartOf s to _ at lind) | [ refl ] | ∅ indeq1 ceq1 eqs1 ceqo1 | .(¬∅ _) with complLₛ ts | ct where
--     m = replacePartOf s to ts at lind
--     mind = subst (λ z → IndexLL z (replLL ll lind ell)) (replLL-↓ lind) ((a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)))
--     ct = compl≡∅⇒compltr≡∅ m ceq1 mind (sym (tr-repl⇒id s lind ts))
--   test {rll = rll} {ll} {n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ {ts = ts} ceqi refl () t | ¬∅ .(replacePartOf s to ts at ind) | [ refl ] | ∅ indeq ceq1 eqs1 ceqo1 | .(¬∅ ts) | .∅ | refl
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ¬∅ mx | [ meq ] | ¬∅∅ () ceqi₁ eqs₁ cll1 x₁
--   test {rll = rll} {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬∅¬∅ ceqi eqs ceqo t | ¬∅ mx | [ meq ] | ¬∅¬∅ ceqi1 eqs1 ceqo1 t1
--       = ¬∅¬∅ eq tseq ceqo1 (λ cll → _⊂_ {ind = hind} (t cll) (subst (λ z → LFun z _) (sym (ho-shrink-repl-comm s lind eq teq ceqi ceqo w ceqi1)) (t1 cll))) where
--     w = trans (cong (λ z → mreplacePartOf ¬∅ s to z at lind) eqs) meq
--     tseq =  sym (trans (cong (λ z → tranLFMSetLL lf₁ z) (trans (cong (λ z → mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) teq) meq)) (sym eqs1))
--     hind = ho-shr-morph s eq lind (sym teq) ceqi
--   test {rll = rll} {n = n} {dt} {df} (¬∅ ind) s (¬∅ ¬ho) (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] with truncSetLL s lind | inspect (truncSetLL s) lind
--   ... | ∅ | [ teq ] with (mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at lind) | inspect (λ z → mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at z) lind
--   ... | ∅ | [ meq ] = ⊥-elim ((trunc≡∅⇒¬mrpls≡∅ s lind teq) meq)
--   ... | ¬∅ mx | [ meq ] with isLTi lind ind
--   ... | no ¬p with test {n = n} {dt} {df} nind mx (¬∅ n¬ho) lf₁ where
--     nord = indτ&¬ge⇒¬Ord ind lind ¬p
--     nind = ¬∅ (¬ord-morph ind lind ell (flipNotOrdᵢ nord))
--     n¬ho = ¬ord&¬ho-del⇒¬ho ind s ¬ho lind nord (sym meq)
--   ... | ∅ () ceq eqs ceqo
--   test {rll = rll} {n = n} {dt} {df} (¬∅ ind) s (¬∅ ¬ho) (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ∅ | [ teq ] | ¬∅ mx | [ meq ] | no ¬p | ¬∅∅ {ind = tind} indeq ceqi eqs cll t
--     = ¬∅∅ refl eq tseq cll (_⊂_ {ind = sind} lf {!l1!}) where 
--     nord = indτ&¬ge⇒¬Ord ind lind ¬p
--     tseq =  sym (trans (cong (λ z → tranLFMSetLL lf₁ z) (trans (cong (λ z → mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) teq) meq)) (sym eqs))
--     hind = ¬ho-shr-morph s eq lind ((trunc≡∅⇒¬ho s lind teq))
--     bind = ¬ho-shr-morph s eq ind ¬ho
    
--     hord : ¬ Orderedᵢ bind hind
--     hord x = nord (¬ho-shr-morph-pres-¬ord s eq ind lind ¬ho (trunc≡∅⇒¬ho s lind teq) x)
    
--     sind = ¬ord-morph hind bind cll hord 
--     l1 = replLL-¬ordab≡ba bind cll hind ell (flipNotOrdᵢ hord)
--     l2 = {!cong (λ z → replLL z (¬ord-morph bind hind ell ?) cll) ?!} 

--     find = ¬ord-morph ind lind ell (flipNotOrdᵢ nord)
--     nind = ¬ord-morph lind ind cll nord
--   test {rll = rll} {n = n} {dt} {df} (¬∅ ind) s (¬∅ ¬ho) (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ∅ | [ teq ] | ¬∅ mx | [ meq ] | no ¬p | ¬∅¬∅ ceqi eqs ceqo t = {!!}
--   test {rll = rll} {n = n} {dt} {df} (¬∅ ind) s (¬∅ ¬ho) (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ∅ | [ teq ] | ¬∅ mx | [ meq ] | yes p = {!!}
--   test (¬∅ ind₁) s (¬∅ ¬ho) (_⊂_ {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] = {!!}
--   test ind s mnho (tr ltr lf) | ¬∅ x | eq = {!!}
--   test ind s mnho (com df₁ lf) | ¬∅ x | eq = {!!}
--   test ind s mnho (call x₁) | ¬∅ x | eq = {!!}





-- --  test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] with tranLFMSetLL lf (¬∅ trs) | inspect (λ z → tranLFMSetLL lf (¬∅ z)) trs | test {n = n} {dt} {df} ∅ trs ∅ lf
-- --  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ | [ tseq ] | I x eqs ceqo with tranLFMSetLL lf (¬∅ trs)
-- --  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ | [ refl ] | I x () ceqo | .∅
-- --  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ | tseq | ¬I∅ ceqi eqs x = {!!}
-- --  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ | [ tseq ] | ¬I¬∅ ceqi eqs ceqo x with tranLFMSetLL lf (¬∅ trs)
-- --  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ∅ | [ refl ] | ¬I¬∅ ceqi () ceqo x | .(¬∅ _)
-- --
-- --  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ¬∅ ts | tseq | I x eqs ceqo = {!!}
-- --  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ¬∅ ts | tseq | ¬I∅ ceqi eqs x = {!!}
-- --  test ∅ s ∅ (_⊂_ {ell = ell} {ind = ind} lf lf₁) | ¬∅ x₁ | [ eq ] | ¬∅ trs | [ teq ] | ¬∅ ts | tseq | ¬I¬∅ ceqi eqs ceqo x = {!!}
-- --
-- --
-- ---- with test {n = n} {dt} {df} ∅ trs ∅ lf
-- ----   ... | I ceq with mreplacePartOf (¬∅ s) to tlf at lind | inspect (λ z → mreplacePartOf (¬∅ s) to tlf at z) lind where -- tranLFMSetLL lf₁ nmx | inspect (tranLFMSetLL lf₁) nmx | test ∅ {!nmx!} ∅ lf₁ where
-- ----     tlf = tranLFMSetLL lf (¬∅ trs)
-- ---- --    is = test ∅ {!!} ∅ lf₁
-- ----   ... | ∅ | [ meq ] = IMPOSSIBLE -- Since we have I, lf cannot contain com or call, thus tlf is not ∅.
-- ----   ... | ¬∅ mx | [ meq ] with test {n = n} {dt} {df} ∅ mx ∅ lf₁
-- ----   ... | I ceq1 = IMPOSSIBLE -- TODO This is impossible because eq assures us that complLₛ s ≡ ¬∅ x but complLₛ of both ceq and ceq1 are ∅.
-- ----   ... | ¬I∅ ceqi1 eqs1 t1 = ¬I∅ eq tseq {!!} where
-- ----     meeq = subst (λ z → (mreplacePartOf ¬∅ s to tranLFMSetLL lf z at lind) ≡ ¬∅ mx) (sym teq) meq
-- ----     tseq = subst (λ z → ∅ ≡ tranLFMSetLL lf₁ z) (sym meeq) eqs1
-- ----   ... | ¬I¬∅ ceqi1 eqs1 ceqo1 t1 = {!!} 
-- ----   test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬I∅ ceqi eqs q = {!!}
-- ----   test {n = n} {dt} {df} ∅ s ∅ (_⊂_ {ell = ell} {ind = lind} lf lf₁) | ¬∅ x | [ eq ] | ¬∅ trs | [ teq ] | ¬I¬∅ ceqi eqs ceqo q = {!!} where
-- --  test ∅ s ∅ (tr ltr lf) | ¬∅ x | [ eq ] = {!!}
-- --  test ∅ s ∅ (com df₁ lf) | ¬∅ x | [ eq ] = IMPOSSIBLE -- Since ind is ∅, this is impossible.
-- --  test ∅ s ∅ (call x₁) | ¬∅ x | [ eq ] = IMPOSSIBLE
-- --  test (¬∅ x) s (¬∅ ¬ho) lf = {!!}
-- --  
-- --  
  
  
  
  
  
