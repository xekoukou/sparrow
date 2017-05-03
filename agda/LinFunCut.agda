{-# OPTIONS --exact-split #-}
-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS --show-irrelevant #-}

module LinFunCut where

open import Common
open import LinLogic
open import IndexLLProp
open import LinDepT
open import LinT 
open import SetLL
open import SetLLProp
open import SetLLRem
open import LinFun
open import IndexLF
open import IndexLFCo
open import LinLogicProp

open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Maybe hiding (map)
open import Category.Monad


-- Some simple properties of Natural numbers that are missing from agda-stdlib
module _ where

  _≤un_ : {a : ℕ} → {b : ℕ} → (c : (a ≤ b)) → (d : (a ≤ b)) → c ≡ d  
  z≤n ≤un z≤n = refl
  s≤s c ≤un s≤s d with ( c ≤un d )
  s≤s c ≤un s≤s .c | refl = refl

  ≤rsuc : {a : ℕ} → {b : ℕ} → (a ≤ b) → a ≤ suc b
  ≤rsuc z≤n = z≤n
  ≤rsuc (s≤s x) = s≤s $ ≤rsuc x


-- Finding all the reachable Coms and then removing all the unnecessary ones might not be efficient. The code becomes simple though.
findComs : ∀{i u ll rll} → (lf : LFun {i} {u} ll rll) → MSetLFCof lf
findComs {i} {u} I = ∅
findComs {i} {u} (lf ⊂ lf₁) with (findComs lf) | findComs lf₁
findComs {i} {u} (lf ⊂ lf₁) | ∅ | ∅ = ∅
findComs {i} {u} (lf ⊂ lf₁) | ∅ | ¬∅ x = ¬∅ (⊂→ x)
findComs {i} {u} (lf ⊂ lf₁) | ¬∅ x | ∅ = ¬∅ (x ←⊂)
findComs {i} {u} (lf ⊂ lf₁) | ¬∅ x | (¬∅ x₁) = ¬∅ (x ←⊂→ x₁)
findComs {i} {u} (tr ltr lf) with (findComs lf)
findComs {i} {u} (tr ltr lf) | ∅ = ∅
findComs {i} {u} (tr ltr lf) | ¬∅ x = ¬∅ (tr x)
findComs {i} {u} (com df lf) = ¬∅ ↓
findComs {i} {u} (call x) = ∅ 


module _ {u : Level} where

  open import Data.List

  private
    tranLFMSetLL : ∀{i ll rll} → (lf : LFun {i} {u} ll rll) → MSetLL ll → MSetLL rll
    tranLFMSetLL lf ∅ = ∅
    tranLFMSetLL I (¬∅ x) = ¬∅ x
    tranLFMSetLL (_⊂_ {ind = ind} lf lf₁) (¬∅ x) = tranLFMSetLL lf₁ nmx where
      tlf = tranLFMSetLL lf (truncSetLL x ind)
      nmx = mreplacePartOf (¬∅ x) to tlf at ind
    tranLFMSetLL (tr ltr lf) (¬∅ x) = tranLFMSetLL lf (¬∅ (SetLL.tran x ltr))
    tranLFMSetLL (com df lf) (¬∅ x) = IMPOSSIBLE -- We should never reach at this point. findComs should have added the com in SetLFCof , and thus we should have already removed the memory.
    tranLFMSetLL (call x) (¬∅ x₁) = IMPOSSIBLE -- Calls that externally reached have been removed.


-- Returns the set of IndexLFCof that is reachable from outside. All inputs are present for each com.
  comsWithAllInputs : ∀{i ll rll} → (lf : LFun {i} {u} ll rll) → MSetLL ll → SetLFCof lf → MSetLFCof lf
  comsWithAllInputs lf ∅ sc = ∅
  comsWithAllInputs I (¬∅ s) ()
  comsWithAllInputs (_⊂_ {ind = ind} lf lf₁) (¬∅ s) (sc ←⊂) = (case n of (λ { ∅ → ∅ ; (¬∅ x) → ¬∅ (x ←⊂) })) where
    n = comsWithAllInputs lf (truncSetLL s ind) sc
  comsWithAllInputs (_⊂_ {ind = ind} lf lf₁) (¬∅ s) (⊂→ sc) = (case n of (λ { ∅ → ∅ ; (¬∅ x) → ¬∅ (⊂→ x) })) where
    ns = mreplacePartOf (¬∅ s) to (tranLFMSetLL lf (truncSetLL s ind)) at ind
    n = comsWithAllInputs lf₁ ns sc
  comsWithAllInputs (_⊂_ {ind = ind} lf lf₁) (¬∅ s) (sc ←⊂→ sc₁) = hf fn sn where
    fn = comsWithAllInputs lf (truncSetLL s ind) sc
    -- Since SetLFCof only leads us to coms, we remove the part of the SetLL that was in ←⊂. 
    ns = mreplacePartOf (¬∅ s) to ∅ at ind
    sn = comsWithAllInputs lf₁ ns sc₁
    hf : MSetLFCof lf → MSetLFCof lf₁ → MSetLFCof (_⊂_ {ind = ind} lf lf₁)
    hf ∅ ∅ = ∅
    hf ∅ (¬∅ x) = ¬∅ (⊂→ x)
    hf (¬∅ x) ∅ = ¬∅ (x ←⊂)
    hf (¬∅ x) (¬∅ x₁) = ¬∅ (x ←⊂→ x₁)
  comsWithAllInputs (tr ltr lf) (¬∅ s) (tr sc) = (case n of (λ { ∅ → ∅ ; (¬∅ x) → ¬∅ (tr x) }) ) where
    n = comsWithAllInputs lf (¬∅ (SetLL.tran s ltr)) sc
  comsWithAllInputs (com df lf) (¬∅ s) ↓ with (contruct s)
  comsWithAllInputs (com df lf) (¬∅ s) ↓ | ↓ = ¬∅ ↓
  {-# CATCHALL #-}
  comsWithAllInputs (com df lf) (¬∅ s) ↓ | r = ∅
  comsWithAllInputs (call x) (¬∅ s) ()


  open RawMonad {f = lsuc u} (Data.Maybe.monad)

  
  -- We check that the IndexLFCofs we found from comsWithAllInputs are actually IndexLFCos
  -- IMPORTANT This should always be as such, thus we put IMPOSSIBLE on the other case.

  turnToCo : ∀{i ll rll} → (lf : LFun {i} {u} ll rll) → IndexLFCof lf → Maybe (Σ (LinLogic i {u}) (λ cll → Σ (LinLogic i {u}) (λ frll → Σ (IndexLL cll ll) (λ ind → IndexLFCo {i} {u} {cll} frll ind lf))))
  turnToCo I ()
  turnToCo (_⊂_ {ind = ind} lf lf₁) (ic ←⊂) = n >>= λ {(cll , frll , lind , ico) → return (cll , frll , ind +ᵢ lind , ico ←⊂ )} where
    n = turnToCo lf ic
  turnToCo (_⊂_ {ind = ind} lf lf₁) (⊂→ ic) = n >>= λ {(cll , frll , lind , ico) → getIndRevNoComsT ind lind lf >>= λ irnc → return (cll , frll , indRevNoComs ind lind lf irnc , (⊂→ ico) irnc )} where
    n = turnToCo lf₁ ic
  turnToCo (tr ltr lf) (tr ic) = n >>= λ {(cll , frll , ind , ico) → (hf ind (revTr ltr)) >>= (λ lut → return (cll , frll , IndexLLProp.tran ind (revTr ltr) (lower lut) , tr ico (lower lut)))  } where
    n = turnToCo lf ic
    hf : ∀ {i ll pll rll} → (ind : IndexLL pll ll) → (ltr : LLTr {i} {u} rll ll) → Maybe (Lift {ℓ = lsuc u} (UpTran ind ltr))
    hf ind ltr with (isUpTran ind ltr)
    hf ind ltr | yes p = just (lift p)
    hf ind ltr | no ¬p = nothing
  turnToCo (com {ll = cll} {frll = frll} df lf) ↓ = just (cll , frll , ↓ , ↓)
  turnToCo (call x) ()
  

  toListCof : ∀{i ll rll} → (lf : LFun {i} {u} ll rll) → SetLFCof lf → List (IndexLFCof lf)
  toListCof I ()
  toListCof (lf ⊂ lf₁) (s ←⊂) = map (λ x → x ←⊂) n where
    n = toListCof lf s
  toListCof (lf ⊂ lf₁) (⊂→ s) = map (λ x → ⊂→ x) n where
    n = toListCof lf₁ s 
  toListCof (lf ⊂ lf₁) (s ←⊂→ s₁) = (map (λ x → x ←⊂) ln) ++ (map (λ x → ⊂→ x) rn) where
    ln = toListCof lf s
    rn = toListCof lf₁ s₁
  toListCof (tr ltr lf) (tr s) = map (λ x → tr x) n where
    n = toListCof lf s
  toListCof (com df lf) ↓ =  Data.List.[ ↓ ]
  toListCof (call x) ()

  turnAllToCo : ∀{i ll rll} → {lf : LFun {i} {u} ll rll} → MSetLFCof lf → MSetLFCoRem lf ll
  turnAllToCo ∅ = ∅
  turnAllToCo {i} {ll} {lf = lf} (¬∅ x) = foldl hf ∅ (map (turnToCo lf) (toListCof lf x)) where
    hf : MSetLFCoRem lf ll → Maybe (Σ (LinLogic i) (λ cll → Σ (LinLogic i)
         (λ frll → Σ (IndexLL cll ll) (λ ind → IndexLFCo frll ind lf))))
         → MSetLFCoRem lf ll
    hf ms (just (cll , frll , ind , ic)) = maddLFCoRem ms ind ic
    hf ms nothing = IMPOSSIBLE   -- turnToCo should always return just x




nextComs :  ∀{i u ll rll} → (lf : LFun {i} {u} ll rll) → MSetLFCoRem lf ll
nextComs lf with (findComs lf)
nextComs lf | ∅ = ∅
nextComs {ll = ll} lf | ¬∅ sc with (comsWithAllInputs lf (¬∅ (fillAllLower ll)) sc)
... | g = turnAllToCo g






removeCom : ∀{i u ll rll cll frll} → {ind : IndexLL cll ll} → (lf : LFun {i} {u} ll rll) → (ic : IndexLFCo frll ind lf) → LFun {i} {u} (replLL ll ind frll) rll
removeCom I ()
removeCom {ll = ll} {rll = rll} {frll = frll} (_⊂_ {ell = ell} {ind = ind} lf lf₁) (_←⊂ {lind = lind} ic) with (replLL ll ind ell) | (replLL-a≤b≡a ind ell (ind +ᵢ lind) frll (+ᵢ⇒l≤ᵢ+ᵢ ind lind))
... | .(replLL (replLL ll (ind +ᵢ lind) frll) (a≤ᵢb-morph ind (ind +ᵢ lind) frll (+ᵢ⇒l≤ᵢ+ᵢ ind lind)) ell) | refl
        with (a≤ᵢb-morph ind (ind +ᵢ lind) frll (+ᵢ⇒l≤ᵢ+ᵢ ind lind))
... | r with (((ind +ᵢ lind) -ᵢ ind) (+ᵢ⇒l≤ᵢ+ᵢ ind lind)) | ([a+b]-a=b ind lind)
... | g | refl = _⊂_ {ind = r} n lf₁ where
  n = removeCom lf ic
removeCom {i} {u} {ll} {cll = cll} {frll = frll} (_⊂_ {pll = pll} {ell = ell} {ind = ind} .I lf₁) ((⊂→_ {lind = lind} ic) (c1 ltul cr1)) -- ell = pll here
    = _⊂_ {pll = replLL pll (rvThf ind x) frll} {ind = hf x uind eq₁ (hf₂ (a≤ᵢb-morph uind lind frll ltul))} I {!uind!} where -- lind
  n = removeCom lf₁ ic
  uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind)
  x = (lind -ᵢ uind) ltul
  eq₁ = replLL-↓ {ell = ell} ind 
  t₁ = replLL pll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) ell
  rvThf` : {t : LinLogic i {u}} → (eq : t ≡ ell) → (x : IndexLL cll t) → IndexLL cll ell
  rvThf` eq x = subst (λ x → x) (cong (λ x → IndexLL cll x) eq) x
  hf : {t : LinLogic i {u}} → (x : IndexLL cll t) → (uind : IndexLL t (replLL ll ind pll)) → (eq : t ≡ ell)
       → IndexLL
         (replLL t
           x frll)
         (replLL (replLL ll ind pll) (uind +ᵢ x) frll)
       →  IndexLL
            (replLL pll (rvThf` eq x) frll)
            (replLL ll (ind +ᵢ (rvThf` eq x)) frll)
  hf x uind refl = {!!}

  hf₂ : IndexLL
          (replLL t₁ x frll)
          (replLL (replLL ll ind pll) lind frll)
        → IndexLL
            (replLL t₁ x frll)
            (replLL (replLL ll ind pll) (uind +ᵢ x) frll)
  hf₂ w with (uind +ᵢ x) | (a+[b-a]=b uind lind ltul)
  hf₂ w | g | refl = w

removeCom (_⊂_ {ind = ind} .(elf ⊂ elf₁) lf₁) ((⊂→ ic) (c1 ltul (cr2 {lf₁ = elf₁} {lf = elf} x ltuindx x₁))) = {!!}
removeCom (_⊂_ {ind = ind} .(elf ⊂ elf₁) lf₁) ((⊂→ ic) (c1 ltul (cr3 {lf₁ = elf₁} {lf = elf} x nord))) = {!!}
removeCom (_⊂_ {ind = ind} .(tr ltr elf) lf₁) ((⊂→ ic) (c1 ltul (cr4 {lf = elf} {ltr = ltr} x x₁))) = {!!}
removeCom {ll = ll} {rll = rll} {frll = frll} (_⊂_ {ell = ell} {ind = ind} lf lf₁) ((⊂→_ {lind = lind} ic) (c2 nord)) = _⊂_ {ind = ¬ord-morph ind (lemma₁-¬ord-a≤ᵢb ind ind ell (≤ᵢ-reflexive ind) lind (flipNotOrdᵢ nord)) frll (flipNotOrdᵢ (rlemma₁⇒¬ord ind ind ell (≤ᵢ-reflexive ind) lind (flipNotOrdᵢ nord)))} lf hf where
  n = removeCom lf₁ ic
  hf : LFun (replLL
       (replLL ll
        (lemma₁-¬ord-a≤ᵢb ind ind ell (≤ᵢ-reflexive ind) lind (flipNotOrdᵢ nord)) frll)
       (¬ord-morph ind
        (lemma₁-¬ord-a≤ᵢb ind ind ell (≤ᵢ-reflexive ind) lind (flipNotOrdᵢ nord)) frll (flipNotOrdᵢ (rlemma₁⇒¬ord ind ind ell (≤ᵢ-reflexive ind) lind (flipNotOrdᵢ nord))))
       ell) rll
       -- I am kicking ass, that's what I am doing...
  hf =  subst (λ x → x)
         (trans
           (sym (cong (λ x → LFun (replLL (replLL ll kemi ell) x frll) rll) (¬ord-morph$lemma₁≡I ell ind ind (≤ᵢ-reflexive ind) lind nord)))
           (sym (cong (λ x → LFun x rll) (replLL-¬ordab≡ba kemi ell kind frll knord)))
         ) n  where
    kind = lemma₁-¬ord-a≤ᵢb ind ind ell (≤ᵢ-reflexive ind) lind (flipNotOrdᵢ nord)
    kemi = ind
    knord = flipNotOrdᵢ (rlemma₁⇒¬ord ind ind ell (≤ᵢ-reflexive ind) lind (flipNotOrdᵢ nord))
removeCom (tr ltr lf) (tr ic ut) = tr {!ltr!} n where
  n = removeCom lf ic
removeCom (com df lf) ↓ = lf
removeCom (call x) ()



