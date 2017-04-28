{-# OPTIONS --exact-split #-}

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
