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
open import Data.Product
open import Data.Nat
open import Data.Maybe
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
    tranLFMSetLLRem : ∀{i oll ll rll} → (lf : LFun {i} {u} ll rll) → MSetLLRem oll ll → MSetLLRem oll rll
    tranLFMSetLLRem lf ∅ = ∅
    tranLFMSetLLRem I (¬∅ x) = ¬∅ x
    tranLFMSetLLRem (_⊂_ {ind = ind} lf lf₁) (¬∅ x) = tranLFMSetLLRem lf₁ nmx where
      tlf = tranLFMSetLLRem lf (truncSetLLRem (¬∅ x) ind)
      nmx = mreplaceRem ind tlf (¬∅ x)
    tranLFMSetLLRem (tr ltr lf) (¬∅ x) = tranLFMSetLLRem lf (¬∅ (tranRem x ltr))
    tranLFMSetLLRem (com df lf) (¬∅ x) = IMPOSSIBLE -- ? I doubt that we will ever reach at this point. The set will be empty due to returnNext emptying it.
    tranLFMSetLLRem (call x) (¬∅ x₁) = IMPOSSIBLE -- We have removed all such coms.
  
  open RawMonad {f = lsuc u} (Data.Maybe.monad)

  -- Returns the next IndexLF that is not shadowed by other coms.
  -- It also returns the IndexLL to the external LinLogic that is the input of that com.
  -- TODO We have not proved and thus assume that the IndexLFCof we find here can always be proved to be IndexLFCo.
  -- If that assumption is correct, then the returning LinLogic will be removed from the MSetLLRem.
  -- It also returns the reduced SetLFCof. (multiple removals could have been made).
  returnNext : ∀{i oll ll rll} → (lf : LFun {i} {u} ll rll) → MSetLLRem oll ll → SetLFCof lf → Maybe ((Σ (LinLogic i {u}) (λ rll → IndexLL rll oll)) × MSetLFCof lf × IndexLFCof lf)
  returnNext lf ∅ s = nothing
  returnNext I (¬∅ sr) ()
  returnNext (_⊂_ {ind = ind} lf lf₁) (¬∅ sr) (s ←⊂) = n >>=  λ { (nl , (¬∅ ns) , nic) → return (nl , (¬∅ (ns ←⊂)) , (nic ←⊂))
                                                           ; (nl , ∅ , nic) → return (nl , ∅ , (nic ←⊂))}                  where
    n = returnNext lf (truncSetLLRem (¬∅ sr) ind) s
  returnNext (_⊂_ {ind = ind} lf lf₁) (¬∅ sr) (⊂→ s) = n >>=  λ { (nl , (¬∅ ns) , nic) → return (nl , ¬∅ (⊂→ ns) , (⊂→ nic))
                                                           ; (nl , ∅ , nic) → return (nl , ∅ , (⊂→ nic))}                  where
    ns = mreplaceRem ind (tranLFMSetLLRem lf (truncSetLLRem (¬∅ sr) ind)) (¬∅ sr)
    n = returnNext lf₁ ns s
  returnNext (_⊂_ {ind = ind} lf lf₁) (¬∅ sr) (s ←⊂→ s₁) with (returnNext lf (truncSetLLRem (¬∅ sr) ind) s)
  returnNext (_⊂_ {ind = ind} lf lf₁) (¬∅ sr) (s ←⊂→ s₁) | just (nl , ¬∅ ns , nic) = just ((nl , ¬∅ (ns ←⊂→ s₁) , nic ←⊂))
  returnNext (_⊂_ {ind = ind} lf lf₁) (¬∅ sr) (s ←⊂→ s₁) | just (nl , ∅ , nic) = just ((nl , ¬∅ (⊂→ s₁) , nic ←⊂))
  returnNext (_⊂_ {ind = ind} lf lf₁) (¬∅ sr) (s ←⊂→ s₁) | nothing = n >>=  λ { (nl , (¬∅ ns) , nic) → return (nl , ¬∅ (⊂→ ns) , (⊂→ nic))
                                                                         ; (nl , ∅ , nic) → return (nl , ∅ , (⊂→ nic))}                  where
    ns = mreplaceRem ind (tranLFMSetLLRem lf (truncSetLLRem (¬∅ sr) ind)) (¬∅ sr)
    n = returnNext lf₁ ns s₁
  
  returnNext (tr ltr lf) (¬∅ x) (tr s) = n >>=  λ { (nl , (¬∅ ns) , nic) → return (nl , ¬∅ (tr ns) , (tr nic))
                                                  ; (nl , ∅ , nic) → return (nl , ∅ , (tr nic))}                  where
    n = returnNext lf (¬∅ (tranRem x ltr)) s
  returnNext (com {ll = _} {frll} df lf) (¬∅ x) ↓ with (contruct (projToSetLL x))
  returnNext (com {_} {_} {frll} df lf) (¬∅ x) ↓ | ↓ with (setToIndex (contruct (conSet x)))
  returnNext (com {_} {_} {frll} df lf) (¬∅ x) ↓ | ↓ | just r = just ( r , (∅ , ↓))
  returnNext (com {_} {_} {frll} df lf) (¬∅ x) ↓ | ↓ | nothing = IMPOSSIBLE -- IMPORTANT conSet x needs to be a single ↓ or our assumptions are wrong. -- setToIndex returns nothing if not.
  {-# CATCHALL #-}
  returnNext (com {_} {_} {frll} df lf) (¬∅ x) ↓ | r = nothing
  returnNext (call x) (¬∅ sr) ()
  
  -- We check that the IndexLFCof we found from returnNext is actually an IndexLFCo.
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
  

-- nextCom : ∀{i u ll rll} → (lf : LFun {i} {u} ll rll) → SetLFCof lf → IndexLF lf × (Σ (LinLogic i {u}) (λ cll → Σ (LinLogic i {u}) (λ frll → Σ (IndexLL cll ll) (λ ind → IndexLFCo {i} {u} {cll} frll ind lf))))
-- nextCom I ()
-- nextCom (lf ⊂ lf₁) (s ←⊂) = {!!}
-- nextCom (lf ⊂ lf₁) (⊂→ s) = {!!}
-- nextCom (lf ⊂ lf₁) (s ←⊂→ s₁) = {!!} -- Here We first pick on the lesft side and then we go on the right side, because there might be a com there that shadows further coms.
-- nextCom (tr ltr lf) (tr s) = {!!}
-- nextCom (com df lf) ↓ = {!!}
-- nextCom (call x) ()
