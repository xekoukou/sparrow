-- {-# OPTIONS --show-implicit #-}

module LinFunCut where

open import Common
open import LinLogic
open import LinDepT
open import LinT 
open import SetLL
open import SetLLProp
open import SetLLRem
open import LinFun
open import IndexLF

open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Maybe


-- Some simple properties of Natural numbers that are missing from agda-stdlib
module _ where

  _≤un_ : {a : ℕ} → {b : ℕ} → (c : (a ≤ b)) → (d : (a ≤ b)) → c ≡ d  
  z≤n ≤un z≤n = refl
  s≤s c ≤un s≤s d with ( c ≤un d )
  s≤s c ≤un s≤s .c | refl = refl

  ≤rsuc : {a : ℕ} → {b : ℕ} → (a ≤ b) → a ≤ suc b
  ≤rsuc z≤n = z≤n
  ≤rsuc (s≤s x) = s≤s $ ≤rsuc x

-- This function should be used after we have removed the specific com, the transformations, and the calls.
-- It is to be used to find the next coms that are available.

nextComs : ∀{i u ll rll} → (olf : LFun {i} {u} ll rll) → MSetLFRem olf ll
nextComs {i} {u} {ll = ll} olf = proj₂ $ nextComs` olf (λ x → x) (¬∅ (fillAllLowerRem ll) , ∅) where
  nextComs` : ∀{oll ll rll} → (lf : LFun {i} {u} ll rll) → (IndexLF lf → IndexLF olf) → MSetLLRem {i} oll ll × MSetLFRem olf oll → MSetLLRem oll rll × MSetLFRem olf oll
  nextComs` I if (sr , s) = (sr , s)
  nextComs` (_⊂_ {ell = ell} {ind = ind} lf lf₁) if (sr , s) with (truncSetLLRem sr ind) 
  ... | r = let (esr , es) = nextComs` lf (λ x → if (x ←⊂)) (r , s)
            in nextComs` lf₁ (λ x → if (⊂→ x)) (mreplaceRem ind esr sr , es)
  nextComs` (tr ltr lf) if (∅ , s) = ( ∅ , s) 
  nextComs` (tr ltr lf) if (¬∅ x , s) = nextComs` lf (λ x → if (tr x)) ((¬∅ $ tranRem x ltr) , s)
  nextComs` (com {ll = _} {frll} df lf) if (∅ , s) = (∅ , s)
  nextComs` (com {ll = _} {frll} df lf) if (¬∅ x , s) with (contruct $ projToSetLL x)
  nextComs` (com {_} {_} {frll} df lf) if (¬∅ x , s) | ↓ with (msetToIndex (mcontruct $ reConSet x))
  nextComs` (com {_} {_} {frll} df lf) if (¬∅ x , s) | ↓ | (just (_ , ind)) = (∅ , maddLFRem s ind (if ↓))
  nextComs` (com {_} {_} {frll} df lf) if (¬∅ x , s) | ↓ | nothing = IMPOSSIBLE -- This leads to a unique ↓ because we have cleaned the transformations.
  nextComs` (com {_} {_} {frll} df lf) if (¬∅ x , s) | r = (∅ , s)
  nextComs` (call x) if (∅ , s) = (∅ , s)
  nextComs` (call x) if (¬∅ x₁ , s) = IMPOSSIBLE -- Since we have removed all calls that are reached from the outside, this is impossible. 


-- Maybe we need to replace IndexLFCo and s with something better in the future. TODO
removeCom : ∀{i u ll rll cll frll s} → (lf : LFun {i} {u} ll rll) → (ic : IndexLFCo cll frll s lf) → let (_ , ind) = pickOne s in LFun {i} {u} (replLL ll ind frll) rll
removeCom I ()
removeCom (_⊂_ elf lf) ic = {!!}
removeCom (tr ltr lf) (tr ic) with (removeCom lf ic)
... | r = tr {!!} {!!}
removeCom (com df lf) ↓ = lf
removeCom (call x) ()

-- Here we have removed the com, but not the transformations or calls.We need to find the next available coms so as to remove the
-- transformations that will make it a single ↓. Also, we need to find if there are calls that are reachable from the outside.

-- See WellFormed. We check that the external/main LinFun has no calls, thus oneElemRem will not pick a "↓c" (memory for call since they do not exist). IMPORTANT. TODO
--nextComsCalls : ∀{i u oll ll} → ∀{rll} → LFun {i} {u} ll rll → MSetLLRem {i} oll ll × MSetLLRem {i} oll ll × MSetLL oll × MSetLL oll → MSetLLRem {i} oll rll × MSetLLRem oll rll × MSetLL oll × MSetLL oll
--nextComsCalls I (cm , sr , s , sc) = (cm , sr , s , sc)
--nextComsCalls (_⊂_ {ell = ell} {ind = ind} lf lf₁) (cm , sr , s , sc) with (truncSetLLRem cm ind) | (truncSetLLRem sr ind) 
--... | c | r = let (ecm , esr , es , esc) = nextComsCalls lf (c , r , s , sc)
--          in nextComsCalls lf₁ (mreplaceRem ind ecm cm , mreplaceRem ind esr sr , es , esc)
--nextComsCalls (tr ltr lf) (cm , ∅ , s , sc) = (∅ , ∅ , s , sc) 
--nextComsCalls (tr ltr lf) (∅ , ¬∅ x , s , sc) = nextComsCalls lf (∅ , (¬∅ $ tranRem x ltr) , s , sc)
--nextComsCalls (tr ltr lf) (¬∅ cx , ¬∅ x , s , sc) = nextComsCalls lf ((¬∅ $ tranRem cx ltr) , (¬∅ $ tranRem x ltr) , s , sc)
--nextComsCalls (com {ll = _} {frll} df lf) (∅ , ∅ , s , sc) = (∅ , ∅ , s , sc)
--nextComsCalls (com {ll = _} {frll} df lf) (¬∅ cx , ∅ , s , sc) = IMPOSSIBLE
--nextComsCalls (com {ll = _} {frll} df lf) (cm , ¬∅ x , s , sc) with (contruct $ projToSetLL x)
--nextComsCalls (com {_} {_} {frll} df lf) (∅ , ¬∅ x , s , sc) | ↓ = {!!}
--nextComsCalls (com {rll} {_} {frll} df lf) (¬∅ x₁ , ¬∅ x , s , sc) | ↓ = (∅ , ¬∅ (fillAllLowerRem rll) , (s ∪ₘₛ (mcontruct $ reConSet x)) , sc) -- Since we haven't cleaned the transf, the mcontruct will not result on unique ↓. After we do the transformations, it should. IMPORTANT TODO.
--... | r = (∅ , ∅ , s , sc)
--nextComsCalls (call x) (∅ , ∅ , s , sc) = (∅ , ∅ , s , sc)
--nextComsCalls (call x) (¬∅ cx , ∅ , s , sc) = IMPOSSIBLE
--nextComsCalls {i = i} {u = u} {oll = oll} {rll = rll} (call x) (∅ , ¬∅ x₁ , s , sc) = hf (oneElemRem x₁) where
--  hf : Σ (LinLogic i {u}) (λ rll → IndexLL rll oll) → MSetLLRem oll rll × MSetLLRem oll rll × MSetLL oll × MSetLL oll
--  hf (rll , ind) with (replLL oll ind rll) | (madd {q = rll} sc ind rll) | (replLL-id oll ind rll refl)
--  hf (rll , ind) | r | g | refl = (∅ , ∅ , s , g) -- Here we pick only one element from the memory and add it
---- to MSetLL oll.
--nextComsCalls (call x) (¬∅ cx , ¬∅ x₁ , s , sc) = IMPOSSIBLE
--



---- See WellFormed. We check that the external/main LinFun has no calls, thus oneElemRem will not pick a "↓c" (memory for call since they do not exist). IMPORTANT. TODO
--nextComsCalls : ∀{i u oll ll} → ∀{rll} → LFun {i} {u} ll rll → MSetLLRem {i} oll ll × MSetLL oll × MSetLL oll → MSetLLRem oll rll × MSetLL oll × MSetLL oll
--nextComsCalls I (sr , s , sc) = (sr , s , sc)
--nextComsCalls (_⊂_ {ell = ell} {ind = ind} lf lf₁) (sr , s , sc) with (truncSetLLRem sr ind) 
--... | r = let (esr , es , esc) = nextComsCalls lf (r , s , sc)
--          in nextComsCalls lf₁ (mreplaceRem ind esr sr , es , esc)
--nextComsCalls (tr ltr lf) (∅ , s , sc) = ( ∅ , s , sc) 
--nextComsCalls (tr ltr lf) (¬∅ x , s , sc) = nextComsCalls lf ((¬∅ $ tranRem x ltr) , s , sc)
--nextComsCalls (com {ll = _} {frll} df lf) (∅ , s , sc) = (∅ , s , sc)
--nextComsCalls (com {ll = _} {frll} df lf) (¬∅ x , s , sc) with (contruct $ projToSetLL x)
--... | ↓ = (∅ , (s ∪ₘₛ (mcontruct $ reConSet x)) , sc) -- Since we haven't cleaned the transf, the mcontruct will not result on unique ↓. After we do the transformations, it should. IMPORTANT TODO.
--... | r = (∅ , s , sc)
--nextComsCalls (call x) (∅ , s , sc) = (∅ , s , sc)
--nextComsCalls {i = i} {u = u} {oll = oll} {rll = rll} (call x) (¬∅ x₁ , s , sc) = hf (oneElemRem x₁) where
--  hf : Σ (LinLogic i {u}) (λ rll → IndexLL rll oll) → MSetLLRem oll rll × MSetLL oll × MSetLL oll
--  hf (rll , ind) with (replLL oll ind rll) | (madd {q = rll} sc ind rll) | (replLL-id oll ind rll refl)
--  hf (rll , ind) | r | g | refl = (∅ , s , g) -- Here we pick only one element from the memory and add it
---- to MSetLL oll.
--




-- Here we assume that cut removes call and obs as soon as the call is possible to be executed,
-- thus if we reach at a call, we do not continue, it means that this specific subtree will not contain a com
-- to execute this communication pattern.



data fS {u} (A : Set (lsuc u)) : Set (lsuc u) where
  fYes : A → fS A
  fNo : fS A

-- We need to return
-- A) the remaining set of inputs
-- B) the computed usesInputs with the inputs that have been found to be used.
-- C) the set of calls that have been unfolded.

-- If the usesInput is not complete, we remove the embedding, we insert the contents of the embedding to the parent and use its computed usesInput for these contents, continuing in the parent embedding.


--cut : {i : Size} → {j : Size< i}  → {k : Size< ↑ i} → ∀{u rll ll} → (s : SetLL ll) → (lf : LFun {u} {i} {k} {rll} {ll}) → cuttable s lf → usesInputT lf
--      → fS ( Σ (LinLogic i) (λ dll → Σ (LFun {u} {i} {k} {rll} {dll}) (λ lf → usesInputT lf)) )
--cut s lf c (usesInputC ui) = cut` s lf c ui where
--  cut` : {i : Size} → {j : Size< i}  → {k : Size< ↑ i} → ∀{u rll ll} → (s : SetLL ll) → (lf : LFun {u} {i} {k} {rll} {ll}) → cuttable s lf → ∀{ms} → usesInputT` lf ms
--        → fS ( Σ (LinLogic i) (λ dll → Σ (LFun {u} {i} {k} {rll} {dll}) (λ lf → usesInputT lf)) )
--  cut` s I () ui
--  cut` s (elf ⊂ lf) (cuttable-s⊂-oi c) ui = {!!}
--  cut` s (elf ⊂ lf) (cuttable-s⊂-¬ho c) ui = {!!}
--  cut` s plf@(tr lf) (cuttable-s-tr-fst c) ui = {!!}
--  cut` s plf@(tr lf) (cuttable-s-tr-snd c) ui = {!!}
--  cut` s (obs lf) () ui
--  cut` s plf@(com df lf) cuttable-s-com ui with (doesItUseAllInputs lf)
--  cut` s (com df lf) cuttable-s-com ui | yes p = fYes (_ , lf , p)
--  cut` s (com df lf) cuttable-s-com ui | no ¬p = fNo
--  cut` s (call x) () ui
--

--module _ where
--
--private
--  hf : {i : Size} → {j : Size< i}  → {k : Size< ↑ i} → ∀{u rll ll} → MSetLL ll → (lf : LFun {u} {i} {k} {rll} {ll}) → ∀{ms} → usesInputT` lf ms
--       → (MSetLL rll) × ( Σ (LinLogic i) (λ dll → Σ (LFun {u} {i} {k} {rll} {dll}) (λ lf → usesInputT lf)) )
--  hf {ll = ll} ms I ui = {!!} 
--  hf ms (lf ⊂ lf₁) ui = {!!}
--  hf ms (tr lf) ui = {!!}
--  hf ms (obs lf) ui = {!!}
--  hf ms (com df lf) ui = {!!}
--  hf ms (call x) ui = {!!}
--
--  removeCalls : {i : Size} → {j : Size< i}  → {k : Size< ↑ i} → ∀{u rll ll} → (s : SetLL ll) → (lf : LFun {u} {i} {k} {rll} {ll}) → cuttable s lf → usesInputT lf
--        → fS ( Σ (LinLogic i) (λ dll → Σ (LFun {u} {i} {k} {rll} {dll}) (λ lf → usesInputT lf)) )
--  removeCalls s lf c (usesInputC ui) = removeCalls` s lf c ui where
--    removeCalls` : {i : Size} → {j : Size< i}  → {k : Size< ↑ i} → ∀{u rll ll} → (s : SetLL ll) → (lf : LFun {u} {i} {k} {rll} {ll}) → cuttable s lf → ∀{ms} → usesInputT` lf ms
--          → fS ( Σ (LinLogic i) (λ dll → Σ (LFun {u} {i} {k} {rll} {dll}) (λ lf → usesInputT lf)) )
--    removeCalls` s I () ui
--    removeCalls` s (elf ⊂ lf) (cuttable-s⊂-oi c) ui = {!!}
--    removeCalls` s (elf ⊂ lf) (cuttable-s⊂-¬ho c) ui = {!!}
--    removeCalls` s plf@(tr lf) (cuttable-s-tr-fst c) ui = {!!}
--    removeCalls` s plf@(tr lf) (cuttable-s-tr-snd c) ui = {!!}
--    removeCalls` s (obs lf) () ui
--    removeCalls` s plf@(com df lf) cuttable-s-com ui = {!!}
--    removeCalls` s (call x) () ui
--


-- Important : We need to introduce a null data point like Unit, that serves to express the dependency between events. 
-- We prohibit LFun Calls that do not depend on a previous com.

-- We remove all the calls who have one of their inputs received and replace them with LFun.
-- We add obs to all the other calls that did not trigger the unfolding and then an embedding of the LFun with ⊂. We use the "usesInput" that is created by step.

-- By removing the calls , the usesInput of the main function is preserved.
-- We also unfold all calls that depend on the call of this call. These are finite by definition of LFun (being inductive data type).

--  mutual
  -- We use this when we compute the next LFun and the next output, thus the size is allowed to be lowered by one.
--    removeCall : {i : Size} → {j : Size< i}  → {k : Size< ↑ i} → ∀{u rll ll} → LFun {u} {i} {k} {rll} {ll} → LFun {u} {i} {k} {rll} {ll}
--    removeCall I = I
--    removeCall (_⊂_ {ind = ind} lf lf₁) = {!!} -- _⊂_ {ind = ind} (removeCall lf) {{prf = prf}} (removeCall lf₁)  -- We need to only remove call that do not depend on a previous com.
--    removeCall (tr lf) = tr $ removeCall lf
--    removeCall (obs lf) = {!!}
--    removeCall (com df lf) = com df $ lf
--    removeCall (call ∞lf lf₁) = {!!} -- let st = step ∞lf in
--      {!!} -- _⊂_ {ind = ↓} (proj₁ st) {{prf = proj₂ st}} (removeCall lf₁) 
--
--    usesInput→usesInput$removeCall : {i : Size} → {j : Size< i } → {k : Size< ↑ i} → ∀{u rll ll} → (lf : LFun {u} {i} {k} {rll} {ll}) → usesInput lf ≡ ⊤ → usesInput (removeCall lf) ≡ ⊤
--    usesInput→usesInput$removeCall I prf = prf
--    usesInput→usesInput$removeCall (lf ⊂ lf₁) prf = {!!}
--    usesInput→usesInput$removeCall (tr lf) prf = {!!}
--    usesInput→usesInput$removeCall (obs lf) prf = {!!}
--    usesInput→usesInput$removeCall (com df lf) prf = {!!}
--    usesInput→usesInput$removeCall (call x lf) prf = {!!}
--    





--  cut : ∀{i u} → {j : Size< ↑ i} → ∀{rll ll} → {s : SetLL ll} → {lf : LFun} → cuttable {u} {i} {j} {rll} s lf
--  cut c = {!!}








module _ where

-- cll is the linear logic that is introduced after the last Com.
-- The indoi points us to the last transformation of the LinLogic, the last place we received data.
-- We need to preserve the ∨(or) choices of the previous inputs.
  mutual
    data Spec :  {i : Size} → ∀{u ll rll} → LinDepT ll → LFun {i} {u} ll rll → Set where  


--  canBeCut : ∀{i} → {j : Size< ↑ i} → ∀{u rll ll} → SetLL ll → LFun {u} {i} {j} {rll} {ll} → Bool × LinLogic j {u}
    data Input {u} : {i : Size} → ∀{rll ll} →  LinDepT ll → LFun {i} {u} ll rll → Set (lsuc u) where
--      I    : {i : Size} {j : Size< ↑ i} → ∀{rll ll ldt lf} → ⦃ prf : nextLFun {i} {j} {u} {rll} {ll} lf ≡ I ⦄ → Input {rll = rll} ldt lf
--      next : {i : Size} {j : Size< ↑ i} → ∀{rll ll ldt lf} → (s : SetLL ll) → let cbc = canBeCut s lf in LinT (proj₂ cbc) → ⦃ prf : nextLFun {i} {j} {u} {rll} {ll} lf ≡ com ⦄ → Input {u} {i} {j} {rll} {ll} ldt lf
--      next : in → Input → Input
--      call : ∞input → Input → Input

--    record ∞Input {i u ll ∞rll} ( ldt : LinDepT ll) ( ∞lf : ∞LFun {i} {u} {∞rll} {ll}) : Set (suc u) where
--      coinductive
--      field
--        step : {j : Size< i} → Input {u} {i = i} {j = j} {rll = step ∞rll} {ll} ldt ((step ∞lf) {j = j})
--


-- As soon as all the inputs of a specific LFun has been received and the resulst is ∅ for all except an embedding, we replace the linear function with that embedding.
