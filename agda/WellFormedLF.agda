-- {-# OPTIONS --show-implicit #-}

module WellFormedLF where

open import Common
open import LinLogic
open import SetLL
open import SetLLRem hiding (drsize)
open import LinFun
open import Data.Product

-- WellFormed
-- TODO Check that calls , _⊂_ and the main LFun use all inputs.



--data IndexLF : ∀{u} → {i : Size} → {j : Size< ↑ i} → {rll : LinLogic j {u}} → {ll : LinLogic i {u}} → LFun {u} {i} {j} {rll} {ll} → Set where
--  ↓    : {i : Size} → {j : Size< ↑ i} → ∀{u rll ll} → (lf : LFun {u} {i} {j} {rll} {ll}) → IndexLF lf
--  _←⊂_ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell ll ind elf prf lf}
--         → IndexLF elf
--         → IndexLF (_⊂_ {u} {i} {j} {k} {pll} {ll} {ell} {rll} {ind} elf {{prf}} lf)
--  _⊂→_ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell ll ind elf prf lf}
--         → IndexLF lf
--         → IndexLF (_⊂_ {u} {i} {j} {k} {pll} {ll} {ell} {rll} {ind} elf {{prf}} lf)
--  tr   : {i : Size} → {j : Size< ↑ i} → ∀{u ll orll rll} → {{ltr : LLTr orll ll}} → {lf : LFun {u} {i} {j} {rll} {orll}}
--         → IndexLF lf → IndexLF (tr {{ltr = ltr}} lf) 
--

--  _←⊂_ : {i : Size} → {j : Size< ↑ i} → {rll : LinLogic j {u}} → {ll : LinLogic i {u}} → (lf : LFun {u} {i} {j} {rll} {ll}) → IndexLF lf

--                                       ↓ probably the subtrees that contain all the inputs. 
-- We need to keep truck of all the latest subtrees that are outputs of coms. We can then check whether a transformation permutates them. If so , the tr is acceptable.
-- transformations inside a subtree are acceptable.
-- tranformations between two subtrees are only acceptable if the next com depends on both of them.
-- If more than one subtree depends on a specific subtree, but the two do not depend on each other, we first separate the elements for the first subtree and then for the other.
-- Since these coms can be independently executed, there can be tranformations of one subtree that can not be done while the others are ready. --> We remove the separation transformation and consider that
-- the unexecuted transformations are done on those separated elements.

-- > The input tree contains subtrees that represent exactly the input of the coms it can execute.

-- 2 TWO
-- We need three structures.
-- THe first is used to identify inputs from the same com. When a tranformation splits these coms, we also split the set into two sets. Next we track all the inputs that are part of the tranformation, be it sets of inputs of a specific com or individual inputs. From all these sets, at least one item from each set needs to be the input of the next com.
-- The set of coms that are used to allow for commutation of inputs.

module _ where

  open import Data.Vec

  mutual 
    data Descendant {u} : Set (lsuc u) where
      end  : Descendant
      dec  : ℕ → ∀{i ll} → SetLLD {i} {u} ll → Descendant
  
  
-- This set is full.    
    data SetLLD {i : Size} {u} : LinLogic i {u} → Set (lsuc u) where
      ↓∅    : Descendant {u}                   → SetLLD ∅
      ↓τ    : ∀{n} {dt : Vec (Set u) n} → {gT : genT dt } →
              Descendant {u}                   → SetLLD (τ gT)
      ↓c    : ∀{∞ll} → Descendant {u}          → SetLLD (call ∞ll)
      _←∧→_ : ∀{rs ls} → SetLLD ls → SetLLD rs → SetLLD (ls ∧ rs)
      _←∨→_ : ∀{rs ls} → SetLLD ls → SetLLD rs → SetLLD (ls ∨ rs)
      _←∂→_ : ∀{rs ls} → SetLLD ls → SetLLD rs → SetLLD (ls ∂ rs)
    
  
  
  data MSetLLD {i : Size} {u} : LinLogic i {u} → Set (lsuc u) where
    ∅   : ∀{ll}             → MSetLLD ll
    ¬∅  : ∀{ll} → SetLLD ll → MSetLLD ll
  
  -- TODO We shouldn't need this. When issue agda #2409 is resolved, remove this.
  drsize : ∀{i u ll} → {j : Size< ↑ i} → SetLLD {i} {u} ll → SetLLD {j} ll
  drsize (↓∅ mm)          = (↓∅ mm)
  drsize (↓τ mm)          = (↓τ mm)
  drsize (↓c mm)          = (↓c mm)
  drsize (x ←∧→ x₁) = (drsize x ←∧→ drsize x₁)
  drsize (x ←∨→ x₁) = (drsize x ←∨→ drsize x₁)
  drsize (x ←∂→ x₁) = (drsize x ←∂→ drsize x₁)
  

  fillAllLowerD : ∀{i u} → ∀ ll → Descendant {u} → SetLLD {i} {u} ll
  fillAllLowerD ∅ d = ↓∅ end
  fillAllLowerD (τ x) d = ↓τ end
  fillAllLowerD (ll ∧ ll₁) d = (fillAllLowerD ll d) ←∧→ fillAllLowerD ll₁ d
  fillAllLowerD (ll ∨ ll₁) d = (fillAllLowerD ll d) ←∨→ fillAllLowerD ll₁ d
  fillAllLowerD (ll ∂ ll₁) d = (fillAllLowerD ll d) ←∂→ fillAllLowerD ll₁ d
  fillAllLowerD (call x) d = ↓c end


  module _ where

    open import Data.Bool

    private

      red : ∀{u i ll q} → {j : Size< ↑ i} → ∀{ell} → (ind : IndexLL {i} {u} q ll) → SetLLD {j} (replLL ll ind ell) → SetLLD {j} ell
      red ↓ sd = sd
      red (ind ←∧) (sd ←∧→ sd₁) = red ind sd
      red (∧→ ind) (sd ←∧→ sd₁) = red ind sd₁
      red (ind ←∨) (sd ←∨→ sd₁) = red ind sd
      red (∨→ ind) (sd ←∨→ sd₁) = red ind sd₁
      red (ind ←∂) (sd ←∂→ sd₁) = red ind sd
      red (∂→ ind) (sd ←∂→ sd₁) = red ind sd₁

 -- TODO This is more like a replace than a compose since the initial descendant is an end.
 -- Here IndexLL actually only points to the lower parts of LinLogic ∅ , τ or call, so some pattern matches are
 -- unnecessary.

      scompose : ∀{u i} → {j : Size< ↑ i} → ∀ {oll rll} → SetLLD {i} {u} oll → IndexLL rll oll → Descendant {u} → SetLLD oll
      scompose (↓∅ x) ↓ d       = ↓∅ d
      scompose (↓τ x) ↓ d       = ↓τ d
      scompose (↓c x) ↓ d       = ↓c d
      -- These pattern cases should never happen.
      scompose (sd ←∧→ sd₁) ↓ d = IMPOSSIBLE
      scompose (sd ←∨→ sd₁) ↓ d = IMPOSSIBLE
      scompose (sd ←∂→ sd₁) ↓ d = IMPOSSIBLE
      
      scompose (sd ←∧→ sd₁) (i₁ ←∧) d = (scompose sd i₁ d) ←∧→ sd₁
      scompose (sd ←∧→ sd₁) (∧→ i₁) d = sd ←∧→ (scompose sd₁ i₁ d)
      scompose (sd ←∨→ sd₁) (i₁ ←∨) d = (scompose sd i₁ d) ←∨→ sd₁
      scompose (sd ←∨→ sd₁) (∨→ i₁) d = sd ←∨→ (scompose sd₁ i₁ d)
      scompose (sd ←∂→ sd₁) (i₁ ←∂) d = (scompose sd i₁ d) ←∂→ sd₁
      scompose (sd ←∂→ sd₁) (∂→ i₁) d = sd ←∂→ (scompose sd₁ i₁ d)
  
    compose : ∀{u i} → {j : Size< ↑ i} → ∀ {oll ll} → SetLLD {i} {u} oll → SetLLRem {i} {j} oll ll → SetLLD ll → SetLLD oll
    compose sdo (↓∅ m) (↓∅ d) = scompose sdo m d
    compose sdo (↓τ m) (↓τ d) = scompose sdo m d
    compose sdo (↓c m) (↓c d) = scompose sdo m d
    -- We should know the position of all elements.
    compose sdo (sr ←∧) (sd ←∧→ sd₁) = IMPOSSIBLE
    compose sdo (∧→ sr) (sd ←∧→ sd₁) = IMPOSSIBLE
    compose sdo (sr ←∧→ sr₁) (sd ←∧→ sd₁) = let r = compose sdo sr sd in
                                              compose r sr₁ sd₁
     -- We should know the position of all elements.
    compose sdo (sr ←∨) (sd ←∨→ sd₁) = IMPOSSIBLE
    compose sdo (∨→ sr) (sd ←∨→ sd₁) = IMPOSSIBLE
    compose sdo (sr ←∨→ sr₁) (sd ←∨→ sd₁) = let r = compose sdo sr sd in
                                              compose r sr₁ sd₁
     -- We should know the position of all elements.
    compose sdo (sr ←∂) (sd ←∂→ sd₁) = IMPOSSIBLE
    compose sdo (∂→ sr) (sd ←∂→ sd₁) = IMPOSSIBLE
    compose sdo (sr ←∂→ sr₁) (sd ←∂→ sd₁) = let r = compose sdo sr sd in
                                              compose r sr₁ sd₁

    ladd : ∀{i u pll ll} → {j : Size< ↑ i} → ∀{ell} → (ind : IndexLL {i} {u} pll ll) → SetLLD (replLL {j = j} ll ind ell) → SetLLD pll → SetLLD {j} ll
    ladd ↓ psd lsd = drsize lsd
    ladd (ind ←∧) (psd ←∧→ psd₁) lsd = ladd ind psd lsd ←∧→ psd₁
    ladd (∧→ ind) (psd ←∧→ psd₁) lsd = psd ←∧→ ladd ind psd₁ lsd
    ladd (ind ←∨) (psd ←∨→ psd₁) lsd = ladd ind psd lsd ←∨→ psd₁
    ladd (∨→ ind) (psd ←∨→ psd₁) lsd = psd ←∨→ ladd ind psd₁ lsd
    ladd (ind ←∂) (psd ←∂→ psd₁) lsd = ladd ind psd lsd ←∂→ psd₁
    ladd (∂→ ind) (psd ←∂→ psd₁) lsd = psd ←∂→ ladd ind psd₁ lsd

-- IMPORTANT We need to check that there are no obs in LinFun, since obs are there after a call has been unfolded.

    extractSetLLD : ∀{u i} → {j : Size< ↑ i} → {rll : LinLogic j {u}} → {ll : LinLogic i {u}} → (lf : LFun {rll = rll} {ll = ll}) → .{{ prf : notObs lf ≡ false }} → SetLLD ll
    extractSetLLD {u} {i = pi} {rll = rll} {ll = oll} lf = proj₂ $ extractSetLLD` zero lf (fillAllLowerD rll end) (fillAllLowerRem oll) where
      extractSetLLD` : ∀{pi} → {oll : LinLogic pi {u}} → {i : Size< ↑ pi} → {j : Size< ↑ i} → {rll : LinLogic j {u}} → {ll : LinLogic i {u}} → ℕ → (lf : LFun {rll = rll} {ll = ll}) → SetLLD rll → SetLLRem oll ll → ℕ × SetLLD oll 
      extractSetLLD` {oll = oll} {i = i} n I sd sr = (n , compose {j = i} (fillAllLowerD oll end) sr sd)
      extractSetLLD` {oll = oll} n (_⊂_ {j = j} {pll = pll} {ll = ll} {ell = ell} {ind = ind} lf₁ lf₂) sd sr with (extractSetLLD` n lf₂ sd (fillAllLowerRem (replLL ll ind ell)))
      ... | (n₁ , g) with (extractSetLLD` n₁ lf₁ (red ind g) (fillAllLowerRem pll))
      ... | (n₂ , r) = (n₂ , compose (fillAllLowerD oll end) (SetLLRem.drsize {j = j} sr) (ladd ind g r))
      extractSetLLD` n (tr {{ltr = ltr}} lf₁) sd sr = extractSetLLD` n lf₁ sd (tranRem sr ltr)
      extractSetLLD` n (obs lf₁) sd sr = IMPOSSIBLE
      extractSetLLD` {oll = oll} n (com {ll = ll} {frll = frll} df lf₁) sd sr with extractSetLLD` n lf₁ sd (fillAllLowerRem frll)
      ... | (n₁ , r) = (suc n₁ , fillAllLowerD oll (dec n₁ r)) 
      extractSetLLD` {oll = oll} n (call x) (↓c d) sr = (n , fillAllLowerD oll d) -- Here, we simply give the descendants of the call ∞rll to all the inputs of call. Since the inputs are not part of a single
      -- independent com , but of possibly many assynchronous independent coms, we should not create a new descendant like we did with the com.
  
  
