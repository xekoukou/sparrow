module WellFormedLF where

open import Common
open import LinLogic
open import SetLL
open import SetLLRem hiding (drsize)
open import LinFun
open import Data.Product

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
      orig  : Descendant
      dec  : ℕ → ∀{i ll} → SetLLD {i} {u} ll → Descendant
  
  
    
    data SetLLD {i : Size} {u} : LinLogic i {u} → Set (lsuc u) where
      ↓     : ∀{ll} →  Descendant {u}              → SetLLD ll
      _←∧   : ∀{rs ls} → SetLLD ls            → SetLLD (ls ∧ rs)
      ∧→_   : ∀{rs ls} → SetLLD rs            → SetLLD (ls ∧ rs)
      _←∧→_ : ∀{rs ls} → SetLLD ls → SetLLD rs → SetLLD (ls ∧ rs)
      _←∨   : ∀{rs ls} → SetLLD ls            → SetLLD (ls ∨ rs)
      ∨→_   : ∀{rs ls} → SetLLD rs            → SetLLD (ls ∨ rs)
      _←∨→_ : ∀{rs ls} → SetLLD ls → SetLLD rs → SetLLD (ls ∨ rs)
      _←∂   : ∀{rs ls} → SetLLD ls            → SetLLD (ls ∂ rs)
      ∂→_   : ∀{rs ls} → SetLLD rs            → SetLLD (ls ∂ rs)
      _←∂→_ : ∀{rs ls} → SetLLD ls → SetLLD rs → SetLLD (ls ∂ rs)
    
  
  
  data MSetLLD {i : Size} {u} : LinLogic i {u} → Set (lsuc u) where
    ∅   : ∀{ll}             → MSetLLD ll
    ¬∅  : ∀{ll} → SetLLD ll → MSetLLD ll
  
  -- TODO We shouldn't need this. When issue agda #2409 is resolved, remove this.
  drsize : ∀{i u ll} → {j : Size< ↑ i} → SetLLD {i} {u} ll → SetLLD {j} ll
  drsize (↓ mm)          = (↓ mm)
  drsize (x ←∧)     = (drsize x) ←∧
  drsize (∧→ x)     = ∧→ (drsize x)
  drsize (x ←∧→ x₁) = (drsize x ←∧→ drsize x₁)
  drsize (x ←∨)     = (drsize x) ←∨
  drsize (∨→ x)     = ∨→ (drsize x)
  drsize (x ←∨→ x₁) = (drsize x ←∨→ drsize x₁)
  drsize (x ←∂)     = (drsize x) ←∂
  drsize (∂→ x)     = ∂→ (drsize x)
  drsize (x ←∂→ x₁) = (drsize x ←∂→ drsize x₁)
  

  fillAllLowerD : ∀{i u} → ∀ ll → SetLLD {i} {u} ll
  fillAllLowerD ∅ = ↓ orig
  fillAllLowerD (τ x) = ↓ orig
  fillAllLowerD (ll ∧ ll₁) = (fillAllLowerD ll) ←∧→ fillAllLowerD ll₁
  fillAllLowerD (ll ∨ ll₁) = (fillAllLowerD ll) ←∨→ fillAllLowerD ll₁
  fillAllLowerD (ll ∂ ll₁) = (fillAllLowerD ll) ←∂→ fillAllLowerD ll₁
  fillAllLowerD (call x) = ↓ orig


  compose : ∀{u i} → {j : Size< ↑ i} → ∀ {oll ll} → SetLLD {i} {u} oll → SetLLRem {_} {j} oll ll → SetLLD ll → SetLLD oll
  compose sdo sr (↓ x) = {!!}
  compose sdo sr (sd ←∧) = {!!}
  compose sdo sr (∧→ sd) = {!!}
  compose sdo sr (sd ←∧→ sd₁) = {!!}
  compose sdo sr (sd ←∨) = {!!}
  compose sdo sr (∨→ sd) = {!!}
  compose sdo sr (sd ←∨→ sd₁) = {!!}
  compose sdo sr (sd ←∂) = {!!}
  compose sdo sr (∂→ sd) = {!!}
  compose sdo sr (sd ←∂→ sd₁) = {!!} 

  findNextCom : ∀{u i} → {j : Size< ↑ i} → {rll : LinLogic j {u}} → {ll : LinLogic i {u}} → LFun {rll = rll} {ll = ll} → SetLLD ll
  findNextCom {u} {i = pi} {ll = oll} lf = {!!} where
    findNextCom` : ∀{pi} → {oll : LinLogic pi {u}} → {i : Size< ↑ pi} → {j : Size< ↑ i} → {rll : LinLogic j {u}} → {ll : LinLogic i {u}} → LFun {rll = rll} {ll = ll} → SetLLRem oll ll → SetLLRem oll rll × SetLLD oll 
    findNextCom` {oll = oll} I sr = (sr , fillAllLowerD oll)
    findNextCom` (_⊂_ {pll = pll} {ll = ll} {ell = ell} {ind = ind} lf₁ lf₂) sr with (findNextCom` lf₁ (fillAllLowerRem pll))
    ... | (r₁ , r₂) with (findNextCom` lf₂ (fillAllLowerRem (replLL ll ind ell)))
    ... | (g₁ , g₂) = {!!}
    findNextCom` (tr lf₁) sr = {!!}
    findNextCom` (obs lf₁) sr = {!!}
    findNextCom` (com df lf₁) sr = {!!}
    findNextCom` (call x lf₁) sr = {!!}



