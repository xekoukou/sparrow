module WellFormedLF where

open import Common
open import LinLogic
open import SetLL

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
  
  data Ancestor : Set where
    orig  : Ancestor
    anc   : ℕ → Ancestor → Ancestor
    manc  : ℕ → ∀{n} → Vec Ancestor n → Ancestor → Ancestor


  
  data SetLLD {i : Size} {u} : LinLogic i {u} → Set (lsuc u) where
    ↓     : ∀{ll} →  Ancestor               → SetLLD ll
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
  fillAllLowerD ll = {!!}
  
  
  
