module WellFormedLF where

open import Common
open import LinLogic
import SetLL

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



-- A non-empty set of nodes in a Linear Logic tree that also can also tag intermediary nodes.
data SetLLInter {i : Size} {u} : LinLogic i {u} → Set where
  ↓     : ∀{ll}                                    → SetLLInter ll
  ↓+    : ∀{ll}    → SetLLInter ll                 → SetLLInter ll
  _←∧   : ∀{rs ls} → SetLLInter ls                 → SetLLInter (ls ∧ rs)
  ∧→_   : ∀{rs ls} → SetLLInter rs                 → SetLLInter (ls ∧ rs)
  _←∧→_ : ∀{rs ls} → SetLLInter ls → SetLLInter rs → SetLLInter (ls ∧ rs)
  _←∨   : ∀{rs ls} → SetLLInter ls                 → SetLLInter (ls ∨ rs)
  ∨→_   : ∀{rs ls} → SetLLInter rs                 → SetLLInter (ls ∨ rs)
  _←∨→_ : ∀{rs ls} → SetLLInter ls → SetLLInter rs → SetLLInter (ls ∨ rs)
  _←∂   : ∀{rs ls} → SetLLInter ls                 → SetLLInter (ls ∂ rs)
  ∂→_   : ∀{rs ls} → SetLLInter rs                 → SetLLInter (ls ∂ rs)
  _←∂→_ : ∀{rs ls} → SetLLInter ls → SetLLInter rs → SetLLInter (ls ∂ rs)


data MSetLLInter {i : Size} {u} : LinLogic i {u} → Set where
  ∅   : ∀{ll}                 → MSetLLInter ll
  ¬∅  : ∀{ll} → SetLLInter ll → MSetLLInter ll


∅-add : ∀{i u ll rll} → {j : Size< ↑ i} → (ind : IndexLL {i} {u} rll ll) → (nrll : LinLogic j )
        → SetLLInter (replLL ll ind nrll)
∅-add ↓ nrll = ↓
∅-add (ind ←∧) nrll = (∅-add ind nrll) ←∧
∅-add (∧→ ind) nrll = ∧→ (∅-add ind nrll)
∅-add (ind ←∨) nrll = (∅-add ind nrll) ←∨
∅-add (∨→ ind) nrll = ∨→ (∅-add ind nrll)
∅-add (ind ←∂) nrll = (∅-add ind nrll) ←∂
∅-add (∂→ ind) nrll = ∂→ (∅-add ind nrll)

-- TODO We shouldn't need this. When issue agda #2409 is resolved, remove this.
dsize : ∀{i u ll} → {j : Size< ↑ i} → SetLLInter {i} {u} ll → SetLLInter {j} ll
dsize ↓          = ↓
dsize (↓+ s)     = (↓+ $ dsize s)
dsize (x ←∧)     = (dsize x) ←∧
dsize (∧→ x)     = ∧→ (dsize x)
dsize (x ←∧→ x₁) = (dsize x ←∧→ dsize x₁)
dsize (x ←∨)     = (dsize x) ←∨
dsize (∨→ x)     = ∨→ (dsize x)
dsize (x ←∨→ x₁) = (dsize x ←∨→ dsize x₁)
dsize (x ←∂)     = (dsize x) ←∂
dsize (∂→ x)     = ∂→ (dsize x)
dsize (x ←∂→ x₁) = (dsize x ←∂→ dsize x₁)

-- Lower level intermediary are removed when adding a new index.
add : ∀{i u ll q} → {j : Size< ↑ i} → SetLLInter ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic j)
      → SetLLInter (replLL ll ind rll)
add ↓ ↓ rll                 = ↓
add ↓ ind rll               = ↓+ (∅-add ind rll)
add (↓+ s) ind rll          = ↓+ (add s ind rll)
add (s ←∧) ↓ rll            = ↓
add (s ←∧) (ind ←∧) rll     = (add s ind rll) ←∧
add (s ←∧) (∧→ ind) rll     = dsize s ←∧→ (∅-add ind rll)
add (∧→ s) ↓ rll            = ↓
add (∧→ s) (ind ←∧) rll     = (∅-add ind rll) ←∧→ dsize s
add (∧→ s) (∧→ ind) rll     = ∧→ add s ind rll
add (s ←∧→ s₁) ↓ rll        = ↓
add (s ←∧→ s₁) (ind ←∧) rll = (add s ind rll) ←∧→ dsize s₁
add (s ←∧→ s₁) (∧→ ind) rll = dsize s ←∧→ (add s₁ ind rll)
add (s ←∨) ↓ rll            = ↓
add (s ←∨) (ind ←∨) rll     = (add s ind rll) ←∨
add (s ←∨) (∨→ ind) rll     = dsize s ←∨→ (∅-add ind rll)
add (∨→ s) ↓ rll            = ↓
add (∨→ s) (ind ←∨) rll     = (∅-add ind rll) ←∨→ dsize s
add (∨→ s) (∨→ ind) rll     = ∨→ add s ind rll
add (s ←∨→ s₁) ↓ rll        = ↓
add (s ←∨→ s₁) (ind ←∨) rll = (add s ind rll) ←∨→ dsize s₁
add (s ←∨→ s₁) (∨→ ind) rll = dsize s ←∨→ (add s₁ ind rll)
add (s ←∂) ↓ rll            = ↓
add (s ←∂) (ind ←∂) rll     = (add s ind rll) ←∂
add (s ←∂) (∂→ ind) rll     = dsize s ←∂→ (∅-add ind rll)
add (∂→ s) ↓ rll            = ↓
add (∂→ s) (ind ←∂) rll     = (∅-add ind rll) ←∂→ dsize s
add (∂→ s) (∂→ ind) rll     = ∂→ add s ind rll
add (s ←∂→ s₁) ↓ rll        = ↓
add (s ←∂→ s₁) (ind ←∂) rll = (add s ind rll) ←∂→ dsize s₁
add (s ←∂→ s₁) (∂→ ind) rll = dsize s ←∂→ (add s₁ ind rll)


madd : ∀{i u ll q} → {j : Size< ↑ i} → MSetLLInter ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic j)
      → MSetLLInter (replLL ll ind rll)
madd ∅ ind rll = ¬∅ (∅-add ind rll)
madd (¬∅ x) ind rll = ¬∅ (add x ind rll)

del : ∀{i u ll q} → {j : Size< ↑ i} → SetLLInter ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic j)
      → MSetLLInter (replLL ll ind rll)
del ↓ ↓ rll = ∅
del (↓+ s) ↓ rll = {!¬∅ s!}
del (s ←∧) ↓ rll = {!!}
del (∧→ s) ↓ rll = {!!}
del (s ←∧→ s₁) ↓ rll = {!!}
del (s ←∨) ↓ rll = {!!}
del (∨→ s) ↓ rll = {!!}
del (s ←∨→ s₁) ↓ rll = {!!}
del (s ←∂) ↓ rll = {!!}
del (∂→ s) ↓ rll = {!!}
del (s ←∂→ s₁) ↓ rll = {!!}
del ↓ (ind ←∧) rll with (del ↓ ind rll)
del ↓ (ind ←∧) rll | ∅ = ¬∅ (∧→ ↓)
del ↓ (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧→ ↓)
del (s ←∧) (ind ←∧) rll with (del s ind rll)
del (s ←∧) (ind ←∧) rll | ∅ = ∅
del (s ←∧) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧)
del (∧→ s) (ind ←∧) rll = ¬∅ (∧→ (dsize s))
del (s ←∧→ s₁) (ind ←∧) rll with (del s ind rll)
del (s ←∧→ s₁) (ind ←∧) rll | ∅ = ¬∅ (∧→ (dsize s₁))
del (s ←∧→ s₁) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧→ (dsize s₁))
del ↓ (∧→ ind) rll with (del ↓ ind rll)
del ↓ (∧→ ind) rll | ∅ = ¬∅ (↓ ←∧)
del ↓ (∧→ ind) rll | ¬∅ x = ¬∅ (↓ ←∧→ x)
del (s ←∧) (∧→ ind) rll = ¬∅ ((dsize s) ←∧)
del (∧→ s) (∧→ ind) rll with (del s ind rll)
del (∧→ s) (∧→ ind) rll | ∅ = ∅
del (∧→ s) (∧→ ind) rll | ¬∅ x = ¬∅ (∧→ x)
del (s ←∧→ s₁) (∧→ ind) rll with (del s₁ ind rll)
del (s ←∧→ s₁) (∧→ ind) rll | ∅ = ¬∅ ((dsize s) ←∧)
del (s ←∧→ s₁) (∧→ ind) rll | ¬∅ x = ¬∅ ((dsize s) ←∧→ x)
del ↓ (ind ←∨) rll with (del ↓ ind rll)
del ↓ (ind ←∨) rll | ∅ = ¬∅ (∨→ ↓)
del ↓ (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨→ ↓)
del (s ←∨) (ind ←∨) rll with (del s ind rll)
del (s ←∨) (ind ←∨) rll | ∅ = ∅
del (s ←∨) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨)
del (∨→ s) (ind ←∨) rll = ¬∅ (∨→ (dsize s))
del (s ←∨→ s₁) (ind ←∨) rll with (del s ind rll)
del (s ←∨→ s₁) (ind ←∨) rll | ∅ = ¬∅ (∨→ (dsize s₁))
del (s ←∨→ s₁) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨→ (dsize s₁))
del ↓ (∨→ ind) rll with (del ↓ ind rll)
del ↓ (∨→ ind) rll | ∅ = ¬∅ (↓ ←∨)
del ↓ (∨→ ind) rll | ¬∅ x = ¬∅ (↓ ←∨→ x)
del (s ←∨) (∨→ ind) rll = ¬∅ ((dsize s) ←∨)
del (∨→ s) (∨→ ind) rll with (del s ind rll)
del (∨→ s) (∨→ ind) rll | ∅ = ∅
del (∨→ s) (∨→ ind) rll | ¬∅ x = ¬∅ (∨→ x)
del (s ←∨→ s₁) (∨→ ind) rll with (del s₁ ind rll)
del (s ←∨→ s₁) (∨→ ind) rll | ∅ = ¬∅ ((dsize s) ←∨)
del (s ←∨→ s₁) (∨→ ind) rll | ¬∅ x = ¬∅ ((dsize s) ←∨→ x)
del ↓ (ind ←∂) rll with (del ↓ ind rll)
del ↓ (ind ←∂) rll | ∅ = ¬∅ (∂→ ↓)
del ↓ (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂→ ↓)
del (s ←∂) (ind ←∂) rll with (del s ind rll)
del (s ←∂) (ind ←∂) rll | ∅ = ∅
del (s ←∂) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂)
del (∂→ s) (ind ←∂) rll = ¬∅ (∂→ (dsize s))
del (s ←∂→ s₁) (ind ←∂) rll with (del s ind rll)
del (s ←∂→ s₁) (ind ←∂) rll | ∅ = ¬∅ (∂→ (dsize s₁))
del (s ←∂→ s₁) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂→ (dsize s₁))
del ↓ (∂→ ind) rll with (del ↓ ind rll)
del ↓ (∂→ ind) rll | ∅ = ¬∅ (↓ ←∂)
del ↓ (∂→ ind) rll | ¬∅ x = ¬∅ (↓ ←∂→ x)
del (s ←∂) (∂→ ind) rll = ¬∅ ((dsize s) ←∂)
del (∂→ s) (∂→ ind) rll with (del s ind rll)
del (∂→ s) (∂→ ind) rll | ∅ = ∅
del (∂→ s) (∂→ ind) rll | ¬∅ x = ¬∅ (∂→ x)
del (s ←∂→ s₁) (∂→ ind) rll with (del s₁ ind rll)
del (s ←∂→ s₁) (∂→ ind) rll | ∅ = ¬∅ ((dsize s) ←∂)
del (s ←∂→ s₁) (∂→ ind) rll | ¬∅ x = ¬∅ ((dsize s) ←∂→ x)


