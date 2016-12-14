module LinLogic where

open import Data.Vec
import Level
open import Size
open import Data.Nat

infixr 5 _∷_

data HVec {u} : ∀{n} -> Vec (Set u) n -> Set u where
  []  : HVec []
  _∷_ : ∀{n} {A : Set u} {vt : Vec (Set u) n} (x : A) (xs : HVec vt) -> HVec (A ∷ vt)


genT : ∀{u} {n : ℕ} -> Vec (Set u) n -> Set (Level.suc u)
genT {u} [] = Set u
genT (x ∷ xs) =  x -> genT xs

applyH : ∀{u n} -> {vt : Vec (Set u) n} -> HVec vt -> genT vt -> Set u
applyH [] y = y
applyH (x ∷ xs) y = applyH xs (y x)


mutual
  -- Linear Logic Connectives : Used to describe the input
  -- and output of an agent.
  data LinLogic (i : Size) {u} : Set (Level.suc u) where
    -- When nothing is sent or received
    ∅    :                                       LinLogic i
    -- Contains a function that computes a dependent type.
    τ    : ∀{n} {dt : Vec (Set u) n} → genT dt → LinLogic i
    -- Both sub-trees need to be sent or received.
    _∧_  : LinLogic i {u} → LinLogic i {u}     → LinLogic i
    -- Only one sub-tree can be sent or received
    -- and the protocol specification has no control
    -- over which choice will be made.
    _∨_  : LinLogic i {u} → LinLogic i {u}     → LinLogic i
    -- Only one sub-tree can be sent or received
    -- and the protocol specification determines the choice
    -- based on the previous input of the agent.
    _∂_  : LinLogic i {u} → LinLogic i {u}     → LinLogic i
    -- The input or output of a linear function.
    -- The function can be recursive or corecursive.
    call : ∞LinLogic i {u}                     → LinLogic i

  record ∞LinLogic (i : Size) {u} : Set (Level.suc u) where
    coinductive
    field
      step : {j : Size< i} → LinLogic j {u = u}

open ∞LinLogic public

-- Transformations of the Linear Logic so as to construct
-- the correct sub-tree that is to be the input of a linear function.
data LLTr {i : Size} {u} (rll : LinLogic i {u}) : LinLogic i {u} → Set (Level.suc u) where
  -- Identity
  I     : LLTr rll rll
  -- Commutative transformations for ∂, ∧ and ∨.
  ∂c    : ∀{r l} → LLTr rll (r ∂ l) → LLTr rll (l ∂ r)
  ∧c    : ∀{r l} → LLTr rll (r ∧ l) → LLTr rll (l ∧ r)
  ∨c    : ∀{r l} → LLTr rll (r ∨ l) → LLTr rll (l ∨ r)
  -- Distributive transformations for ∧∂ and ∧∨.
  ∧∂d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∧ r) ∂ (l₂ ∧ r)) → LLTr rll ((l₁ ∂ l₂) ∧ r)
  ∧∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∧ r) ∨ (l₂ ∧ r)) → LLTr rll ((l₁ ∨ l₂) ∧ r)

-- Indexes over a specific node of a linear logic tree. 
data IndexLL {i : Size} {u} (rll : LinLogic i {u}) : LinLogic i {u} → Set u where
  ↓   :                             IndexLL rll rll
  _←∧ : ∀{li ri} → IndexLL rll li → IndexLL rll (li ∧ ri) 
  ∧→_ : ∀{li ri} → IndexLL rll ri → IndexLL rll (li ∧ ri) 
  _←∨ : ∀{li ri} → IndexLL rll li → IndexLL rll (li ∨ ri) 
  ∨→_ : ∀{li ri} → IndexLL rll ri → IndexLL rll (li ∨ ri) 
  _←∂ : ∀{li ri} → IndexLL rll li → IndexLL rll (li ∂ ri) 
  ∂→_ : ∀{li ri} → IndexLL rll ri → IndexLL rll (li ∂ ri) 

-- Replaces a node of a linear logic tree with another one.
replLL : ∀{i u q} → (ll : LinLogic i {u}) → IndexLL {i} {u} q ll → LinLogic i {u} → LinLogic i {u}
replLL ll ↓ c            = c
replLL (l ∧ r) (li ←∧) c = (replLL l li c) ∧ r
replLL (l ∧ r) (∧→ ri) c = l ∧ (replLL r ri c)
replLL (l ∨ r) (li ←∨) c = (replLL l li c) ∨ r
replLL (l ∨ r) (∨→ ri) c = l ∨ (replLL r ri c)
replLL (l ∂ r) (li ←∂) c = (replLL l li c) ∂ r
replLL (l ∂ r) (∂→ ri) c = l ∂ (replLL r ri c)

-- A non-empty set of nodes in a Linear Logic tree.
data SetLL {i : Size} {u} : LinLogic i {u} → Set where
  ↓     : ∀{ll}                          → SetLL ll
  _←∧   : ∀{rs ls} → SetLL ls            → SetLL (ls ∧ rs)
  ∧→_   : ∀{rs ls} → SetLL rs            → SetLL (ls ∧ rs)
  _←∧→_ : ∀{rs ls} → SetLL ls → SetLL rs → SetLL (ls ∧ rs)
  _←∨   : ∀{rs ls} → SetLL ls            → SetLL (ls ∨ rs)
  ∨→_   : ∀{rs ls} → SetLL rs            → SetLL (ls ∨ rs)
  _←∨→_ : ∀{rs ls} → SetLL ls → SetLL rs → SetLL (ls ∨ rs)
  _←∂   : ∀{rs ls} → SetLL ls            → SetLL (ls ∂ rs)
  ∂→_   : ∀{rs ls} → SetLL rs            → SetLL (ls ∂ rs)
  _←∂→_ : ∀{rs ls} → SetLL ls → SetLL rs → SetLL (ls ∂ rs)
  

-- A possibly empty set of nodes in a Linear Logic tree. 
data MSetLL {i : Size} {u} : LinLogic i {u} → Set where
  ∅   : ∀{ll}            → MSetLL ll
  ¬∅  : ∀{ll} → SetLL ll → MSetLL ll

module SetLLMp where
-- Add a node to an empty set (and potentially replace the linear logic sub-tree).
  ∅-add : ∀{i u ll q} → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic i {u})
          → SetLL (replLL ll ind rll)
  ∅-add ↓ rll = ↓
  ∅-add (ind ←∧) rll = (∅-add ind rll) ←∧
  ∅-add (∧→ ind) rll = ∧→ (∅-add ind rll)
  ∅-add (ind ←∨) rll = (∅-add ind rll) ←∨
  ∅-add (∨→ ind) rll = ∨→ (∅-add ind rll)
  ∅-add (ind ←∂) rll = (∅-add ind rll) ←∂
  ∅-add (∂→ ind) rll = ∂→ (∅-add ind rll)

-- If two adjacent nodes exist in the set, the higher node is in the set.
-- We contruct the set.
  contruct : ∀{i u ll} → SetLL {i} {u} ll → SetLL {i} {u} ll
  contruct ↓          = ↓
  contruct (x ←∧)     = (contruct x) ←∧
  contruct (∧→ x)     = ∧→ (contruct x)
  contruct (x ←∧→ x₁) = ↓
  contruct (x ←∨)     = (contruct x) ←∨
  contruct (∨→ x)     = ∨→ (contruct x)
  contruct (x ←∨→ x₁) = ↓
  contruct (x ←∂)     = (contruct x) ←∂
  contruct (∂→ x)     = ∂→ (contruct x)
  contruct (x ←∂→ x₁) = ↓

-- Add a node to a set (and potentially replace the linear logic sub-tree).
  add : ∀{i u ll q} → SetLL ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic i {u})
        → SetLL (replLL ll ind rll)
  add ↓ ind rll               = ↓
  add (s ←∧) ↓ rll            = ↓
  add (s ←∧) (ind ←∧) rll     = (add s ind rll) ←∧
  add (s ←∧) (∧→ ind) rll     = s ←∧→ (∅-add ind rll)
  add (∧→ s) ↓ rll            = ↓
  add (∧→ s) (ind ←∧) rll     = (∅-add ind rll) ←∧→ s
  add (∧→ s) (∧→ ind) rll     = ∧→ add s ind rll
  add (s ←∧→ s₁) ↓ rll        = ↓
  add (s ←∧→ s₁) (ind ←∧) rll = (add s ind rll) ←∧→ s₁
  add (s ←∧→ s₁) (∧→ ind) rll = s ←∧→ (add s₁ ind rll)
  add (s ←∨) ↓ rll            = ↓
  add (s ←∨) (ind ←∨) rll     = (add s ind rll) ←∨
  add (s ←∨) (∨→ ind) rll     = s ←∨→ (∅-add ind rll)
  add (∨→ s) ↓ rll            = ↓
  add (∨→ s) (ind ←∨) rll     = (∅-add ind rll) ←∨→ s
  add (∨→ s) (∨→ ind) rll     = ∨→ add s ind rll
  add (s ←∨→ s₁) ↓ rll        = ↓
  add (s ←∨→ s₁) (ind ←∨) rll = (add s ind rll) ←∨→ s₁
  add (s ←∨→ s₁) (∨→ ind) rll = s ←∨→ (add s₁ ind rll)
  add (s ←∂) ↓ rll            = ↓
  add (s ←∂) (ind ←∂) rll     = (add s ind rll) ←∂
  add (s ←∂) (∂→ ind) rll     = s ←∂→ (∅-add ind rll)
  add (∂→ s) ↓ rll            = ↓
  add (∂→ s) (ind ←∂) rll     = (∅-add ind rll) ←∂→ s
  add (∂→ s) (∂→ ind) rll     = ∂→ add s ind rll
  add (s ←∂→ s₁) ↓ rll        = ↓
  add (s ←∂→ s₁) (ind ←∂) rll = (add s ind rll) ←∂→ s₁
  add (s ←∂→ s₁) (∂→ ind) rll = s ←∂→ (add s₁ ind rll)

-- If we transform the linear logic tree, we need to transform the SetLL as well.
  tran : ∀ {i u ll rll} → SetLL {i} {u} ll → (tr : LLTr {i} {u} rll ll)
         → SetLL {i} {u} (replLL ll ↓ rll)
  tran s I                = s
  tran ↓ (∂c tr)          = ↓
  tran (s ←∂) (∂c tr)     = tran (∂→ s) tr
  tran (∂→ s) (∂c tr)     = tran (s ←∂) tr
  tran (s ←∂→ s₁) (∂c tr) = tran (s₁ ←∂→ s) tr
  tran ↓ (∨c tr)          = ↓
  tran (s ←∨) (∨c tr)     = tran (∨→ s) tr
  tran (∨→ s) (∨c tr)     = tran (s ←∨) tr
  tran (s ←∨→ s₁) (∨c tr) = tran (s₁ ←∨→ s) tr
  tran ↓ (∧c tr)          = ↓
  tran (s ←∧) (∧c tr)     = tran (∧→ s) tr
  tran (∧→ s) (∧c tr)     = tran (s ←∧) tr
  tran (s ←∧→ s₁) (∧c tr) = tran (s₁ ←∧→ s) tr
  tran ↓ (∧∂d tr)           = ↓
  tran (↓ ←∧) (∧∂d tr)      = tran ((↓ ←∧) ←∂→ (↓ ←∧)) tr
  tran ((s ←∂) ←∧) (∧∂d tr) = tran ((s ←∧) ←∂) tr
  tran ((∂→ s) ←∧) (∧∂d tr) = tran (∂→ (s ←∧)) tr
  tran ((s ←∂→ s₁) ←∧) (∧∂d tr) = tran ((s ←∧) ←∂→ (s₁ ←∧)) tr
  tran (∧→ s) (∧∂d tr)          = tran ((∧→ s) ←∂→ (∧→ s)) tr
  tran (↓ ←∧→ s₁) (∧∂d tr)      = tran ((↓ ←∧→ s₁) ←∂→ (↓ ←∧→ s₁)) tr
  tran ((s ←∂) ←∧→ s₁) (∧∂d tr) = tran ((s ←∧→ s₁) ←∂) tr
  tran ((∂→ s) ←∧→ s₁) (∧∂d tr) = tran (∂→ (s ←∧→ s₁)) tr
  tran ((s ←∂→ s₁) ←∧→ s₂) (∧∂d tr) = tran ((s ←∧→ s₂) ←∂→ (s₁ ←∧→ s₂)) tr
  tran ↓ (∧∨d tr)                   = ↓
  tran (↓ ←∧) (∧∨d tr)              = tran ((↓ ←∧) ←∨→ (↓ ←∧)) tr
  tran ((s ←∨) ←∧) (∧∨d tr)         = tran ((s ←∧) ←∨) tr
  tran ((∨→ s) ←∧) (∧∨d tr)         = tran (∨→ (s ←∧)) tr
  tran ((s ←∨→ s₁) ←∧) (∧∨d tr)     = tran ((s ←∧) ←∨→ (s₁ ←∧)) tr
  tran (∧→ s) (∧∨d tr)              = tran ((∧→ s) ←∨→ (∧→ s)) tr
  tran (↓ ←∧→ s₁) (∧∨d tr)          = tran ((↓ ←∧→ s₁) ←∨→ (↓ ←∧→ s₁)) tr
  tran ((s ←∨) ←∧→ s₁) (∧∨d tr)     = tran ((s ←∧→ s₁) ←∨) tr
  tran ((∨→ s) ←∧→ s₁) (∧∨d tr)     = tran (∨→ (s ←∧→ s₁)) tr
  tran ((s ←∨→ s₁) ←∧→ s₂) (∧∨d tr) = tran ((s ←∧→ s₂) ←∨→ (s₁ ←∧→ s₂)) tr

  itran : ∀ {i u ll rll pll} → SetLL {i} {u} ll → (ind : IndexLL {i} {u} pll ll) → (tr : LLTr {i} {u} rll pll)
          → SetLL {i} {u} (replLL ll ind rll)
  itran s ↓ tr                 = tran s tr
  itran ↓ (ind ←∧) tr          = ↓
  itran (s ←∧) (ind ←∧) tr     = itran s ind tr ←∧
  itran (∧→ s) (ind ←∧) tr     = ∧→ s
  itran (s ←∧→ s₁) (ind ←∧) tr = itran s ind tr ←∧→ s₁ 
  itran ↓ (∧→ ind) tr          = ↓
  itran (s ←∧) (∧→ ind) tr     = s ←∧
  itran (∧→ s) (∧→ ind) tr     = ∧→ itran s ind tr
  itran (s ←∧→ s₁) (∧→ ind) tr = s ←∧→ itran s₁ ind tr
  itran ↓ (ind ←∨) tr          = ↓
  itran (s ←∨) (ind ←∨) tr     = itran s ind tr ←∨
  itran (∨→ s) (ind ←∨) tr     = ∨→ s
  itran (s ←∨→ s₁) (ind ←∨) tr = itran s ind tr ←∨→ s₁ 
  itran ↓ (∨→ ind) tr          = ↓
  itran (s ←∨) (∨→ ind) tr     = s ←∨
  itran (∨→ s) (∨→ ind) tr     = ∨→ itran s ind tr
  itran (s ←∨→ s₁) (∨→ ind) tr = s ←∨→ itran s₁ ind tr
  itran ↓ (ind ←∂) tr          = ↓
  itran (s ←∂) (ind ←∂) tr     = itran s ind tr ←∂
  itran (∂→ s) (ind ←∂) tr     = ∂→ s
  itran (s ←∂→ s₁) (ind ←∂) tr = itran s ind tr ←∂→ s₁ 
  itran ↓ (∂→ ind) tr          = ↓
  itran (s ←∂) (∂→ ind) tr     = s ←∂
  itran (∂→ s) (∂→ ind) tr     = ∂→ itran s ind tr
  itran (s ←∂→ s₁) (∂→ ind) tr = s ←∂→ itran s₁ ind tr

