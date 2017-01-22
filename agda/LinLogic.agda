{-# OPTIONS --exact-split #-}

module LinLogic where

import Level
open import Size
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.List
open import Relation.Nullary


module _ where

  open import Data.Vec
  
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
replLL : ∀{i u q} → {j : Size< ↑ i} → (ll : LinLogic i {u}) → IndexLL {i} {u} q ll → LinLogic j {u} → LinLogic j {u}
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
  ∅-add : ∀{i u ll q} → {j : Size< ↑ i} → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic j {u})
          → SetLL (replLL {j = j} ll ind rll)
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


-- TODO Why do we need dsize? we shouldn't need it.
  dsize : ∀{i u ll} → {j : Size< ↑ i} → SetLL {i} {u} ll → SetLL {j} {u} ll
  dsize ↓          = ↓
  dsize (x ←∧)     = (dsize x) ←∧
  dsize (∧→ x)     = ∧→ (dsize x)
  dsize (x ←∧→ x₁) = (dsize x ←∧→ dsize x₁)
  dsize (x ←∨)     = (dsize x) ←∨
  dsize (∨→ x)     = ∨→ (dsize x)
  dsize (x ←∨→ x₁) = (dsize x ←∨→ dsize x₁)
  dsize (x ←∂)     = (dsize x) ←∂
  dsize (∂→ x)     = ∂→ (dsize x)
  dsize (x ←∂→ x₁) = (dsize x ←∂→ dsize x₁)


-- Add a node to a set (and potentially replace the linear logic sub-tree).
  add : ∀{i u ll q} → {j : Size< ↑ i} → SetLL {i} {u} ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic j {u})
        → SetLL (replLL {j = j} ll ind rll)
  add ↓ ind rll               = ↓
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

  data exactHit {i u} : ∀{ll rll} → (s : SetLL {i} {u} ll) → (ind : IndexLL {i} {u} rll ll) → Set where
    exactHitC↓↓ : ∀{ll} → exactHit {ll = ll} {rll = ll} ↓ ↓
    exactHitC←∧←∧ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = ll ∧ q} {rll = rll} (s ←∧) (ind ←∧)
    exactHitC∧→∧→ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = q ∧ ll} {rll = rll} (∧→ s) (∧→ ind)
    exactHitC←∨←∨ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = ll ∨ q} {rll = rll} (s ←∨) (ind ←∨)
    exactHitC∨→∨→ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = q ∨ ll} {rll = rll} (∨→ s) (∨→ ind)
    exactHitC←∂←∂ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = ll ∂ q} {rll = rll} (s ←∂) (ind ←∂)
    exactHitC∂→∂→ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = q ∂ ll} {rll = rll} (∂→ s) (∂→ ind)



  isExactHit : ∀{i u ll rll} → (s : SetLL {i} {u} ll) → (ind : IndexLL {i} {u} rll ll) → Dec (exactHit{ll = ll} {rll = rll} s ind)
  isExactHit ↓ ↓ = yes exactHitC↓↓
  isExactHit ↓ (ind ←∧) = no (λ ())
  isExactHit ↓ (∧→ ind) = no (λ ())
  isExactHit ↓ (ind ←∨) = no (λ ())
  isExactHit ↓ (∨→ ind) = no (λ ())
  isExactHit ↓ (ind ←∂) = no (λ ())
  isExactHit ↓ (∂→ ind) = no (λ ())
  isExactHit (s ←∧) ↓ = no (λ ())
  isExactHit (s ←∧) (ind ←∧) with (isExactHit s ind)
  isExactHit (s ←∧) (ind ←∧) | yes p = yes (exactHitC←∧←∧ p)
  isExactHit (s ←∧) (ind ←∧) | no ¬p = no (λ {(exactHitC←∧←∧ x) → ¬p x})
  isExactHit (s ←∧) (∧→ ind) = no (λ ())
  isExactHit (∧→ s) ↓ = no (λ ())
  isExactHit (∧→ s) (ind ←∧) = no (λ ())
  isExactHit (∧→ s) (∧→ ind) with (isExactHit s ind)
  isExactHit (∧→ s) (∧→ ind) | yes p = yes (exactHitC∧→∧→ p)
  isExactHit (∧→ s) (∧→ ind) | no ¬p = no (λ { (exactHitC∧→∧→ x) → ¬p x})
  isExactHit (s ←∧→ s₁) ind = no (λ ())
  isExactHit (s ←∨) ↓ = no (λ ())
  isExactHit (s ←∨) (ind ←∨) with (isExactHit s ind)
  isExactHit (s ←∨) (ind ←∨) | yes p = yes (exactHitC←∨←∨ p)
  isExactHit (s ←∨) (ind ←∨) | no ¬p = no ( λ { (exactHitC←∨←∨ x) → ¬p x})
  isExactHit (s ←∨) (∨→ ind) = no (λ ())
  isExactHit (∨→ s) ↓ = no (λ ())
  isExactHit (∨→ s) (ind ←∨) = no (λ ())
  isExactHit (∨→ s) (∨→ ind) with (isExactHit s ind)
  isExactHit (∨→ s) (∨→ ind) | yes p = yes (exactHitC∨→∨→ p)
  isExactHit (∨→ s) (∨→ ind) | no ¬p = no ( λ { (exactHitC∨→∨→ x) → ¬p x})
  isExactHit (s ←∨→ s₁) ind = no (λ ())
  isExactHit (s ←∂) ↓ = no (λ ())
  isExactHit (s ←∂) (ind ←∂) with (isExactHit s ind)
  isExactHit (s ←∂) (ind ←∂) | yes p = yes (exactHitC←∂←∂ p)
  isExactHit (s ←∂) (ind ←∂) | no ¬p = no ( λ { (exactHitC←∂←∂ x) → ¬p x})
  isExactHit (s ←∂) (∂→ ind) = no (λ ())
  isExactHit (∂→ s) ↓ = no (λ ())
  isExactHit (∂→ s) (ind ←∂) = no (λ ())
  isExactHit (∂→ s) (∂→ ind) with (isExactHit s ind)
  isExactHit (∂→ s) (∂→ ind) | yes p = yes (exactHitC∂→∂→ p)
  isExactHit (∂→ s) (∂→ ind) | no ¬p = no (λ { (exactHitC∂→∂→ x) → ¬p x})
  isExactHit (s ←∂→ s₁) ind = no (λ ())


-- It does not belong at all.


  data hitsOnce {i u} : ∀{ll rll} → SetLL {i} {u} ll → (ind : IndexLL {i} {u} rll ll) → Set where
    hitsOnce↓ : ∀{ll rll ind} → hitsOnce {ll = ll} {rll = rll} ↓ ind
    hitsOnce←∧↓ : ∀{lll llr s} → hitsOnce {ll = lll ∧ llr} {rll = lll ∧ llr} (s ←∧) ↓
    hitsOnce←∧←∧ : ∀{ll rll s q ind} → hitsOnce {ll = ll} {rll = rll} s ind → hitsOnce {ll = ll ∧ q} {rll = rll} (s ←∧) (ind ←∧)
    hitsOnce∧→↓ : ∀{lll llr s} → hitsOnce {ll = lll ∧ llr} {rll = lll ∧ llr} (∧→ s) ↓
    hitsOnce∧→∧→ : ∀{ll rll s q ind} → hitsOnce {ll = ll} {rll = rll} s ind → hitsOnce {ll = q ∧ ll} {rll = rll} (∧→ s) (∧→ ind) 
    hitsOnce←∧→↓ : ∀{lll llr s s₁} → hitsOnce {ll = lll ∧ llr} {rll = lll ∧ llr} (s ←∧→ s₁) ↓
    hitsOnce←∧→←∧ : ∀{ll rll s q s₁ ind} → hitsOnce {ll = ll} {rll = rll} s ind → hitsOnce {ll = ll ∧ q} {rll = rll} (s ←∧→ s₁) (ind ←∧)
    hitsOnce←∧→∧→ : ∀{ll rll q s s₁ ind} → hitsOnce {ll = ll} {rll = rll} s₁ ind → hitsOnce {ll = q ∧ ll} {rll = rll} (s ←∧→ s₁) (∧→ ind) 
    hitsOnce←∨↓ : ∀{lll llr s} → hitsOnce {ll = lll ∨ llr} {rll = lll ∨ llr} (s ←∨) ↓
    hitsOnce←∨←∨ : ∀{ll rll s q ind} → hitsOnce {ll = ll} {rll = rll} s ind → hitsOnce {ll = ll ∨ q} {rll = rll} (s ←∨) (ind ←∨)
    hitsOnce∨→↓ : ∀{lll llr s} → hitsOnce {ll = lll ∨ llr} {rll = lll ∨ llr} (∨→ s) ↓
    hitsOnce∨→∨→ : ∀{ll rll s q ind} → hitsOnce {ll = ll} {rll = rll} s ind → hitsOnce {ll = q ∨ ll} {rll = rll} (∨→ s) (∨→ ind) 
    hitsOnce←∨→↓ : ∀{lll llr s s₁} → hitsOnce {ll = lll ∨ llr} {rll = lll ∨ llr} (s ←∨→ s₁) ↓
    hitsOnce←∨→←∨ : ∀{ll rll s q s₁ ind} → hitsOnce {ll = ll} {rll = rll} s ind → hitsOnce {ll = ll ∨ q} {rll = rll} (s ←∨→ s₁) (ind ←∨)
    hitsOnce←∨→∨→ : ∀{ll rll q s s₁ ind} → hitsOnce {ll = ll} {rll = rll} s₁ ind → hitsOnce {ll = q ∨ ll} {rll = rll} (s ←∨→ s₁) (∨→ ind) 
    hitsOnce←∂↓ : ∀{lll llr s} → hitsOnce {ll = lll ∂ llr} {rll = lll ∂ llr} (s ←∂) ↓
    hitsOnce←∂←∂ : ∀{ll rll s q ind} → hitsOnce {ll = ll} {rll = rll} s ind → hitsOnce {ll = ll ∂ q} {rll = rll} (s ←∂) (ind ←∂)
    hitsOnce∂→↓ : ∀{lll llr s} → hitsOnce {ll = lll ∂ llr} {rll = lll ∂ llr} (∂→ s) ↓
    hitsOnce∂→∂→ : ∀{ll rll s q ind} → hitsOnce {ll = ll} {rll = rll} s ind → hitsOnce {ll = q ∂ ll} {rll = rll} (∂→ s) (∂→ ind) 
    hitsOnce←∂→↓ : ∀{lll llr s s₁} → hitsOnce {ll = lll ∂ llr} {rll = lll ∂ llr} (s ←∂→ s₁) ↓
    hitsOnce←∂→←∂ : ∀{ll rll s q s₁ ind} → hitsOnce {ll = ll} {rll = rll} s ind → hitsOnce {ll = ll ∂ q} {rll = rll} (s ←∂→ s₁) (ind ←∂)
    hitsOnce←∂→∂→ : ∀{ll rll q s s₁ ind} → hitsOnce {ll = ll} {rll = rll} s₁ ind → hitsOnce {ll = q ∂ ll} {rll = rll} (s ←∂→ s₁) (∂→ ind) 

  doesItHitOnce : ∀{i u ll q} → (s : SetLL {i} {u} ll) → (ind : IndexLL {i} {u} q ll) → Dec (hitsOnce s ind)
  doesItHitOnce ↓ ind = yes hitsOnce↓
  doesItHitOnce (s ←∧) ↓ = yes hitsOnce←∧↓
  doesItHitOnce (s ←∧) (ind ←∧) with (doesItHitOnce s ind)
  doesItHitOnce (s ←∧) (ind ←∧) | yes p = yes (hitsOnce←∧←∧ p)
  doesItHitOnce (s ←∧) (ind ←∧) | no ¬p = no (λ {(hitsOnce←∧←∧ x) → ¬p x})
  doesItHitOnce (s ←∧) (∧→ ind) = no (λ ())
  doesItHitOnce (∧→ s) ↓ = yes hitsOnce∧→↓
  doesItHitOnce (∧→ s) (ind ←∧) = no (λ ())
  doesItHitOnce (∧→ s) (∧→ ind) with (doesItHitOnce s ind)
  doesItHitOnce (∧→ s) (∧→ ind) | yes p = yes (hitsOnce∧→∧→ p)
  doesItHitOnce (∧→ s) (∧→ ind) | no ¬p = no (λ {(hitsOnce∧→∧→ x) → ¬p x})
  doesItHitOnce (s ←∧→ s₁) ↓ = yes hitsOnce←∧→↓
  doesItHitOnce (s ←∧→ s₁) (ind ←∧) with (doesItHitOnce s ind)
  doesItHitOnce (s ←∧→ s₁) (ind ←∧) | yes p = yes (hitsOnce←∧→←∧ p)
  doesItHitOnce (s ←∧→ s₁) (ind ←∧) | no ¬p = no (λ {(hitsOnce←∧→←∧ x) → ¬p x})
  doesItHitOnce (s ←∧→ s₁) (∧→ ind) with (doesItHitOnce s₁ ind)
  doesItHitOnce (s ←∧→ s₁) (∧→ ind) | yes p = yes (hitsOnce←∧→∧→ p) 
  doesItHitOnce (s ←∧→ s₁) (∧→ ind) | no ¬p = no (λ {(hitsOnce←∧→∧→ x) → ¬p x})
  doesItHitOnce (s ←∨) ↓ = yes hitsOnce←∨↓
  doesItHitOnce (s ←∨) (ind ←∨) with (doesItHitOnce s ind)
  doesItHitOnce (s ←∨) (ind ←∨) | yes p = yes (hitsOnce←∨←∨ p) 
  doesItHitOnce (s ←∨) (ind ←∨) | no ¬p = no (λ {(hitsOnce←∨←∨ x) → ¬p x})
  doesItHitOnce (s ←∨) (∨→ ind) = no (λ ())
  doesItHitOnce (∨→ s) ↓ = yes hitsOnce∨→↓
  doesItHitOnce (∨→ s) (ind ←∨) = no (λ ())
  doesItHitOnce (∨→ s) (∨→ ind) with (doesItHitOnce s ind)
  doesItHitOnce (∨→ s) (∨→ ind) | yes p = yes (hitsOnce∨→∨→ p) 
  doesItHitOnce (∨→ s) (∨→ ind) | no ¬p = no (λ {(hitsOnce∨→∨→ x) → ¬p x})
  doesItHitOnce (s ←∨→ s₁) ↓ = yes hitsOnce←∨→↓
  doesItHitOnce (s ←∨→ s₁) (ind ←∨) with (doesItHitOnce s ind)
  doesItHitOnce (s ←∨→ s₁) (ind ←∨) | yes p = yes (hitsOnce←∨→←∨ p) 
  doesItHitOnce (s ←∨→ s₁) (ind ←∨) | no ¬p = no (λ {(hitsOnce←∨→←∨ x) → ¬p x})
  doesItHitOnce (s ←∨→ s₁) (∨→ ind) with (doesItHitOnce s₁ ind)
  doesItHitOnce (s ←∨→ s₁) (∨→ ind) | yes p = yes (hitsOnce←∨→∨→ p)
  doesItHitOnce (s ←∨→ s₁) (∨→ ind) | no ¬p = no (λ {(hitsOnce←∨→∨→ x) → ¬p x})
  doesItHitOnce (s ←∂) ↓ = yes hitsOnce←∂↓
  doesItHitOnce (s ←∂) (ind ←∂) with (doesItHitOnce s ind)
  doesItHitOnce (s ←∂) (ind ←∂) | yes p = yes (hitsOnce←∂←∂ p) 
  doesItHitOnce (s ←∂) (ind ←∂) | no ¬p = no (λ {(hitsOnce←∂←∂ x) → ¬p x})
  doesItHitOnce (s ←∂) (∂→ ind) = no (λ ())
  doesItHitOnce (∂→ s) ↓ = yes hitsOnce∂→↓
  doesItHitOnce (∂→ s) (ind ←∂) = no (λ ())
  doesItHitOnce (∂→ s) (∂→ ind) with (doesItHitOnce s ind)
  doesItHitOnce (∂→ s) (∂→ ind) | yes p = yes (hitsOnce∂→∂→ p) 
  doesItHitOnce (∂→ s) (∂→ ind) | no ¬p = no (λ {(hitsOnce∂→∂→ x) → ¬p x})
  doesItHitOnce (s ←∂→ s₁) ↓ = yes hitsOnce←∂→↓
  doesItHitOnce (s ←∂→ s₁) (ind ←∂) with (doesItHitOnce s ind)
  doesItHitOnce (s ←∂→ s₁) (ind ←∂) | yes p = yes (hitsOnce←∂→←∂ p)
  doesItHitOnce (s ←∂→ s₁) (ind ←∂) | no ¬p = no (λ {(hitsOnce←∂→←∂ x) → ¬p x})
  doesItHitOnce (s ←∂→ s₁) (∂→ ind) with (doesItHitOnce s₁ ind)
  doesItHitOnce (s ←∂→ s₁) (∂→ ind) | yes p = yes (hitsOnce←∂→∂→ p)
  doesItHitOnce (s ←∂→ s₁) (∂→ ind) | no ¬p = no (λ {(hitsOnce←∂→∂→ x) → ¬p x})


-- Replace the linear logic sub-tree.
  replSetLL : ∀{i u ll q} → {j : Size< ↑ i} → (s : SetLL {i} {u} ll) → (ind : IndexLL {i} {u} q ll)
              → ⦃ prf : ¬ (hitsOnce s ind) ⦄ → (rll : LinLogic j {u})
              → (SetLL (replLL {j = j} ll ind rll))
  replSetLL ↓ ↓ {{prf}} rll = ⊥-elim (prf hitsOnce↓)
  replSetLL ↓ (ind ←∧) {{prf}} rll = ⊥-elim (prf hitsOnce↓)
  replSetLL ↓ (∧→ ind) {{prf}} rll = ⊥-elim (prf hitsOnce↓)
  replSetLL ↓ (ind ←∨) {{prf}} rll = ⊥-elim (prf hitsOnce↓)
  replSetLL ↓ (∨→ ind) {{prf}} rll = ⊥-elim (prf hitsOnce↓)
  replSetLL ↓ (ind ←∂) {{prf}} rll = ⊥-elim (prf hitsOnce↓)
  replSetLL ↓ (∂→ ind) {{prf}} rll = ⊥-elim (prf hitsOnce↓)
  replSetLL (s ←∧) ↓ {{prf}} rll = ⊥-elim (prf hitsOnce←∧↓)
  replSetLL (s ←∧) (ind ←∧) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsOnce←∧←∧ x)}} rll) ←∧
  replSetLL (s ←∧) (∧→ ind) {{prf}} rll = dsize s ←∧
  replSetLL (∧→ s) ↓ {{prf}} rll = ⊥-elim (prf hitsOnce∧→↓)
  replSetLL (∧→ s) (ind ←∧) {{prf}} rll = ∧→ dsize s
  replSetLL (∧→ s) (∧→ ind) {{prf}} rll = ∧→ (replSetLL s ind {{prf = λ x → prf (hitsOnce∧→∧→ x)}} rll)
  replSetLL (s ←∧→ s₁) ↓ {{prf}} rll = ⊥-elim (prf hitsOnce←∧→↓)
  replSetLL (s ←∧→ s₁) (ind ←∧) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsOnce←∧→←∧ x)}} rll) ←∧
  replSetLL (s ←∧→ s₁) (∧→ ind) {{prf}} rll = ∧→ (replSetLL s₁ ind {{prf = λ x → prf (hitsOnce←∧→∧→ x)}} rll)
  replSetLL (s ←∨) ↓ {{prf}} rll = ⊥-elim (prf hitsOnce←∨↓)
  replSetLL (s ←∨) (ind ←∨) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsOnce←∨←∨ x)}} rll) ←∨
  replSetLL (s ←∨) (∨→ ind) {{prf}} rll = dsize s ←∨
  replSetLL (∨→ s) ↓ {{prf}} rll = ⊥-elim (prf hitsOnce∨→↓)
  replSetLL (∨→ s) (ind ←∨) {{prf}} rll = ∨→ dsize s
  replSetLL (∨→ s) (∨→ ind) {{prf}} rll = ∨→ (replSetLL s ind {{prf = λ x → prf (hitsOnce∨→∨→ x)}} rll)
  replSetLL (s ←∨→ s₁) ↓ {{prf}} rll = ⊥-elim (prf hitsOnce←∨→↓)
  replSetLL (s ←∨→ s₁) (ind ←∨) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsOnce←∨→←∨ x)}} rll) ←∨
  replSetLL (s ←∨→ s₁) (∨→ ind) {{prf}} rll = ∨→ (replSetLL s₁ ind {{prf = λ x → prf (hitsOnce←∨→∨→ x)}} rll)
  replSetLL (s ←∂) ↓ {{prf}} rll = ⊥-elim (prf hitsOnce←∂↓)
  replSetLL (s ←∂) (ind ←∂) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsOnce←∂←∂ x)}} rll) ←∂
  replSetLL (s ←∂) (∂→ ind) {{prf}} rll = dsize s ←∂
  replSetLL (∂→ s) ↓ {{prf}} rll = ⊥-elim (prf hitsOnce∂→↓)
  replSetLL (∂→ s) (ind ←∂) {{prf}} rll = ∂→ dsize s
  replSetLL (∂→ s) (∂→ ind) {{prf}} rll = ∂→ (replSetLL s ind {{prf = λ x → prf (hitsOnce∂→∂→ x)}} rll)
  replSetLL (s ←∂→ s₁) ↓ {{prf}} rll = ⊥-elim (prf hitsOnce←∂→↓)
  replSetLL (s ←∂→ s₁) (ind ←∂) {{prf}} rll = (replSetLL s ind {{prf = λ x → prf (hitsOnce←∂→←∂ x)}} rll) ←∂
  replSetLL (s ←∂→ s₁) (∂→ ind) {{prf}} rll = ∂→ (replSetLL s₁ ind {{prf = λ x → prf (hitsOnce←∂→∂→ x)}} rll)

  truncSetLL : ∀ {i u ll pll} → SetLL {i} {u} ll → (ind : IndexLL {i} {u} pll ll)
               → MSetLL {i} {u} pll
  truncSetLL s ↓ = ¬∅ s
  truncSetLL ↓ (ind ←∧) = ¬∅ ↓
  truncSetLL (s ←∧) (ind ←∧) = truncSetLL s ind
  truncSetLL (∧→ s) (ind ←∧) = ∅
  truncSetLL (s ←∧→ s₁) (ind ←∧) = truncSetLL s ind
  truncSetLL ↓ (∧→ ind) = ¬∅ ↓
  truncSetLL (s ←∧) (∧→ ind) = ∅
  truncSetLL (∧→ s) (∧→ ind) = truncSetLL s ind
  truncSetLL (s ←∧→ s₁) (∧→ ind) = truncSetLL s₁ ind
  truncSetLL ↓ (ind ←∨) = ¬∅ ↓
  truncSetLL (s ←∨) (ind ←∨) = truncSetLL s ind
  truncSetLL (∨→ s) (ind ←∨) = ∅
  truncSetLL (s ←∨→ s₁) (ind ←∨) = truncSetLL s ind
  truncSetLL ↓ (∨→ ind) = ¬∅ ↓
  truncSetLL (s ←∨) (∨→ ind) = ∅
  truncSetLL (∨→ s) (∨→ ind) = truncSetLL s ind
  truncSetLL (s ←∨→ s₁) (∨→ ind) = truncSetLL s₁ ind
  truncSetLL ↓ (ind ←∂) = ¬∅ ↓
  truncSetLL (s ←∂) (ind ←∂) = truncSetLL s ind
  truncSetLL (∂→ s) (ind ←∂) = ∅
  truncSetLL (s ←∂→ s₁) (ind ←∂) = truncSetLL s ind
  truncSetLL ↓ (∂→ ind) = ¬∅ ↓
  truncSetLL (s ←∂) (∂→ ind) = ∅
  truncSetLL (∂→ s) (∂→ ind) = truncSetLL s ind
  truncSetLL (s ←∂→ s₁) (∂→ ind) = truncSetLL s₁ ind

  truncExSetLL : ∀ {i u ll pll} → (s : SetLL {i} {u} ll) → (ind : IndexLL {i} {u} pll ll)
               → ⦃ prf : exactHit (contruct s) ind ⦄ → SetLL {i} {u} pll
  truncExSetLL s ↓ {{prf}} = s
  truncExSetLL ↓ (ind ←∧) {{()}}
  truncExSetLL (s ←∧) (ind ←∧) {{exactHitC←∧←∧ prf}} = truncExSetLL s ind {{prf}}
  truncExSetLL (∧→ s) (ind ←∧) {{()}}
  truncExSetLL (s ←∧→ s₁) (ind ←∧) {{()}}
  truncExSetLL ↓ (∧→ ind) {{()}}
  truncExSetLL (s ←∧) (∧→ ind) {{()}}
  truncExSetLL (∧→ s) (∧→ ind) {{exactHitC∧→∧→ prf}} = truncExSetLL s ind {{prf}}
  truncExSetLL (s ←∧→ s₁) (∧→ ind) {{()}}
  truncExSetLL ↓ (ind ←∨) {{()}}
  truncExSetLL (s ←∨) (ind ←∨) {{exactHitC←∨←∨ prf}} = truncExSetLL s ind {{prf}}
  truncExSetLL (∨→ s) (ind ←∨) {{()}}
  truncExSetLL (s ←∨→ s₁) (ind ←∨) {{()}}
  truncExSetLL ↓ (∨→ ind) {{()}}
  truncExSetLL (s ←∨) (∨→ ind) {{()}}
  truncExSetLL (∨→ s) (∨→ ind) {{exactHitC∨→∨→ prf}} = truncExSetLL s ind {{prf}}
  truncExSetLL (s ←∨→ s₁) (∨→ ind) {{()}}
  truncExSetLL ↓ (ind ←∂) {{()}}
  truncExSetLL (s ←∂) (ind ←∂) {{exactHitC←∂←∂ prf}} = truncExSetLL s ind {{prf}}
  truncExSetLL (∂→ s) (ind ←∂) {{()}}
  truncExSetLL (s ←∂→ s₁) (ind ←∂) {{()}}
  truncExSetLL ↓ (∂→ ind) {{()}}
  truncExSetLL (s ←∂) (∂→ ind) {{()}}
  truncExSetLL (∂→ s) (∂→ ind) {{exactHitC∂→∂→ prf}} = truncExSetLL s ind {{prf}}
  truncExSetLL (s ←∂→ s₁) (∂→ ind) {{()}}



-- If we transform the linear logic tree, we need to transform the SetLL as well.
  tran : ∀ {i u ll rll} → SetLL {i} {u} ll → (tr : LLTr {i} {u} rll ll)
         → SetLL {i} {u} rll
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


-- In this transformation, we duplicate the set when we use distributive transformations, thus we
-- have two sets that contains the same number of inputs as before. One of them can be executed
-- when they join together into one root and a com exists in the Linear Function.
  sptran : ∀ {i u ll rll} → SetLL {i} {u} ll → (tr : LLTr {i} {u} rll ll)
         → List (SetLL {i} {u} rll)
  sptran s I                = [ s ]
  sptran ↓ (∂c tr)          = [ ↓ ]
  sptran (s ←∂) (∂c tr)     = sptran (∂→ s) tr
  sptran (∂→ s) (∂c tr)     = sptran (s ←∂) tr
  sptran (s ←∂→ s₁) (∂c tr) = sptran (s₁ ←∂→ s) tr
  sptran ↓ (∨c tr)          = [ ↓ ]
  sptran (s ←∨) (∨c tr)     = sptran (∨→ s) tr
  sptran (∨→ s) (∨c tr)     = sptran (s ←∨) tr
  sptran (s ←∨→ s₁) (∨c tr) = sptran (s₁ ←∨→ s) tr
  sptran ↓ (∧c tr)          = [ ↓ ]
  sptran (s ←∧) (∧c tr)     = sptran (∧→ s) tr
  sptran (∧→ s) (∧c tr)     = sptran (s ←∧) tr
  sptran (s ←∧→ s₁) (∧c tr) = sptran (s₁ ←∧→ s) tr
  sptran ↓ (∧∂d tr)           = [ ↓ ]
  sptran (↓ ←∧) (∧∂d tr)      = sptran ((↓ ←∧) ←∂→ (↓ ←∧)) tr
  sptran ((s ←∂) ←∧) (∧∂d tr) = sptran ((s ←∧) ←∂) tr
  sptran ((∂→ s) ←∧) (∧∂d tr) = sptran (∂→ (s ←∧)) tr
  sptran ((s ←∂→ s₁) ←∧) (∧∂d tr) = sptran ((s ←∧) ←∂→ (s₁ ←∧)) tr
  sptran (∧→ s) (∧∂d tr)          = (sptran ((∧→ s) ←∂) tr) ++ (sptran (∂→ (∧→ s)) tr)
  sptran (↓ ←∧→ s₁) (∧∂d tr)      = (sptran ((↓ ←∧→ s₁) ←∂) tr) ++ (sptran (∂→ (↓ ←∧→ s₁)) tr)
  sptran ((s ←∂) ←∧→ s₁) (∧∂d tr) = sptran ((s ←∧→ s₁) ←∂) tr
  sptran ((∂→ s) ←∧→ s₁) (∧∂d tr) = sptran (∂→ (s ←∧→ s₁)) tr
  sptran ((s ←∂→ s₁) ←∧→ s₂) (∧∂d tr) = (sptran ((s ←∧→ s₂) ←∂) tr) ++ (sptran (∂→ (s₁ ←∧→ s₂)) tr)
  sptran ↓ (∧∨d tr)                   = [ ↓ ]
  sptran (↓ ←∧) (∧∨d tr)              = sptran ((↓ ←∧) ←∨→ (↓ ←∧)) tr
  sptran ((s ←∨) ←∧) (∧∨d tr)         = sptran ((s ←∧) ←∨) tr
  sptran ((∨→ s) ←∧) (∧∨d tr)         = sptran (∨→ (s ←∧)) tr
  sptran ((s ←∨→ s₁) ←∧) (∧∨d tr)     = sptran ((s ←∧) ←∨→ (s₁ ←∧)) tr
  sptran (∧→ s) (∧∨d tr)              = (sptran ((∧→ s) ←∨) tr) ++ (sptran (∨→ (∧→ s)) tr)
  sptran (↓ ←∧→ s₁) (∧∨d tr)          = (sptran ((↓ ←∧→ s₁) ←∨) tr) ++ (sptran (∨→ (↓ ←∧→ s₁)) tr)
  sptran ((s ←∨) ←∧→ s₁) (∧∨d tr)     = sptran ((s ←∧→ s₁) ←∨) tr
  sptran ((∨→ s) ←∧→ s₁) (∧∨d tr)     = sptran (∨→ (s ←∧→ s₁)) tr
  sptran ((s ←∨→ s₁) ←∧→ s₂) (∧∨d tr) = (sptran ((s ←∧→ s₂) ←∨) tr) ++ (sptran (∨→ (s₁ ←∧→ s₂)) tr)


-- TODO FilledSetLL describes a SetLL as it would be when used to indicate that all
-- linear functions have being executed/cut.
  data FilledSetLL {i : Size} {u} : {ll : LinLogic i {u}} → SetLL ll → Set where
    ↓     :                              FilledSetLL (↓ {ll = ∅})
    _←∧→_   : ∀{rs ls s s₁} → FilledSetLL s → FilledSetLL s₁ → FilledSetLL (_←∧→_ {rs = rs} {ls = ls} s s₁)   
    _←∨   : ∀{rs ls s} → FilledSetLL s → FilledSetLL (_←∨ {rs = rs} {ls = ls} s) 
    ∨→_   : ∀{rs ls s} → FilledSetLL s → FilledSetLL (∨→_ {rs = rs} {ls = ls} s) 
    _←∂   : ∀{rs ls s} → FilledSetLL s → FilledSetLL (_←∂ {rs = rs} {ls = ls} s) 
    ∂→_   : ∀{rs ls s} → FilledSetLL s → FilledSetLL (∂→_ {rs = rs} {ls = ls} s) 
  


module _ where

  open import Data.Bool
  
  private
    noNilFinite : ∀{i u} → (ll : LinLogic i {u}) → Bool
    noNilFinite ∅ = false
    noNilFinite (τ x₁) = true
    noNilFinite (y LinLogic.∧ y₁) = noNilFinite y Data.Bool.∧ noNilFinite y₁
    noNilFinite (y LinLogic.∨ y₁) = noNilFinite y Data.Bool.∧ noNilFinite y₁
    noNilFinite (y ∂ y₁) = noNilFinite y Data.Bool.∧ noNilFinite y₁
    noNilFinite (call x₁) = false

  -- TODO Do we have to do that?
  onlyOneNilOrNoNilFinite : ∀{i u} → (ll : LinLogic i {u}) → Bool
  onlyOneNilOrNoNilFinite ∅ = true
  onlyOneNilOrNoNilFinite (τ x) = noNilFinite (τ x)
  onlyOneNilOrNoNilFinite (x LinLogic.∧ x₁) = noNilFinite (x LinLogic.∧ x₁)
  onlyOneNilOrNoNilFinite (x LinLogic.∨ x₁) = noNilFinite (x LinLogic.∨ x₁)
  onlyOneNilOrNoNilFinite (x ∂ x₁) = noNilFinite (x ∂ x₁)
  onlyOneNilOrNoNilFinite (call x) = noNilFinite (call x)

mutual
  data All∅ {i u} : LinLogic i {u} → Set where
    ∅ :                               All∅ ∅
    _∧_  : ∀{l r} → All∅ l → All∅ r → All∅ (l ∧ r)
    _∨_  : ∀{l r} → All∅ l → All∅ r → All∅ (l ∨ r)
    _∂_  : ∀{l r} → All∅ l → All∅ r → All∅ (l ∂ r)
    call : ∀{∞ll} → ∞All∅ ∞ll       → All∅ (call ∞ll)
  
  record ∞All∅ {i u} (∞ll : ∞LinLogic i {u}) : Set where
    coinductive
    field
      step : {j : Size< i} → All∅ {i = j} {u = u} (step ∞ll)
