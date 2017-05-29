{-# OPTIONS --exact-split #-}
module SetLL where

open import Common hiding (_≤_)
open import LinLogic
open import LinLogicProp
open import IndexLLProp hiding (tran)
import Data.List
import Relation.Binary.PropositionalEquality


-- TODO ?? We need to remove all nrll like in ∅-add and simply use a special function for that. (indₛ-morph)

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


-- Add a node to an empty set (and potentially replace the linear logic sub-tree).
∅-add : ∀{i u ll rll} → (ind : IndexLL {i} {u} rll ll) → (nrll : LinLogic i )
        → SetLL (replLL ll ind nrll)
∅-add ↓ nrll = ↓
∅-add (ind ←∧) nrll = (∅-add ind nrll) ←∧
∅-add (∧→ ind) nrll = ∧→ (∅-add ind nrll)
∅-add (ind ←∨) nrll = (∅-add ind nrll) ←∨
∅-add (∨→ ind) nrll = ∨→ (∅-add ind nrll)
∅-add (ind ←∂) nrll = (∅-add ind nrll) ←∂
∅-add (∂→ ind) nrll = ∂→ (∅-add ind nrll)


-- Add a node to a set (and potentially replace the linear logic sub-tree).
add : ∀{i u ll q} → SetLL ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic i)
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

madd : ∀{i u ll q} → MSetLL ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic i)
      → MSetLL (replLL ll ind rll)
madd ∅ ind rll = ¬∅ (∅-add ind rll)
madd (¬∅ x) ind rll = ¬∅ (add x ind rll)


_∪ₛ_ : ∀{i u ll} → SetLL {i} {u} ll → SetLL ll → SetLL ll
↓ ∪ₛ b = ↓
(a ←∧) ∪ₛ ↓ = ↓
(a ←∧) ∪ₛ (b ←∧) = (a ∪ₛ b) ←∧
(a ←∧) ∪ₛ (∧→ b) = a ←∧→ b
(a ←∧) ∪ₛ (b ←∧→ b₁) = (a ∪ₛ b) ←∧→ b₁
(∧→ a) ∪ₛ ↓ = ↓
(∧→ a) ∪ₛ (b ←∧) = b ←∧→ a
(∧→ a) ∪ₛ (∧→ b) = ∧→ (a ∪ₛ b)
(∧→ a) ∪ₛ (b ←∧→ b₁) = b ←∧→ (a ∪ₛ b₁)
(a ←∧→ a₁) ∪ₛ ↓ = ↓
(a ←∧→ a₁) ∪ₛ (b ←∧) = (a ∪ₛ b) ←∧→ a₁
(a ←∧→ a₁) ∪ₛ (∧→ b) = a ←∧→ (a₁ ∪ₛ b)
(a ←∧→ a₁) ∪ₛ (b ←∧→ b₁) = (a ∪ₛ b) ←∧→ (a₁ ∪ₛ b₁)
(a ←∨) ∪ₛ ↓ = ↓
(a ←∨) ∪ₛ (b ←∨) = (a ∪ₛ b) ←∨
(a ←∨) ∪ₛ (∨→ b) = a ←∨→ b
(a ←∨) ∪ₛ (b ←∨→ b₁) = (a ∪ₛ b) ←∨→ b₁
(∨→ a) ∪ₛ ↓ = ↓
(∨→ a) ∪ₛ (b ←∨) = b ←∨→ a
(∨→ a) ∪ₛ (∨→ b) = ∨→ (a ∪ₛ b)
(∨→ a) ∪ₛ (b ←∨→ b₁) = b ←∨→ (a ∪ₛ b₁)
(a ←∨→ a₁) ∪ₛ ↓ = ↓
(a ←∨→ a₁) ∪ₛ (b ←∨) = (a ∪ₛ b) ←∨→ a₁
(a ←∨→ a₁) ∪ₛ (∨→ b) = a ←∨→ (a₁ ∪ₛ b)
(a ←∨→ a₁) ∪ₛ (b ←∨→ b₁) = (a ∪ₛ b) ←∨→ (a₁ ∪ₛ b₁)
(a ←∂) ∪ₛ ↓ = ↓
(a ←∂) ∪ₛ (b ←∂) = (a ∪ₛ b) ←∂
(a ←∂) ∪ₛ (∂→ b) = a ←∂→ b
(a ←∂) ∪ₛ (b ←∂→ b₁) = (a ∪ₛ b) ←∂→ b₁
(∂→ a) ∪ₛ ↓ = ↓
(∂→ a) ∪ₛ (b ←∂) = b ←∂→ a
(∂→ a) ∪ₛ (∂→ b) = ∂→ (a ∪ₛ b)
(∂→ a) ∪ₛ (b ←∂→ b₁) = b ←∂→ (a ∪ₛ b₁)
(a ←∂→ a₁) ∪ₛ ↓ = ↓
(a ←∂→ a₁) ∪ₛ (b ←∂) = (a ∪ₛ b) ←∂→ a₁
(a ←∂→ a₁) ∪ₛ (∂→ b) = a ←∂→ (a₁ ∪ₛ b)
(a ←∂→ a₁) ∪ₛ (b ←∂→ b₁) = (a ∪ₛ b) ←∂→ (a₁ ∪ₛ b₁)

_∪ₘₛ_ : ∀{i u} → {ll : LinLogic i {u}} → MSetLL ll → MSetLL ll → MSetLL ll
_∪ₘₛ_ ∅ ∅            = ∅
_∪ₘₛ_ ∅ (¬∅ s)       = ¬∅ s
_∪ₘₛ_ (¬∅ fs) ∅      = ¬∅ fs
_∪ₘₛ_ (¬∅ fs) (¬∅ s) = ¬∅ (fs ∪ₛ s)


_∩ₛ_ : ∀{i u ll} → SetLL {i} {u} ll → SetLL ll → MSetLL ll
↓ ∩ₛ b = ¬∅ b
(a ←∧) ∩ₛ ↓ = ¬∅ (a ←∧)
(a ←∧) ∩ₛ (b ←∧) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (x ←∧)
(a ←∧) ∩ₛ (∧→ b) = ∅
(a ←∧) ∩ₛ (b ←∧→ b₁) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (x ←∧)
(∧→ a) ∩ₛ ↓ = ¬∅ (∧→ a)
(∧→ a) ∩ₛ (b ←∧) = ∅
(∧→ a) ∩ₛ (∧→ b) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (∧→ x)
(∧→ a) ∩ₛ (b ←∧→ b₁) with (a ∩ₛ b₁)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (∧→ x)
(a ←∧→ a₁) ∩ₛ ↓ = ¬∅ (a ←∧→ a₁)
(a ←∧→ a₁) ∩ₛ (b ←∧) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (x ←∧)
(a ←∧→ a₁) ∩ₛ (∧→ b) with (a₁ ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (∧→ x)
(a ←∧→ a₁) ∩ₛ (b ←∧→ b₁) with (a ∩ₛ b) | (a₁ ∩ₛ b₁)
... | ∅ | ∅ = ∅
... | ∅ | ¬∅ r = ¬∅ (∧→ r)
... | ¬∅ l | ∅ = ¬∅ (l ←∧)
... | ¬∅ l | ¬∅ r = ¬∅ (l ←∧→ r)
(a ←∨) ∩ₛ ↓ = ¬∅ (a ←∨)
(a ←∨) ∩ₛ (b ←∨) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (x ←∨)
(a ←∨) ∩ₛ (∨→ b) = ∅
(a ←∨) ∩ₛ (b ←∨→ b₁) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (x ←∨)
(∨→ a) ∩ₛ ↓ = ¬∅ (∨→ a)
(∨→ a) ∩ₛ (b ←∨) = ∅
(∨→ a) ∩ₛ (∨→ b) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (∨→ x)
(∨→ a) ∩ₛ (b ←∨→ b₁) with (a ∩ₛ b₁)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (∨→ x)
(a ←∨→ a₁) ∩ₛ ↓ = ¬∅ (a ←∨→ a₁)
(a ←∨→ a₁) ∩ₛ (b ←∨) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (x ←∨)
(a ←∨→ a₁) ∩ₛ (∨→ b) with (a₁ ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (∨→ x)
(a ←∨→ a₁) ∩ₛ (b ←∨→ b₁) with (a ∩ₛ b) | (a₁ ∩ₛ b₁)
... | ∅ | ∅ = ∅
... | ∅ | ¬∅ r = ¬∅ (∨→ r)
... | ¬∅ l | ∅ = ¬∅ (l ←∨)
... | ¬∅ l | ¬∅ r = ¬∅ (l ←∨→ r)
(a ←∂) ∩ₛ ↓ = ¬∅ (a ←∂)
(a ←∂) ∩ₛ (b ←∂) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (x ←∂)
(a ←∂) ∩ₛ (∂→ b) = ∅
(a ←∂) ∩ₛ (b ←∂→ b₁) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (x ←∂)
(∂→ a) ∩ₛ ↓ = ¬∅ (∂→ a)
(∂→ a) ∩ₛ (b ←∂) = ∅
(∂→ a) ∩ₛ (∂→ b) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (∂→ x)
(∂→ a) ∩ₛ (b ←∂→ b₁) with (a ∩ₛ b₁)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (∂→ x)
(a ←∂→ a₁) ∩ₛ ↓ = ¬∅ (a ←∂→ a₁)
(a ←∂→ a₁) ∩ₛ (b ←∂) with (a ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (x ←∂)
(a ←∂→ a₁) ∩ₛ (∂→ b) with (a₁ ∩ₛ b)
... | ∅ = ∅
... | ¬∅ x = ¬∅ (∂→ x)
(a ←∂→ a₁) ∩ₛ (b ←∂→ b₁) with (a ∩ₛ b) | (a₁ ∩ₛ b₁)
... | ∅ | ∅ = ∅
... | ∅ | ¬∅ r = ¬∅ (∂→ r)
... | ¬∅ l | ∅ = ¬∅ (l ←∂)
... | ¬∅ l | ¬∅ r = ¬∅ (l ←∂→ r)


fillAllLower : ∀{i u} → ∀ ll → SetLL {i} {u} ll
fillAllLower ∅ = ↓
fillAllLower (τ x) = ↓
fillAllLower (ll₁ ∧ ll₂) = (fillAllLower ll₁) ←∧→ (fillAllLower ll₂)
fillAllLower (ll₁ ∨ ll₂) = (fillAllLower ll₁) ←∨→ (fillAllLower ll₂)
fillAllLower (ll₁ ∂ ll₂) = (fillAllLower ll₁) ←∂→ (fillAllLower ll₂)
fillAllLower (call x) =  ↓


complLₛ : ∀{i u ll} → SetLL {i} {u} ll → MSetLL ll
complLₛ ↓ = ∅
complLₛ (s ←∧) with complLₛ s
... | ∅ = ¬∅ (∧→ (fillAllLower _))
... | ¬∅ r = ¬∅ (r ←∧→ (fillAllLower _))
complLₛ (∧→ s) with complLₛ s 
... | ∅ = ¬∅ ((fillAllLower _) ←∧)
... | ¬∅ r = ¬∅ ((fillAllLower _) ←∧→ r)
complLₛ (s ←∧→ s₁) with complLₛ s | complLₛ s₁
... | ∅ | ∅ = ∅
... | ∅ | ¬∅ r = ¬∅ (∧→ r)
... | ¬∅ l | ∅ = ¬∅ (l ←∧)
... | ¬∅ l | ¬∅ r = ¬∅ (l ←∧→ r)
complLₛ (s ←∨) with complLₛ s
... | ∅ = ¬∅ (∨→ (fillAllLower _))
... | ¬∅ r = ¬∅ (r ←∨→ (fillAllLower _))
complLₛ (∨→ s) with complLₛ s 
... | ∅ = ¬∅ ((fillAllLower _) ←∨)
... | ¬∅ r = ¬∅ ((fillAllLower _) ←∨→ r)
complLₛ (s ←∨→ s₁) with complLₛ s | complLₛ s₁
... | ∅ | ∅ = ∅
... | ∅ | ¬∅ r = ¬∅ (∨→ r)
... | ¬∅ l | ∅ = ¬∅ (l ←∨)
... | ¬∅ l | ¬∅ r = ¬∅ (l ←∨→ r)
complLₛ (s ←∂) with complLₛ s
... | ∅ = ¬∅ (∂→ (fillAllLower _))
... | ¬∅ r = ¬∅ (r ←∂→ (fillAllLower _))
complLₛ (∂→ s) with complLₛ s 
... | ∅ = ¬∅ ((fillAllLower _) ←∂)
... | ¬∅ r = ¬∅ ((fillAllLower _) ←∂→ r)
complLₛ (s ←∂→ s₁) with complLₛ s | complLₛ s₁
... | ∅ | ∅ = ∅
... | ∅ | ¬∅ r = ¬∅ (∂→ r)
... | ¬∅ l | ∅ = ¬∅ (l ←∂)
... | ¬∅ l | ¬∅ r = ¬∅ (l ←∂→ r)





-- Deletes an index if it is present, otherwise does nothing.
del : ∀{i u ll q} → SetLL ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic i)
      → MSetLL (replLL ll ind rll)
del s ↓ rll = ∅
del ↓ (ind ←∧) rll with (del ↓ ind rll)
del ↓ (ind ←∧) rll | ∅ = ¬∅ (∧→ ↓)
del ↓ (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧→ ↓)
del (s ←∧) (ind ←∧) rll with (del s ind rll)
del (s ←∧) (ind ←∧) rll | ∅ = ∅
del (s ←∧) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧)
del (∧→ s) (ind ←∧) rll = ¬∅ (∧→ (s))
del (s ←∧→ s₁) (ind ←∧) rll with (del s ind rll)
del (s ←∧→ s₁) (ind ←∧) rll | ∅ = ¬∅ (∧→ (s₁))
del (s ←∧→ s₁) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧→ (s₁))
del ↓ (∧→ ind) rll with (del ↓ ind rll)
del ↓ (∧→ ind) rll | ∅ = ¬∅ (↓ ←∧)
del ↓ (∧→ ind) rll | ¬∅ x = ¬∅ (↓ ←∧→ x)
del (s ←∧) (∧→ ind) rll = ¬∅ ((s) ←∧)
del (∧→ s) (∧→ ind) rll with (del s ind rll)
del (∧→ s) (∧→ ind) rll | ∅ = ∅
del (∧→ s) (∧→ ind) rll | ¬∅ x = ¬∅ (∧→ x)
del (s ←∧→ s₁) (∧→ ind) rll with (del s₁ ind rll)
del (s ←∧→ s₁) (∧→ ind) rll | ∅ = ¬∅ ((s) ←∧)
del (s ←∧→ s₁) (∧→ ind) rll | ¬∅ x = ¬∅ ((s) ←∧→ x)
del ↓ (ind ←∨) rll with (del ↓ ind rll)
del ↓ (ind ←∨) rll | ∅ = ¬∅ (∨→ ↓)
del ↓ (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨→ ↓)
del (s ←∨) (ind ←∨) rll with (del s ind rll)
del (s ←∨) (ind ←∨) rll | ∅ = ∅
del (s ←∨) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨)
del (∨→ s) (ind ←∨) rll = ¬∅ (∨→ (s))
del (s ←∨→ s₁) (ind ←∨) rll with (del s ind rll)
del (s ←∨→ s₁) (ind ←∨) rll | ∅ = ¬∅ (∨→ (s₁))
del (s ←∨→ s₁) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨→ (s₁))
del ↓ (∨→ ind) rll with (del ↓ ind rll)
del ↓ (∨→ ind) rll | ∅ = ¬∅ (↓ ←∨)
del ↓ (∨→ ind) rll | ¬∅ x = ¬∅ (↓ ←∨→ x)
del (s ←∨) (∨→ ind) rll = ¬∅ ((s) ←∨)
del (∨→ s) (∨→ ind) rll with (del s ind rll)
del (∨→ s) (∨→ ind) rll | ∅ = ∅
del (∨→ s) (∨→ ind) rll | ¬∅ x = ¬∅ (∨→ x)
del (s ←∨→ s₁) (∨→ ind) rll with (del s₁ ind rll)
del (s ←∨→ s₁) (∨→ ind) rll | ∅ = ¬∅ ((s) ←∨)
del (s ←∨→ s₁) (∨→ ind) rll | ¬∅ x = ¬∅ ((s) ←∨→ x)
del ↓ (ind ←∂) rll with (del ↓ ind rll)
del ↓ (ind ←∂) rll | ∅ = ¬∅ (∂→ ↓)
del ↓ (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂→ ↓)
del (s ←∂) (ind ←∂) rll with (del s ind rll)
del (s ←∂) (ind ←∂) rll | ∅ = ∅
del (s ←∂) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂)
del (∂→ s) (ind ←∂) rll = ¬∅ (∂→ (s))
del (s ←∂→ s₁) (ind ←∂) rll with (del s ind rll)
del (s ←∂→ s₁) (ind ←∂) rll | ∅ = ¬∅ (∂→ (s₁))
del (s ←∂→ s₁) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂→ (s₁))
del ↓ (∂→ ind) rll with (del ↓ ind rll)
del ↓ (∂→ ind) rll | ∅ = ¬∅ (↓ ←∂)
del ↓ (∂→ ind) rll | ¬∅ x = ¬∅ (↓ ←∂→ x)
del (s ←∂) (∂→ ind) rll = ¬∅ ((s) ←∂)
del (∂→ s) (∂→ ind) rll with (del s ind rll)
del (∂→ s) (∂→ ind) rll | ∅ = ∅
del (∂→ s) (∂→ ind) rll | ¬∅ x = ¬∅ (∂→ x)
del (s ←∂→ s₁) (∂→ ind) rll with (del s₁ ind rll)
del (s ←∂→ s₁) (∂→ ind) rll | ∅ = ¬∅ ((s) ←∂)
del (s ←∂→ s₁) (∂→ ind) rll | ¬∅ x = ¬∅ ((s) ←∂→ x)



--extend : ∀{i u ll pll} → IndexLL {i} {u} pll ll → SetLL pll → SetLL ll
--extend ↓ s = s
--extend (ind ←∧) s = (extend ind s) ←∧
--extend (∧→ ind) s = ∧→ (extend ind s) 
--extend (ind ←∨) s = (extend ind s) ←∨
--extend (∨→ ind) s = ∨→ (extend ind s) 
--extend (ind ←∂) s = (extend ind s) ←∂
--extend (∂→ ind) s = ∂→ (extend ind s) 
--

extend : ∀{i u ll q} → ∀{rll} → (ind : IndexLL {i} {u} q ll) → SetLL {i} rll → SetLL (replLL ll ind rll)
extend ↓ b = b
extend (ind ←∧) b = (extend ind b) ←∧
extend (∧→ ind) b = ∧→ (extend ind b)
extend (ind ←∨) b = (extend ind b) ←∨
extend (∨→ ind) b = ∨→ (extend ind b)
extend (ind ←∂) b = (extend ind b) ←∂
extend (∂→ ind) b = ∂→ (extend ind b)




module _ where

  
  replacePartOf_to_at_ : ∀{i u ll q} → ∀{rll} → SetLL ll → SetLL {i} rll → (ind : IndexLL {i} {u} q ll)
            → SetLL (replLL ll ind rll)
  replacePartOf a to b at ↓               = b
  replacePartOf ↓ to b at (ind ←∧)        = (replacePartOf ↓ to b at ind) ←∧→ ↓
  replacePartOf a ←∧ to b at (ind ←∧)     = (replacePartOf a to b at ind) ←∧
  replacePartOf_to_at_ {q = q} {rll = rll} (∧→ a) b (ind ←∧) = (extend ind b) ←∧→ (a)
  replacePartOf a ←∧→ a₁ to b at (ind ←∧) = (replacePartOf a to b at ind) ←∧→ (a₁)
  replacePartOf ↓ to b at (∧→ ind)        =  ↓ ←∧→ (replacePartOf ↓ to b at ind)
  replacePartOf a ←∧ to b at (∧→ ind)     = (a) ←∧→ (extend ind b)  
  replacePartOf ∧→ a to b at (∧→ ind)     = ∧→ (replacePartOf a to b at ind)
  replacePartOf a ←∧→ a₁ to b at (∧→ ind) = (a) ←∧→ (replacePartOf a₁ to b at ind)
  replacePartOf ↓ to b at (ind ←∨)        = (replacePartOf ↓ to b at ind) ←∨→ ↓
  replacePartOf a ←∨ to b at (ind ←∨)     = (replacePartOf a to b at ind) ←∨
  replacePartOf_to_at_ {q = q} {rll = rll} (∨→ a) b (ind ←∨) = (extend ind b) ←∨→ (a)
  replacePartOf a ←∨→ a₁ to b at (ind ←∨) = (replacePartOf a to b at ind) ←∨→ (a₁)
  replacePartOf ↓ to b at (∨→ ind)        =  ↓ ←∨→ (replacePartOf ↓ to b at ind)
  replacePartOf a ←∨ to b at (∨→ ind)     = (a) ←∨→ (extend ind b)  
  replacePartOf ∨→ a to b at (∨→ ind)     = ∨→ (replacePartOf a to b at ind)
  replacePartOf a ←∨→ a₁ to b at (∨→ ind) = (a) ←∨→ (replacePartOf a₁ to b at ind)
  replacePartOf ↓ to b at (ind ←∂)        = (replacePartOf ↓ to b at ind) ←∂→ ↓
  replacePartOf a ←∂ to b at (ind ←∂)     = (replacePartOf a to b at ind) ←∂
  replacePartOf_to_at_ {q = q} {rll = rll} (∂→ a) b (ind ←∂) = (extend ind b) ←∂→ (a)
  replacePartOf a ←∂→ a₁ to b at (ind ←∂) = (replacePartOf a to b at ind) ←∂→ (a₁)
  replacePartOf ↓ to b at (∂→ ind)        =  ↓ ←∂→ (replacePartOf ↓ to b at ind)
  replacePartOf a ←∂ to b at (∂→ ind)     = (a) ←∂→ (extend ind b)  
  replacePartOf ∂→ a to b at (∂→ ind)     = ∂→ (replacePartOf a to b at ind)
  replacePartOf a ←∂→ a₁ to b at (∂→ ind) = (a) ←∂→ (replacePartOf a₁ to b at ind)


  mreplacePartOf_to_at_ : ∀{i u ll q} → ∀{rll} → MSetLL ll → MSetLL {i} rll → (ind : IndexLL {i} {u} q ll)
            → MSetLL (replLL ll ind rll)
  mreplacePartOf ∅ to ∅ at ind = ∅
  mreplacePartOf_to_at_ {q = q} {rll = rll} ∅ (¬∅ x) ind = ¬∅ (extend ind x)
  mreplacePartOf_to_at_ {rll = rll} (¬∅ x) ∅ ind = del x ind rll
  mreplacePartOf ¬∅ x to ¬∅ x₁ at ind = ¬∅ (replacePartOf x to x₁ at ind)


module _ {u} where

  open Relation.Binary.PropositionalEquality

  open import Data.Maybe
  open import Data.Product
  open import Category.Monad
  open RawMonad {f = lsuc u} (monad)

 -- This might not be used. 
  setToIndex : ∀{i ll} → SetLL {i} {u} ll → Maybe $ Σ (LinLogic i {u}) (λ x → IndexLL x ll)
  setToIndex {ll = ll} ↓ = just (ll , ↓)
  setToIndex (s ←∧) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ind ←∧) })
  setToIndex (∧→ s) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ∧→ ind) })
  setToIndex (s ←∧→ s₁) = nothing
  setToIndex (s ←∨) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ind ←∨) })
  setToIndex (∨→ s) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ∨→ ind) })
  setToIndex (s ←∨→ s₁) = nothing
  setToIndex (s ←∂) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ind ←∂) })
  setToIndex (∂→ s) = setToIndex s >>= (λ { (pll , ind)  → just (pll , ∂→ ind) })
  setToIndex (s ←∂→ s₁) = nothing
  
  msetToIndex : ∀{i ll} → MSetLL {i} {u} ll → Maybe $ Σ (LinLogic i {u}) (λ x → IndexLL x ll)
  msetToIndex ∅ = nothing
  msetToIndex (¬∅ x) = setToIndex x

-- This is used.
  pickOne : ∀{i ll} → SetLL {i} {u} ll → Σ (LinLogic i {u}) (λ x → IndexLL x ll)
  pickOne {ll = ll} ↓ = ll , ↓
  pickOne (s ←∧) = (rll , ind ←∧) where
    n = pickOne s
    rll = proj₁ n
    ind = proj₂ n
  pickOne (∧→ s) = (rll , ∧→ ind) where
    n = pickOne s
    rll = proj₁ n
    ind = proj₂ n
  pickOne (s ←∧→ s₁) = rll , ind ←∧ where
    n = pickOne s
    rll = proj₁ n
    ind = proj₂ n
  pickOne (s ←∨) = rll , ind ←∨ where
    n = pickOne s
    rll = proj₁ n
    ind = proj₂ n
  pickOne (∨→ s) = rll , ∨→ ind where
    n = pickOne s
    rll = proj₁ n
    ind = proj₂ n
  pickOne (s ←∨→ s₁) = rll , ind ←∨ where
    n = pickOne s
    rll = proj₁ n
    ind = proj₂ n
  pickOne (s ←∂) = rll , ind ←∂ where
    n = pickOne s
    rll = proj₁ n
    ind = proj₂ n
  pickOne (∂→ s) = rll , ∂→ ind where
    n = pickOne s
    rll = proj₁ n
    ind = proj₂ n
  pickOne (s ←∂→ s₁) = rll , ind ←∂ where
    n = pickOne s
    rll = proj₁ n
    ind = proj₂ n

  pickadd-id : ∀{i pll ll} → (ind : IndexLL {i} {u} pll ll) → (pickOne (subst (λ x → SetLL x) (replLL-id ll ind pll refl) (∅-add ind pll))) ≡ (pll , ind)
  pickadd-id ↓ = refl
  pickadd-id {pll = pll} {ll = li ∧ ri} (ind ←∧) with replLL li ind pll | replLL-id li ind pll refl | oa | pickadd-id ind where
    oa = ∅-add ind pll
  pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∧ ri} (.(proj₂ (pickOne oa)) ←∧) | .li | refl | oa | refl = refl
  pickadd-id {pll = pll} {ll = li ∧ ri} (∧→ ind) with replLL ri ind pll | replLL-id ri ind pll refl | oa | pickadd-id ind where
    oa = ∅-add ind pll
  pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∧ ri} (∧→ .(proj₂ (pickOne oa))) | .ri | refl | oa | refl = refl
  pickadd-id {pll = pll} {ll = li ∨ ri} (ind ←∨) with replLL li ind pll | replLL-id li ind pll refl | oa | pickadd-id ind where
    oa = ∅-add ind pll
  pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∨ ri} (.(proj₂ (pickOne oa)) ←∨) | .li | refl | oa | refl = refl
  pickadd-id {pll = pll} {ll = li ∨ ri} (∨→ ind) with replLL ri ind pll | replLL-id ri ind pll refl | oa | pickadd-id ind where
    oa = ∅-add ind pll
  pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∨ ri} (∨→ .(proj₂ (pickOne oa))) | .ri | refl | oa | refl = refl
  pickadd-id {pll = pll} {ll = li ∂ ri} (ind ←∂) with replLL li ind pll | replLL-id li ind pll refl | oa | pickadd-id ind where
    oa = ∅-add ind pll
  pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∂ ri} (.(proj₂ (pickOne oa)) ←∂) | .li | refl | oa | refl = refl
  pickadd-id {pll = pll} {ll = li ∂ ri} (∂→ ind) with replLL ri ind pll | replLL-id ri ind pll refl | oa | pickadd-id ind where
    oa = ∅-add ind pll
  pickadd-id {pll = .(proj₁ (pickOne oa))} {li ∂ ri} (∂→ .(proj₂ (pickOne oa))) | .ri | refl | oa | refl = refl


-- TODO This is used in LinFun.agda Mybe we need to place it there.
module _ where

-- UsesInput tries to find that all inputs have been used. By definition, calls are not to be used unless observed.
-- Thus we need to add them in the set.
-- Since LinLogic calls can only be consumed by LinFun calls, we can add them when we reach the appropriate LinFun call.

  open Data.List
  open import Data.Product


  findCalls : ∀{i u} → (ll : LinLogic i {u}) → List (Σ (LinLogic i {u}) (λ pll → IndexLL pll ll))
  findCalls ∅ = []
  findCalls (τ x) = []
  findCalls (li ∧ ri) = (Data.List.map (λ x → ((proj₁ x) , (proj₂ x) ←∧)) (findCalls li)) ++ (Data.List.map (λ x → ((proj₁ x) , ∧→ (proj₂ x) )) (findCalls ri))
  findCalls (li ∨ ri) = (Data.List.map (λ x → ((proj₁ x) , (proj₂ x) ←∨)) (findCalls li)) ++ (Data.List.map (λ x → ((proj₁ x) , ∨→ (proj₂ x) )) (findCalls ri))
  findCalls (li ∂ ri) = (Data.List.map (λ x → ((proj₁ x) , (proj₂ x) ←∂)) (findCalls li)) ++ (Data.List.map (λ x → ((proj₁ x) , ∂→ (proj₂ x) )) (findCalls ri))
  findCalls ll@(call x) = [(ll , ↓) ]


  fillWithCalls : ∀{i u} → (ll : LinLogic i {u}) → MSetLL ll
  fillWithCalls ll with (findCalls ll)
  fillWithCalls ll | [] = ∅
  fillWithCalls ll | x ∷ xs with (∅-add (proj₂ x) (proj₁ x))
  ... | r with (replLL ll (proj₂ x) (proj₁ x)) | (replLL-id ll (proj₂ x) (proj₁ x) refl) 
  fillWithCalls {i} {u} ll | x ∷ xs | r | .ll | refl = ¬∅ $ foldl hf r xs where
    hf : SetLL ll → Σ (LinLogic i {u}) (λ pll → IndexLL pll ll) → SetLL ll
    hf s ind with (add s (proj₂ x) (proj₁ x))
    ... | r with (replLL ll (proj₂ x) (proj₁ x)) | (replLL-id ll (proj₂ x) (proj₁ x) refl)
    hf s ind | r₁ | _ | refl = r₁



-- Decidable Equality
isEq : {i : Size} → ∀{u} → {ll : LinLogic i {u}} → (a : SetLL ll) → (b : SetLL ll) → Dec (a ≡ b)
isEq ↓ ↓ = yes refl 
isEq ↓ (b ←∧) = no (λ ())
isEq ↓ (∧→ b) = no (λ ())
isEq ↓ (b ←∧→ b₁) = no (λ ()) 
isEq ↓ (b ←∨) = no (λ ()) 
isEq ↓ (∨→ b) = no (λ ()) 
isEq ↓ (b ←∨→ b₁) = no (λ ())
isEq ↓ (b ←∂) = no (λ ())
isEq ↓ (∂→ b) = no (λ ())
isEq ↓ (b ←∂→ b₁) = no (λ ())
isEq (a ←∧) ↓ = no (λ ())
isEq {ll = lll ∧ llr} (a ←∧) (b ←∧) with (isEq a b)
isEq {ll = lll ∧ llr} (a ←∧) (b ←∧)  | yes p with p
isEq {ll = lll ∧ llr} (a ←∧) (.a ←∧) | yes p | refl = yes refl
isEq {ll = lll ∧ llr} (a ←∧) (b ←∧)  | no ¬p = no (hf) where
  hf : (((SetLL (lll ∧ llr)) ∋ (a ←∧)) ≡ (b ←∧)) → ⊥
  hf refl = ¬p refl
isEq (a ←∧) (∧→ b) = no (λ ())
isEq (a ←∧) (b ←∧→ b₁) = no (λ ())
isEq (∧→ a) ↓ = no (λ ())
isEq (∧→ a) (b ←∧) = no (λ ())
isEq {ll = lll ∧ llr} (∧→ a) (∧→ b) with (isEq a b)
isEq {ll = lll ∧ llr} (∧→ a) (∧→ b)  | yes p with p
isEq {ll = lll ∧ llr} (∧→ a) (∧→ .a) | yes p | refl = yes refl
isEq {ll = lll ∧ llr} (∧→ a) (∧→ b)  | no ¬p = no (hf) where
  hf : (((SetLL (lll ∧ llr)) ∋ (∧→ a)) ≡ (∧→ b)) → ⊥
  hf refl = ¬p refl
isEq (∧→ a) (b ←∧→ b₁) = no (λ ())
isEq (a ←∧→ a₁) ↓ = no (λ ())
isEq (a ←∧→ a₁) (b ←∧) = no (λ ())
isEq (a ←∧→ a₁) (∧→ b) = no (λ ())
isEq (a ←∧→ a₁) (b ←∧→ b₁) with (isEq a b)
isEq (a ←∧→ a₁) (b ←∧→ b₁) | yes p with (isEq a₁ b₁)
isEq (a ←∧→ a₁) (b ←∧→ b₁) | yes p₁ | (yes p) with p₁ | p
isEq (a ←∧→ a₁) (.a ←∧→ .a₁) | yes p₁ | (yes p) | refl | refl = yes refl
isEq (a ←∧→ a₁) (b ←∧→ b₁) | yes p | (no ¬p) = no (hf) where 
  hf : (a ←∧→ a₁) ≡ (b ←∧→ b₁) → ⊥
  hf refl = ¬p refl
isEq (a ←∧→ a₁) (b ←∧→ b₁) | no ¬p = no (hf) where
  hf : (a ←∧→ a₁) ≡ (b ←∧→ b₁) → ⊥
  hf refl = ¬p refl
isEq (a ←∨) ↓ = no (λ ())
isEq {ll = lll ∨ llr} (a ←∨) (b ←∨) with (isEq a b)
isEq {ll = lll ∨ llr} (a ←∨) (b ←∨)  | yes p with p
isEq {ll = lll ∨ llr} (a ←∨) (.a ←∨) | yes p | refl = yes refl
isEq {ll = lll ∨ llr} (a ←∨) (b ←∨)  | no ¬p = no (hf) where
  hf : (((SetLL (lll ∨ llr)) ∋ (a ←∨)) ≡ (b ←∨)) → ⊥
  hf refl = ¬p refl
isEq (a ←∨) (∨→ b) = no (λ ())
isEq (a ←∨) (b ←∨→ b₁) = no (λ ())
isEq (∨→ a) ↓ = no (λ ())
isEq (∨→ a) (b ←∨) = no (λ ())
isEq {ll = lll ∨ llr} (∨→ a) (∨→ b) with (isEq a b)
isEq {ll = lll ∨ llr} (∨→ a) (∨→ b)  | yes p with p
isEq {ll = lll ∨ llr} (∨→ a) (∨→ .a) | yes p | refl = yes refl
isEq {ll = lll ∨ llr} (∨→ a) (∨→ b)  | no ¬p = no (hf) where
  hf : (((SetLL (lll ∨ llr)) ∋ (∨→ a)) ≡ (∨→ b)) → ⊥
  hf refl = ¬p refl
isEq (∨→ a) (b ←∨→ b₁) = no (λ ())
isEq (a ←∨→ a₁) ↓ = no (λ ())
isEq (a ←∨→ a₁) (b ←∨) = no (λ ())
isEq (a ←∨→ a₁) (∨→ b) = no (λ ())
isEq (a ←∨→ a₁) (b ←∨→ b₁) with (isEq a b)
isEq (a ←∨→ a₁) (b ←∨→ b₁) | yes p with (isEq a₁ b₁)
isEq (a ←∨→ a₁) (b ←∨→ b₁) | yes p₁ | (yes p) with p₁ | p
isEq (a ←∨→ a₁) (.a ←∨→ .a₁) | yes p₁ | (yes p) | refl | refl = yes refl
isEq (a ←∨→ a₁) (b ←∨→ b₁) | yes p | (no ¬p) = no (hf) where 
  hf : (a ←∨→ a₁) ≡ (b ←∨→ b₁) → ⊥
  hf refl = ¬p refl
isEq (a ←∨→ a₁) (b ←∨→ b₁) | no ¬p = no (hf) where
  hf : (a ←∨→ a₁) ≡ (b ←∨→ b₁) → ⊥
  hf refl = ¬p refl
isEq (a ←∂) ↓ = no (λ ())
isEq {ll = lll ∂ llr} (a ←∂) (b ←∂) with (isEq a b)
isEq {ll = lll ∂ llr} (a ←∂) (b ←∂)  | yes p with p
isEq {ll = lll ∂ llr} (a ←∂) (.a ←∂) | yes p | refl = yes refl
isEq {ll = lll ∂ llr} (a ←∂) (b ←∂)  | no ¬p = no (hf) where
  hf : (((SetLL (lll ∂ llr)) ∋ (a ←∂)) ≡ (b ←∂)) → ⊥
  hf refl = ¬p refl
isEq (a ←∂) (∂→ b) = no (λ ())
isEq (a ←∂) (b ←∂→ b₁) = no (λ ())
isEq (∂→ a) ↓ = no (λ ())
isEq (∂→ a) (b ←∂) = no (λ ())
isEq {ll = lll ∂ llr} (∂→ a) (∂→ b) with (isEq a b)
isEq {ll = lll ∂ llr} (∂→ a) (∂→ b)  | yes p with p
isEq {ll = lll ∂ llr} (∂→ a) (∂→ .a) | yes p | refl = yes refl
isEq {ll = lll ∂ llr} (∂→ a) (∂→ b)  | no ¬p = no (hf) where
  hf : (((SetLL (lll ∂ llr)) ∋ (∂→ a)) ≡ (∂→ b)) → ⊥
  hf refl = ¬p refl
isEq (∂→ a) (b ←∂→ b₁) = no (λ ())
isEq (a ←∂→ a₁) ↓ = no (λ ())
isEq (a ←∂→ a₁) (b ←∂) = no (λ ())
isEq (a ←∂→ a₁) (∂→ b) = no (λ ())
isEq (a ←∂→ a₁) (b ←∂→ b₁) with (isEq a b)
isEq (a ←∂→ a₁) (b ←∂→ b₁) | yes p with (isEq a₁ b₁)
isEq (a ←∂→ a₁) (b ←∂→ b₁) | yes p₁ | (yes p) with p₁ | p
isEq (a ←∂→ a₁) (.a ←∂→ .a₁) | yes p₁ | (yes p) | refl | refl = yes refl
isEq (a ←∂→ a₁) (b ←∂→ b₁) | yes p | (no ¬p) = no (hf) where 
  hf : (a ←∂→ a₁) ≡ (b ←∂→ b₁) → ⊥
  hf refl = ¬p refl
isEq (a ←∂→ a₁) (b ←∂→ b₁) | no ¬p = no (hf) where
  hf : (a ←∂→ a₁) ≡ (b ←∂→ b₁) → ⊥
  hf refl = ¬p refl


isEqM : {i : Size} → ∀{u} → {ll : LinLogic i {u}} → (a : MSetLL ll) → (b : MSetLL ll) → Dec (a ≡ b)
isEqM ∅ ∅ = yes refl
isEqM ∅ (¬∅ x) = no (λ ())
isEqM (¬∅ x) ∅ = no (λ ())
isEqM (¬∅ x) (¬∅ x₁) with (isEq x x₁)
isEqM (¬∅ x) (¬∅ .x) | yes refl = yes refl
isEqM (¬∅ x) (¬∅ x₁) | no ¬p = no (λ {refl → ¬p refl})

-- If two adjacent nodes exist in the set, the higher node is in the set.
-- We contruct the set.
contruct : ∀{i u ll} → SetLL {i} {u} ll → SetLL ll
contruct ↓          = ↓
contruct (x ←∧)     = (contruct x) ←∧
contruct (∧→ x)     = ∧→ (contruct x)
contruct (x ←∧→ x₁) with contruct x | contruct x₁
... | ↓ | ↓ = ↓
{-# CATCHALL #-}
... | g | r = (g ←∧→ r)
contruct (x ←∨)     = (contruct x) ←∨
contruct (∨→ x)     = ∨→ (contruct x)
contruct (x ←∨→ x₁) with contruct x | contruct x₁
... | ↓ | ↓ = ↓
{-# CATCHALL #-}
... | g | r = (g ←∨→ r)
contruct (x ←∂)     = (contruct x) ←∂
contruct (∂→ x)     = ∂→ (contruct x)
contruct (x ←∂→ x₁) with contruct x | contruct x₁
... | ↓ | ↓ = ↓
{-# CATCHALL #-}
... | g | r = (g ←∂→ r)


mcontruct : ∀{i u ll} → MSetLL {i} {u} ll → MSetLL ll
mcontruct ∅ = ∅
mcontruct (¬∅ x) = ¬∅ $ contruct x



-- This might not be used now but it might be used in the future, when I finish implementing the cut.

-- Resource-aware contruction used in cuttable. A node will only receive one resource from ∂ or ∨, by their semantic definition,
-- thus here we contruct based on whether the specific subtree has all the possible resources that it could
-- get from the network.
res-contruct : ∀{i u ll} → SetLL {i} {u} ll → SetLL ll
res-contruct ↓          = ↓
res-contruct (x ←∧)     = (res-contruct x) ←∧
res-contruct (∧→ x)     = ∧→ (res-contruct x)
res-contruct (x ←∧→ x₁) with res-contruct x | res-contruct x₁
... | ↓ | ↓ = ↓
{-# CATCHALL #-}
... | g | r = (g ←∧→ r)
res-contruct (x ←∨) with res-contruct x
... | ↓ = ↓
{-# CATCHALL #-}
... | g = (g ←∨)
res-contruct (∨→ x) with res-contruct x 
... | ↓ = ↓
{-# CATCHALL #-}
... | g = (∨→ g)
res-contruct (x ←∨→ x₁) with res-contruct x | res-contruct x₁
... | ↓ | ↓ = ↓
{-# CATCHALL #-}
... | g | r = (g ←∨→ r)
res-contruct (x ←∂) with res-contruct x
... | ↓ = ↓
{-# CATCHALL #-}
... | g = (g ←∂)
res-contruct (∂→ x) with res-contruct x
... | ↓ = ↓
{-# CATCHALL #-}
... | g = (∂→ g)
res-contruct (x ←∂→ x₁) with res-contruct x | res-contruct x₁
... | ↓ | ↓ = ↓
{-# CATCHALL #-}
... | g | r = (g ←∂→ r)




-- If we transform the linear logic tree, we need to transform the SetLL as well.
tran : ∀ {i u ll rll} → SetLL ll → (tr : LLTr {i} {u} rll ll)
       → SetLL rll
tran s I                           = s
tran ↓ (∂c tr)                     = ↓
tran (s ←∂) (∂c tr)                = tran (∂→ s) tr
tran (∂→ s) (∂c tr)                = tran (s ←∂) tr
tran (s ←∂→ s₁) (∂c tr)            = tran (s₁ ←∂→ s) tr
tran ↓ (∨c tr)                     = ↓
tran (s ←∨) (∨c tr)                = tran (∨→ s) tr
tran (∨→ s) (∨c tr)                = tran (s ←∨) tr
tran (s ←∨→ s₁) (∨c tr)            = tran (s₁ ←∨→ s) tr
tran ↓ (∧c tr)                     = ↓
tran (s ←∧) (∧c tr)                = tran (∧→ s) tr
tran (∧→ s) (∧c tr)                = tran (s ←∧) tr
tran (s ←∧→ s₁) (∧c tr)            = tran (s₁ ←∧→ s) tr
tran ↓ (∧∧d tr)                    = ↓
tran (↓ ←∧) (∧∧d tr)               = tran (↓ ←∧→ (↓ ←∧)) tr
tran ((s ←∧) ←∧) (∧∧d tr)          = tran (s ←∧) tr
tran ((∧→ s) ←∧) (∧∧d tr)          = tran (∧→ (s ←∧)) tr
tran ((s ←∧→ s₁) ←∧) (∧∧d tr)      = tran (s ←∧→ (s₁ ←∧)) tr
tran (∧→ s) (∧∧d tr)               = tran (∧→ (∧→ s)) tr
tran (↓ ←∧→ s₁) (∧∧d tr)           = tran (↓ ←∧→ (↓ ←∧→ s₁)) tr
tran ((s ←∧) ←∧→ s₁) (∧∧d tr)      = tran (s ←∧→ (∧→ s₁)) tr
tran ((∧→ s) ←∧→ s₁) (∧∧d tr)      = tran (∧→ (s ←∧→ s₁)) tr
tran ((s ←∧→ s₁) ←∧→ s₂) (∧∧d tr)  = tran (s ←∧→ (s₁ ←∧→ s₂)) tr
tran ↓ (¬∧∧d tr)                   = ↓
tran (s ←∧) (¬∧∧d tr)              = tran ((s ←∧) ←∧) tr
tran (∧→ ↓) (¬∧∧d tr)              = tran ((∧→ ↓) ←∧→ ↓) tr
tran (∧→ (s ←∧)) (¬∧∧d tr)         = tran ((∧→ s) ←∧) tr
tran (∧→ (∧→ s)) (¬∧∧d tr)         = tran (∧→ s) tr
tran (∧→ (s ←∧→ s₁)) (¬∧∧d tr)     = tran ((∧→ s) ←∧→ s₁) tr
tran (s ←∧→ ↓) (¬∧∧d tr)           = tran ((s ←∧→ ↓) ←∧→ ↓) tr
tran (s ←∧→ (s₁ ←∧)) (¬∧∧d tr)     = tran ((s ←∧→ s₁) ←∧) tr
tran (s ←∧→ (∧→ s₁)) (¬∧∧d tr)     = tran ((s ←∧) ←∧→ s₁) tr
tran (s ←∧→ (s₁ ←∧→ s₂)) (¬∧∧d tr) = tran ((s ←∧→ s₁) ←∧→ s₂) tr
tran ↓ (∨∨d tr)                    = ↓
tran (↓ ←∨) (∨∨d tr)               = tran (↓ ←∨→ (↓ ←∨)) tr
tran ((s ←∨) ←∨) (∨∨d tr)          = tran (s ←∨) tr
tran ((∨→ s) ←∨) (∨∨d tr)          = tran (∨→ (s ←∨)) tr
tran ((s ←∨→ s₁) ←∨) (∨∨d tr)      = tran (s ←∨→ (s₁ ←∨)) tr
tran (∨→ s) (∨∨d tr)               = tran (∨→ (∨→ s)) tr
tran (↓ ←∨→ s₁) (∨∨d tr)           = tran (↓ ←∨→ (↓ ←∨→ s₁)) tr
tran ((s ←∨) ←∨→ s₁) (∨∨d tr)      = tran (s ←∨→ (∨→ s₁)) tr
tran ((∨→ s) ←∨→ s₁) (∨∨d tr)      = tran (∨→ (s ←∨→ s₁)) tr
tran ((s ←∨→ s₁) ←∨→ s₂) (∨∨d tr)  = tran (s ←∨→ (s₁ ←∨→ s₂)) tr
tran ↓ (¬∨∨d tr)                   = ↓
tran (s ←∨) (¬∨∨d tr)              = tran ((s ←∨) ←∨) tr
tran (∨→ ↓) (¬∨∨d tr)              = tran ((∨→ ↓) ←∨→ ↓) tr
tran (∨→ (s ←∨)) (¬∨∨d tr)         = tran ((∨→ s) ←∨) tr
tran (∨→ (∨→ s)) (¬∨∨d tr)         = tran (∨→ s) tr
tran (∨→ (s ←∨→ s₁)) (¬∨∨d tr)     = tran ((∨→ s) ←∨→ s₁) tr
tran (s ←∨→ ↓) (¬∨∨d tr)           = tran ((s ←∨→ ↓) ←∨→ ↓) tr
tran (s ←∨→ (s₁ ←∨)) (¬∨∨d tr)     = tran ((s ←∨→ s₁) ←∨) tr
tran (s ←∨→ (∨→ s₁)) (¬∨∨d tr)     = tran ((s ←∨) ←∨→ s₁) tr
tran (s ←∨→ (s₁ ←∨→ s₂)) (¬∨∨d tr) = tran ((s ←∨→ s₁) ←∨→ s₂) tr
tran ↓ (∂∂d tr)                    = ↓
tran (↓ ←∂) (∂∂d tr)               = tran (↓ ←∂→ (↓ ←∂)) tr
tran ((s ←∂) ←∂) (∂∂d tr)          = tran (s ←∂) tr
tran ((∂→ s) ←∂) (∂∂d tr)          = tran (∂→ (s ←∂)) tr
tran ((s ←∂→ s₁) ←∂) (∂∂d tr)      = tran (s ←∂→ (s₁ ←∂)) tr
tran (∂→ s) (∂∂d tr)               = tran (∂→ (∂→ s)) tr
tran (↓ ←∂→ s₁) (∂∂d tr)           = tran (↓ ←∂→ (↓ ←∂→ s₁)) tr
tran ((s ←∂) ←∂→ s₁) (∂∂d tr)      = tran (s ←∂→ (∂→ s₁)) tr
tran ((∂→ s) ←∂→ s₁) (∂∂d tr)      = tran (∂→ (s ←∂→ s₁)) tr
tran ((s ←∂→ s₁) ←∂→ s₂) (∂∂d tr)  = tran (s ←∂→ (s₁ ←∂→ s₂)) tr
tran ↓ (¬∂∂d tr)                   = ↓
tran (s ←∂) (¬∂∂d tr)              = tran ((s ←∂) ←∂) tr
tran (∂→ ↓) (¬∂∂d tr)              = tran ((∂→ ↓) ←∂→ ↓) tr
tran (∂→ (s ←∂)) (¬∂∂d tr)         = tran ((∂→ s) ←∂) tr
tran (∂→ (∂→ s)) (¬∂∂d tr)         = tran (∂→ s) tr
tran (∂→ (s ←∂→ s₁)) (¬∂∂d tr)     = tran ((∂→ s) ←∂→ s₁) tr
tran (s ←∂→ ↓) (¬∂∂d tr)           = tran ((s ←∂→ ↓) ←∂→ ↓) tr
tran (s ←∂→ (s₁ ←∂)) (¬∂∂d tr)     = tran ((s ←∂→ s₁) ←∂) tr
tran (s ←∂→ (∂→ s₁)) (¬∂∂d tr)     = tran ((s ←∂) ←∂→ s₁) tr
tran (s ←∂→ (s₁ ←∂→ s₂)) (¬∂∂d tr) = tran ((s ←∂→ s₁) ←∂→ s₂) tr




-- Transformations that start from a specific index.
itran : ∀ {i u ll rll pll} → SetLL ll → (ind : IndexLL {i} {u} pll ll) → (tr : LLTr rll pll)
        → SetLL (replLL ll ind rll)
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




truncSetLL : ∀ {i u ll pll} → SetLL ll → (ind : IndexLL {i} {u} pll ll)
             → MSetLL pll
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




data _≤s_ {i : Size} {u} : {ll : LinLogic i {u}} → SetLL ll → SetLL ll → Set where
  ≤id   : ∀{ll s} → _≤s_ {ll = ll} s s
  ≤←∧  : ∀{lll llr sx sy} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∧ llr} (sx ←∧) (sy ←∧)
  ≤∧→  : ∀{lll llr sx sy} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∧ llr} (∧→ sx) (∧→ sy)
  ≤←∨  : ∀{lll llr sx sy} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∨ llr} (sx ←∨) (sy ←∨)
  ≤∨→  : ∀{lll llr sx sy} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∨ llr} (∨→ sx) (∨→ sy)
  ≤←∂  : ∀{lll llr sx sy} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∂ llr} (sx ←∂) (sy ←∂)
  ≤∂→  : ∀{lll llr sx sy} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∂ llr} (∂→ sx) (∂→ sy)
  ≤←∧→ : ∀{lll llr slx sly srx sry} → _≤s_ {ll = lll} slx sly → _≤s_ {ll = llr} srx sry → _≤s_ {ll = lll ∧ llr} (slx ←∧→ srx) (sly ←∧→ sry)
  ≤←∨→ : ∀{lll llr slx sly srx sry} → _≤s_ {ll = lll} slx sly → _≤s_ {ll = llr} srx sry → _≤s_ {ll = lll ∨ llr} (slx ←∨→ srx) (sly ←∨→ sry)
  ≤←∂→ : ∀{lll llr slx sly srx sry} → _≤s_ {ll = lll} slx sly → _≤s_ {ll = llr} srx sry → _≤s_ {ll = lll ∂ llr} (slx ←∂→ srx) (sly ←∂→ sry)
  ≤d←∧ : ∀{lll llr sx sy s} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∧ llr} (sx ←∧) (sy ←∧→ s)
  ≤d∧→ : ∀{lll llr sx sy s} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∧ llr} (∧→ sx) (s ←∧→ sy)
  ≤d←∨ : ∀{lll llr sx sy s} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∨ llr} (sx ←∨) (sy ←∨→ s)
  ≤d∨→ : ∀{lll llr sx sy s} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∨ llr} (∨→ sx) (s ←∨→ sy)
  ≤d←∂ : ∀{lll llr sx sy s} → _≤s_ {ll = lll} sx sy → _≤s_ {ll = lll ∂ llr} (sx ←∂) (sy ←∂→ s)
  ≤d∂→ : ∀{lll llr sx sy s} → _≤s_ {ll = llr} sx sy → _≤s_ {ll = lll ∂ llr} (∂→ sx) (s ←∂→ sy)





≤s-ext : ∀{i u pll ll q ss} → (ind : IndexLL {i} {u} q ll) → {s : SetLL pll} → ss ≤s s → extend ind ss ≤s extend ind s
≤s-ext ↓ ss≤s = ss≤s
≤s-ext (ind ←∧) ss≤s = ≤←∧ (≤s-ext ind ss≤s)
≤s-ext (∧→ ind) ss≤s = ≤∧→ (≤s-ext ind ss≤s)
≤s-ext (ind ←∨) ss≤s = ≤←∨ (≤s-ext ind ss≤s)
≤s-ext (∨→ ind) ss≤s = ≤∨→ (≤s-ext ind ss≤s)
≤s-ext (ind ←∂) ss≤s = ≤←∂ (≤s-ext ind ss≤s)
≤s-ext (∂→ ind) ss≤s = ≤∂→ (≤s-ext ind ss≤s)




≤s-trans : ∀{i u ll b c} → {a : SetLL {i} {u} ll} → a ≤s b → b ≤s c → a ≤s c
≤s-trans {c = ↓} ≤id ≤id                        = ≤id
≤s-trans {c = c ←∧} x ≤id                       = x
≤s-trans {c = c ←∧} ≤id (≤←∧ y)                 = ≤←∧ y
≤s-trans {c = c ←∧} (≤←∧ x) (≤←∧ y)             = ≤←∧ (≤s-trans x y)
≤s-trans {c = ∧→ c} x ≤id                       = x
≤s-trans {c = ∧→ c} ≤id (≤∧→ y)                 = ≤∧→ y
≤s-trans {c = ∧→ c} (≤∧→ x) (≤∧→ y)             = ≤∧→ (≤s-trans x y)
≤s-trans {c = c ←∧→ c₁} x ≤id                   = x
≤s-trans {c = c ←∧→ c₁} ≤id (≤←∧→ y y₁)         = ≤←∧→ y y₁
≤s-trans {c = c ←∧→ c₁} (≤←∧→ x x₁) (≤←∧→ y y₁) = ≤←∧→ (≤s-trans x y) (≤s-trans x₁ y₁)
≤s-trans {c = c ←∧→ c₁} (≤d←∧ x) (≤←∧→ y y₁)    = ≤d←∧ (≤s-trans x y)
≤s-trans {c = c ←∧→ c₁} (≤d∧→ x) (≤←∧→ y y₁)    = ≤d∧→ (≤s-trans x y₁)
≤s-trans {c = c ←∧→ c₁} ≤id (≤d←∧ y)            = ≤d←∧ y
≤s-trans {c = c ←∧→ c₁} (≤←∧ x) (≤d←∧ y)        = ≤d←∧ (≤s-trans x y)
≤s-trans {c = c ←∧→ c₁} ≤id (≤d∧→ y)            = ≤d∧→ y
≤s-trans {c = c ←∧→ c₁} (≤∧→ x) (≤d∧→ y)        = ≤d∧→ (≤s-trans x y)
≤s-trans {c = c ←∨} x ≤id                       = x
≤s-trans {c = c ←∨} ≤id (≤←∨ y)                 = ≤←∨ y
≤s-trans {c = c ←∨} (≤←∨ x) (≤←∨ y)             = ≤←∨ (≤s-trans x y)
≤s-trans {c = ∨→ c} x ≤id                       = x
≤s-trans {c = ∨→ c} ≤id (≤∨→ y)                 = ≤∨→ y
≤s-trans {c = ∨→ c} (≤∨→ x) (≤∨→ y)             = ≤∨→ (≤s-trans x y)
≤s-trans {c = c ←∨→ c₁} x ≤id                   = x
≤s-trans {c = c ←∨→ c₁} ≤id (≤←∨→ y y₁)         = ≤←∨→ y y₁
≤s-trans {c = c ←∨→ c₁} (≤←∨→ x x₁) (≤←∨→ y y₁) = ≤←∨→ (≤s-trans x y) (≤s-trans x₁ y₁)
≤s-trans {c = c ←∨→ c₁} (≤d←∨ x) (≤←∨→ y y₁)    = ≤d←∨ (≤s-trans x y)
≤s-trans {c = c ←∨→ c₁} (≤d∨→ x) (≤←∨→ y y₁)    = ≤d∨→ (≤s-trans x y₁)
≤s-trans {c = c ←∨→ c₁} ≤id (≤d←∨ y)            = ≤d←∨ y
≤s-trans {c = c ←∨→ c₁} (≤←∨ x) (≤d←∨ y)        = ≤d←∨ (≤s-trans x y)
≤s-trans {c = c ←∨→ c₁} ≤id (≤d∨→ y)            = ≤d∨→ y
≤s-trans {c = c ←∨→ c₁} (≤∨→ x) (≤d∨→ y)        = ≤d∨→ (≤s-trans x y)
≤s-trans {c = c ←∂} x ≤id                       = x
≤s-trans {c = c ←∂} ≤id (≤←∂ y)                 = ≤←∂ y
≤s-trans {c = c ←∂} (≤←∂ x) (≤←∂ y)             = ≤←∂ (≤s-trans x y)
≤s-trans {c = ∂→ c} x ≤id                       = x
≤s-trans {c = ∂→ c} ≤id (≤∂→ y)                 = ≤∂→ y
≤s-trans {c = ∂→ c} (≤∂→ x) (≤∂→ y)             = ≤∂→ (≤s-trans x y)
≤s-trans {c = c ←∂→ c₁} x ≤id                   = x
≤s-trans {c = c ←∂→ c₁} ≤id (≤←∂→ y y₁)         = ≤←∂→ y y₁
≤s-trans {c = c ←∂→ c₁} (≤←∂→ x x₁) (≤←∂→ y y₁) = ≤←∂→ (≤s-trans x y) (≤s-trans x₁ y₁)
≤s-trans {c = c ←∂→ c₁} (≤d←∂ x) (≤←∂→ y y₁)    = ≤d←∂ (≤s-trans x y)
≤s-trans {c = c ←∂→ c₁} (≤d∂→ x) (≤←∂→ y y₁)    = ≤d∂→ (≤s-trans x y₁)
≤s-trans {c = c ←∂→ c₁} ≤id (≤d←∂ y)            = ≤d←∂ y
≤s-trans {c = c ←∂→ c₁} (≤←∂ x) (≤d←∂ y)        = ≤d←∂ (≤s-trans x y)
≤s-trans {c = c ←∂→ c₁} ≤id (≤d∂→ y)            = ≤d∂→ y
≤s-trans {c = c ←∂→ c₁} (≤∂→ x) (≤d∂→ y)        = ≤d∂→ (≤s-trans x y)




data _∈ₛ_ {i u rll} : ∀{ll} → IndexLL {i} {u} rll ll → SetLL ll → Set where
  inS ↓↓ : ↓ ∈ₛ ↓
  inS←∧←∧ : ∀{li ri ind s} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∧ ri} (ind ←∧) (s ←∧)
  inS←∧←∧→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∧ ri} (ind ←∧) (s ←∧→ s₁)
  inS∧→∧→ : ∀{li ri ind s} → _∈ₛ_ {ll = ri} ind s → _∈ₛ_ {ll = li ∧ ri} (∧→ ind) (∧→ s)
  inS∧→←∧→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = ri} ind s₁ → _∈ₛ_ {ll = li ∧ ri} (∧→ ind) (s ←∧→ s₁)
  inS←∨←∨ : ∀{li ri ind s} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∨ ri} (ind ←∨) (s ←∨)
  inS←∨←∨→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∨ ri} (ind ←∨) (s ←∨→ s₁)
  inS∨→∨→ : ∀{li ri ind s} → _∈ₛ_ {ll = ri} ind s → _∈ₛ_ {ll = li ∨ ri} (∨→ ind) (∨→ s)
  inS∨→←∨→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = ri} ind s₁ → _∈ₛ_ {ll = li ∨ ri} (∨→ ind) (s ←∨→ s₁)
  inS←∂←∂ : ∀{li ri ind s} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∂ ri} (ind ←∂) (s ←∂)
  inS←∂←∂→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = li} ind s → _∈ₛ_ {ll = li ∂ ri} (ind ←∂) (s ←∂→ s₁)
  inS∂→∂→ : ∀{li ri ind s} → _∈ₛ_ {ll = ri} ind s → _∈ₛ_ {ll = li ∂ ri} (∂→ ind) (∂→ s)
  inS∂→←∂→ : ∀{li ri ind s s₁} → _∈ₛ_ {ll = ri} ind s₁ → _∈ₛ_ {ll = li ∂ ri} (∂→ ind) (s ←∂→ s₁)


¬contruct↓⇒¬compl∅ : ∀{i u ll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → ¬ (complLₛ s ≡ ∅)
¬contruct↓⇒¬compl∅ ↓ eq = ⊥-elim (eq refl)
¬contruct↓⇒¬compl∅ (s ←∧) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (s ←∧) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∧) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (∧→ s) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (∧→ s) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (∧→ s) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | yes g with contruct s | contruct s₁ 
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes refl | yes refl | .↓ | .↓ = ⊥-elim (eq refl)
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g with ¬contruct↓⇒¬compl∅ s₁ ¬g
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | w | r | ∅ = ⊥-elim (w refl) 
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | w | ∅ | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | w | ¬∅ x | ¬∅ x₁ = λ ()
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g with ¬contruct↓⇒¬compl∅ s ¬p
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g | w | ∅ | e = ⊥-elim (w refl)
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g | w | ¬∅ x | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g | w | ¬∅ x | ¬∅ x₁ = λ ()
¬contruct↓⇒¬compl∅ (s ←∨) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (s ←∨) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∨) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (∨→ s) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (∨→ s) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (∨→ s) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | yes g with contruct s | contruct s₁ 
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes refl | yes refl | .↓ | .↓ = ⊥-elim (eq refl)
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g with ¬contruct↓⇒¬compl∅ s₁ ¬g
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | w | r | ∅ = ⊥-elim (w refl) 
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | w | ∅ | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | w | ¬∅ x | ¬∅ x₁ = λ ()
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g with ¬contruct↓⇒¬compl∅ s ¬p
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g | w | ∅ | e = ⊥-elim (w refl)
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g | w | ¬∅ x | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g | w | ¬∅ x | ¬∅ x₁ = λ ()
¬contruct↓⇒¬compl∅ (s ←∂) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (s ←∂) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∂) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (∂→ s) eq with (complLₛ s)
¬contruct↓⇒¬compl∅ (∂→ s) eq | ∅ = λ ()
¬contruct↓⇒¬compl∅ (∂→ s) eq | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | yes g with contruct s | contruct s₁ 
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes refl | yes refl | .↓ | .↓ = ⊥-elim (eq refl)
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g with ¬contruct↓⇒¬compl∅ s₁ ¬g
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | w | r | ∅ = ⊥-elim (w refl) 
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | w | ∅ | ¬∅ x = λ ()
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | w | ¬∅ x | ¬∅ x₁ = λ ()
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g with ¬contruct↓⇒¬compl∅ s ¬p
... | w with complLₛ s | complLₛ s₁
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g | w | ∅ | e = ⊥-elim (w refl)
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g | w | ¬∅ x | ∅ = λ ()
¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g | w | ¬∅ x | ¬∅ x₁ = λ ()


module _ where

  open Relation.Binary.PropositionalEquality
  
  contruct↓⇒compl∅ : ∀{i u ll} → (s : SetLL {i} {u} ll) → (contruct s ≡ ↓) → (complLₛ s ≡ ∅)
  contruct↓⇒compl∅ ↓ eq = refl
  contruct↓⇒compl∅ (s ←∧) ()
  contruct↓⇒compl∅ (∧→ s) ()
  contruct↓⇒compl∅ (s ←∧→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g with complLₛ s | inspect complLₛ s | complLₛ s₁ |  inspect complLₛ s₁
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ∅ | [ eq2 ] = refl
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ¬∅ x | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s₁ g)) eq2
  ... | ()
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g | ¬∅ x | [ eq1 ] | r | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s p)) eq1
  ... | ()
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | no ¬g with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | ↓ | ↓ = ⊥-elim (¬g refl)
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∧
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | ∧→ r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∧→ r₁ 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∨ 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | ∨→ r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∨→ r₁ 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∂ 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | ∂→ r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∂→ r₁ 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∧ | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ∧→ e | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∧→ e₁ | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∨ | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ∨→ e | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∨→ e₁ | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∂ | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ∂→ e | r 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∂→ e₁ | r 

  contruct↓⇒compl∅ (s ←∧→ s₁) eq | no ¬p | r with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∧→ s₁) eq | no ¬p | r | ↓ | w = ⊥-elim (¬p refl)
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∧ | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | ∧→ e | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∧→ e₁ | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∨ | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | ∨→ e | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∨→ e₁ | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∂ | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | ∂→ e | w 
  contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∂→ e₁ | w 


  contruct↓⇒compl∅ (s ←∨) ()
  contruct↓⇒compl∅ (∨→ s) ()
  contruct↓⇒compl∅ (s ←∨→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g with complLₛ s | inspect complLₛ s | complLₛ s₁ |  inspect complLₛ s₁
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ∅ | [ eq2 ] = refl
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ¬∅ x | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s₁ g)) eq2
  ... | ()
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g | ¬∅ x | [ eq1 ] | r | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s p)) eq1
  ... | ()
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | no ¬g with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | ↓ | ↓ = ⊥-elim (¬g refl)
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∧
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | ∧→ r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∧→ r₁ 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∨ 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | ∨→ r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∨→ r₁ 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∂ 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | ∂→ r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∂→ r₁ 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∧ | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ∧→ e | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∧→ e₁ | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∨ | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ∨→ e | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∨→ e₁ | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∂ | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ∂→ e | r 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∂→ e₁ | r 

  contruct↓⇒compl∅ (s ←∨→ s₁) eq | no ¬p | r with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∨→ s₁) eq | no ¬p | r | ↓ | w = ⊥-elim (¬p refl)
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∧ | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | ∧→ e | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∧→ e₁ | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∨ | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | ∨→ e | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∨→ e₁ | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∂ | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | ∂→ e | w 
  contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∂→ e₁ | w 




  contruct↓⇒compl∅ (s ←∂) ()
  contruct↓⇒compl∅ (∂→ s) ()
  contruct↓⇒compl∅ (s ←∂→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g with complLₛ s | inspect complLₛ s | complLₛ s₁ |  inspect complLₛ s₁
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ∅ | [ eq2 ] = refl
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ¬∅ x | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s₁ g)) eq2
  ... | ()
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g | ¬∅ x | [ eq1 ] | r | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s p)) eq1
  ... | ()
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | no ¬g with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | ↓ | ↓ = ⊥-elim (¬g refl)
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∧
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | ∧→ r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∧→ r₁ 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∨ 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | ∨→ r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∨→ r₁ 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∂ 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | ∂→ r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∂→ r₁ 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∧ | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ∧→ e | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∧→ e₁ | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∨ | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ∨→ e | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∨→ e₁ | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∂ | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ∂→ e | r 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∂→ e₁ | r 

  contruct↓⇒compl∅ (s ←∂→ s₁) eq | no ¬p | r with contruct s | contruct s₁
  contruct↓⇒compl∅ (s ←∂→ s₁) eq | no ¬p | r | ↓ | w = ⊥-elim (¬p refl)
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∧ | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | ∧→ e | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∧→ e₁ | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∨ | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | ∨→ e | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∨→ e₁ | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∂ | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | ∂→ e | w 
  contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∂→ e₁ | w 
