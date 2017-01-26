{-# OPTIONS --exact-split #-}


module SetLL where

open import Common
open import LinLogic
import Data.List



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
∅-add : ∀{i u ll rll} → {j : Size< ↑ i} → (ind : IndexLL {i} {u} rll ll) → (nrll : LinLogic j )
        → SetLL (replLL ll ind nrll)
∅-add ↓ nrll = ↓
∅-add (ind ←∧) nrll = (∅-add ind nrll) ←∧
∅-add (∧→ ind) nrll = ∧→ (∅-add ind nrll)
∅-add (ind ←∨) nrll = (∅-add ind nrll) ←∨
∅-add (∨→ ind) nrll = ∨→ (∅-add ind nrll)
∅-add (ind ←∂) nrll = (∅-add ind nrll) ←∂
∅-add (∂→ ind) nrll = ∂→ (∅-add ind nrll)


-- TODO We shouldn't need this. When issue agda #2409 is resolved, remove this.
dsize : ∀{i u ll} → {j : Size< ↑ i} → SetLL {i} {u} ll → SetLL {j} ll
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
add : ∀{i u ll q} → {j : Size< ↑ i} → SetLL ll → (ind : IndexLL {i} {u} q ll) → (rll : LinLogic j)
      → SetLL (replLL ll ind rll)
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


-- If two adjacent nodes exist in the set, the higher node is in the set.
-- We contruct the set.
contruct : ∀{i u ll} → SetLL {i} {u} ll → SetLL ll
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



-- If we transform the linear logic tree, we need to transform the SetLL as well.
tran : ∀ {i u ll rll} → SetLL ll → (tr : LLTr {i} {u} rll ll)
       → SetLL rll
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


module _ where

  open Data.List

  -- In this transformation, we duplicate the set when we use distributive transformations, thus we
  -- have two sets that contains the same number of inputs as before. One of them can be executed
  -- when they join together into one root and a com exists in the Linear Function.
  sptran : ∀{i u ll rll} → SetLL ll → (tr : LLTr {i} {u} rll ll)
         → List (SetLL rll)
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


