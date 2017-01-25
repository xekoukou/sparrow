{-# OPTIONS --exact-split #-}

module SetLL where

open import Common
open import LinLogic


-- A non-empty set of nodes in a Linear Logic tree.
data SetLL {u} : LinLogic ∞ {u} → Set where
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
data MSetLL {u} : LinLogic ∞ {u} → Set where
  ∅   : ∀{ll}            → MSetLL ll
  ¬∅  : ∀{ll} → SetLL ll → MSetLL ll







module SetLLMp where

  open import Data.List

-- Add a node to an empty set (and potentially replace the linear logic sub-tree).
  ∅-add : ∀{u ll q} → (ind : IndexLL {u} q ll) → (rll : LinLogic ∞ {u})
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
  contruct : ∀{u ll} → SetLL {u} ll → SetLL {u} ll
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
  dsize : ∀{u ll} → SetLL {u} ll → SetLL {u} ll
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
  add : ∀{u ll q} → SetLL {u} ll → (ind : IndexLL {u} q ll) → (rll : LinLogic ∞ {u})
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


  isEq : ∀{u} → {ll : LinLogic ∞ {u}} → (a : SetLL ll) → (b : SetLL ll) → Dec (a ≡ b)
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


-- If we transform the linear logic tree, we need to transform the SetLL as well.
  tran : ∀ {u ll rll} → SetLL {u} ll → (tr : LLTr {u} rll ll)
         → SetLL {u} rll
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

  itran : ∀ {u ll rll pll} → SetLL {u} ll → (ind : IndexLL {u} pll ll) → (tr : LLTr {u} rll pll)
          → SetLL {u} (replLL ll ind rll)
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
  sptran : ∀ {u ll rll} → SetLL {u} ll → (tr : LLTr {u} rll ll)
         → List (SetLL {u} rll)
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



module _ where

  open SetLLMp

  data exactHit {u} : ∀{ll rll} → (s : SetLL {u} ll) → (ind : IndexLL {u} rll ll) → Set where
    exactHitCs↓ : ∀{ll s} → exactHit {ll = ll} {rll = ll} s ↓
    exactHitC←∧←∧ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = ll ∧ q} {rll = rll} (s ←∧) (ind ←∧)
    exactHitC∧→∧→ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = q ∧ ll} {rll = rll} (∧→ s) (∧→ ind)
    exactHitC←∨←∨ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = ll ∨ q} {rll = rll} (s ←∨) (ind ←∨)
    exactHitC∨→∨→ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = q ∨ ll} {rll = rll} (∨→ s) (∨→ ind)
    exactHitC←∂←∂ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = ll ∂ q} {rll = rll} (s ←∂) (ind ←∂)
    exactHitC∂→∂→ : ∀{ll q rll s ind} → exactHit {ll = ll} {rll = rll} s ind → exactHit {ll = q ∂ ll} {rll = rll} (∂→ s) (∂→ ind)

  exactHitUnique : ∀{u ll rll} → (s : SetLL {u} ll) → (ind : IndexLL {u} rll ll) 
                   → (a : exactHit {u} {ll} {rll} s ind) → (b : exactHit {u} {ll} {rll} s ind)
                   → a ≡ b
  exactHitUnique ↓ ↓ exactHitCs↓ exactHitCs↓ = refl
  exactHitUnique ↓ (ind ←∧) () b
  exactHitUnique ↓ (∧→ ind) () b
  exactHitUnique ↓ (ind ←∨) () b
  exactHitUnique ↓ (∨→ ind) () b
  exactHitUnique ↓ (ind ←∂) () b
  exactHitUnique ↓ (∂→ ind) () b
  exactHitUnique (s ←∧) ↓ exactHitCs↓ exactHitCs↓ = refl
  exactHitUnique (s ←∧) (ind ←∧) (exactHitC←∧←∧ a) (exactHitC←∧←∧ b) with (exactHitUnique s ind a b)
  exactHitUnique (s ←∧) (ind ←∧) (exactHitC←∧←∧ a) (exactHitC←∧←∧ .a) | refl = refl
  exactHitUnique (s ←∧) (∧→ ind) () b
  exactHitUnique (∧→ s) ↓ exactHitCs↓ exactHitCs↓ = refl
  exactHitUnique (∧→ s) (ind ←∧) () b
  exactHitUnique (∧→ s) (∧→ ind) (exactHitC∧→∧→ a) (exactHitC∧→∧→ b) with (exactHitUnique s ind a b)
  exactHitUnique (∧→ s) (∧→ ind) (exactHitC∧→∧→ a) (exactHitC∧→∧→ .a) | refl = refl
  exactHitUnique (s ←∧→ s₁) ↓ exactHitCs↓ exactHitCs↓ = refl
  exactHitUnique (s ←∧→ s₁) (ind ←∧) () b
  exactHitUnique (s ←∧→ s₁) (∧→ ind) () b
  exactHitUnique (s ←∨) ↓ exactHitCs↓ exactHitCs↓ = refl
  exactHitUnique (s ←∨) (ind ←∨) (exactHitC←∨←∨ a) (exactHitC←∨←∨ b) with (exactHitUnique s ind a b)
  exactHitUnique (s ←∨) (ind ←∨) (exactHitC←∨←∨ a) (exactHitC←∨←∨ .a) | refl = refl
  exactHitUnique (s ←∨) (∨→ ind) () b
  exactHitUnique (∨→ s) ↓ exactHitCs↓ exactHitCs↓ = refl
  exactHitUnique (∨→ s) (ind ←∨) () b
  exactHitUnique (∨→ s) (∨→ ind) (exactHitC∨→∨→ a) (exactHitC∨→∨→ b) with (exactHitUnique s ind a b)
  exactHitUnique (∨→ s) (∨→ ind) (exactHitC∨→∨→ a) (exactHitC∨→∨→ .a) | refl = refl
  exactHitUnique (s ←∨→ s₁) ↓ exactHitCs↓ exactHitCs↓ = refl
  exactHitUnique (s ←∨→ s₁) (ind ←∨) () b
  exactHitUnique (s ←∨→ s₁) (∨→ ind) () b
  exactHitUnique (s ←∂) ↓ exactHitCs↓ exactHitCs↓ = refl
  exactHitUnique (s ←∂) (ind ←∂) (exactHitC←∂←∂ a) (exactHitC←∂←∂ b) with (exactHitUnique s ind a b)
  exactHitUnique (s ←∂) (ind ←∂) (exactHitC←∂←∂ a) (exactHitC←∂←∂ .a) | refl = refl
  exactHitUnique (s ←∂) (∂→ ind) () b
  exactHitUnique (∂→ s) ↓ exactHitCs↓ exactHitCs↓ = refl
  exactHitUnique (∂→ s) (ind ←∂) () b
  exactHitUnique (∂→ s) (∂→ ind) (exactHitC∂→∂→ a) (exactHitC∂→∂→ b) with (exactHitUnique s ind a b)
  exactHitUnique (∂→ s) (∂→ ind) (exactHitC∂→∂→ a) (exactHitC∂→∂→ .a) | refl = refl
  exactHitUnique (s ←∂→ s₁) ↓ exactHitCs↓ exactHitCs↓ = refl
  exactHitUnique (s ←∂→ s₁) (ind ←∂) () b
  exactHitUnique (s ←∂→ s₁) (∂→ ind) () b


  isExactHit : ∀{u ll rll} → (s : SetLL {u} ll) → (ind : IndexLL {u} rll ll) → Dec (exactHit{ll = ll} {rll = rll} s ind)
  isExactHit ↓ ↓ = yes exactHitCs↓
  isExactHit ↓ (ind ←∧) = no (λ ())
  isExactHit ↓ (∧→ ind) = no (λ ())
  isExactHit ↓ (ind ←∨) = no (λ ())
  isExactHit ↓ (∨→ ind) = no (λ ())
  isExactHit ↓ (ind ←∂) = no (λ ())
  isExactHit ↓ (∂→ ind) = no (λ ())
  isExactHit (s ←∧) ↓ = yes exactHitCs↓
  isExactHit (s ←∧) (ind ←∧) with (isExactHit s ind)
  isExactHit (s ←∧) (ind ←∧) | yes p = yes (exactHitC←∧←∧ p)
  isExactHit (s ←∧) (ind ←∧) | no ¬p = no (λ {(exactHitC←∧←∧ x) → ¬p x})
  isExactHit (s ←∧) (∧→ ind) = no (λ ())
  isExactHit (∧→ s) ↓ = yes exactHitCs↓
  isExactHit (∧→ s) (ind ←∧) = no (λ ())
  isExactHit (∧→ s) (∧→ ind) with (isExactHit s ind)
  isExactHit (∧→ s) (∧→ ind) | yes p = yes (exactHitC∧→∧→ p)
  isExactHit (∧→ s) (∧→ ind) | no ¬p = no (λ { (exactHitC∧→∧→ x) → ¬p x})
  isExactHit (s ←∧→ s₁) ↓ = yes exactHitCs↓
  isExactHit (s ←∧→ s₁) (ind ←∧) = no (λ ())
  isExactHit (s ←∧→ s₁) (∧→ ind) = no (λ ())
  isExactHit (s ←∨) ↓ = yes exactHitCs↓
  isExactHit (s ←∨) (ind ←∨) with (isExactHit s ind)
  isExactHit (s ←∨) (ind ←∨) | yes p = yes (exactHitC←∨←∨ p)
  isExactHit (s ←∨) (ind ←∨) | no ¬p = no ( λ { (exactHitC←∨←∨ x) → ¬p x})
  isExactHit (s ←∨) (∨→ ind) = no (λ ())
  isExactHit (∨→ s) ↓ = yes exactHitCs↓
  isExactHit (∨→ s) (ind ←∨) = no (λ ())
  isExactHit (∨→ s) (∨→ ind) with (isExactHit s ind)
  isExactHit (∨→ s) (∨→ ind) | yes p = yes (exactHitC∨→∨→ p)
  isExactHit (∨→ s) (∨→ ind) | no ¬p = no ( λ { (exactHitC∨→∨→ x) → ¬p x})
  isExactHit (s ←∨→ s₁) ↓ = yes exactHitCs↓
  isExactHit (s ←∨→ s₁) (ind ←∨) = no (λ ())
  isExactHit (s ←∨→ s₁) (∨→ ind) = no (λ ())
  isExactHit (s ←∂) ↓ = yes exactHitCs↓
  isExactHit (s ←∂) (ind ←∂) with (isExactHit s ind)
  isExactHit (s ←∂) (ind ←∂) | yes p = yes (exactHitC←∂←∂ p)
  isExactHit (s ←∂) (ind ←∂) | no ¬p = no ( λ { (exactHitC←∂←∂ x) → ¬p x})
  isExactHit (s ←∂) (∂→ ind) = no (λ ())
  isExactHit (∂→ s) ↓ = yes exactHitCs↓
  isExactHit (∂→ s) (ind ←∂) = no (λ ())
  isExactHit (∂→ s) (∂→ ind) with (isExactHit s ind)
  isExactHit (∂→ s) (∂→ ind) | yes p = yes (exactHitC∂→∂→ p)
  isExactHit (∂→ s) (∂→ ind) | no ¬p = no (λ { (exactHitC∂→∂→ x) → ¬p x})
  isExactHit (s ←∂→ s₁) ↓ = yes exactHitCs↓
  isExactHit (s ←∂→ s₁) (ind ←∂) = no (λ ())
  isExactHit (s ←∂→ s₁) (∂→ ind) = no (λ ())


-- It hits at least once.

  data hitsOnce {u} : ∀{ll rll} → SetLL {u} ll → (ind : IndexLL {u} rll ll) → Set where
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

  hitsOnceUnique : ∀{u ll rll} → (s : SetLL {u} ll) → (ind : IndexLL {u} rll ll) → (a : hitsOnce s ind) → (b : hitsOnce s ind) → a ≡ b
  hitsOnceUnique ↓ ind hitsOnce↓ hitsOnce↓ = refl
  hitsOnceUnique (s ←∧) ↓ hitsOnce←∧↓ hitsOnce←∧↓ = refl
  hitsOnceUnique (s ←∧) (ind ←∧) (hitsOnce←∧←∧ a) (hitsOnce←∧←∧ b) with (hitsOnceUnique s ind a b)
  hitsOnceUnique (s ←∧) (ind ←∧) (hitsOnce←∧←∧ a) (hitsOnce←∧←∧ .a) | refl = refl
  hitsOnceUnique (s ←∧) (∧→ ind) () b
  hitsOnceUnique (∧→ s) ↓ hitsOnce∧→↓ hitsOnce∧→↓ = refl
  hitsOnceUnique (∧→ s) (ind ←∧) () b
  hitsOnceUnique (∧→ s) (∧→ ind) (hitsOnce∧→∧→ a) (hitsOnce∧→∧→ b) with (hitsOnceUnique s ind a b)
  hitsOnceUnique (∧→ s) (∧→ ind) (hitsOnce∧→∧→ a) (hitsOnce∧→∧→ .a) | refl = refl
  hitsOnceUnique (s ←∧→ s₁) ↓ hitsOnce←∧→↓ hitsOnce←∧→↓ = refl
  hitsOnceUnique (s ←∧→ s₁) (ind ←∧) (hitsOnce←∧→←∧ a) (hitsOnce←∧→←∧ b) with (hitsOnceUnique s ind a b)
  hitsOnceUnique (s ←∧→ s₁) (ind ←∧) (hitsOnce←∧→←∧ a) (hitsOnce←∧→←∧ .a) | refl = refl
  hitsOnceUnique (s ←∧→ s₁) (∧→ ind) (hitsOnce←∧→∧→ a) (hitsOnce←∧→∧→ b) with (hitsOnceUnique s₁ ind a b)
  hitsOnceUnique (s ←∧→ s₁) (∧→ ind) (hitsOnce←∧→∧→ a) (hitsOnce←∧→∧→ .a) | refl = refl
  hitsOnceUnique (s ←∨) ↓ hitsOnce←∨↓ hitsOnce←∨↓ = refl
  hitsOnceUnique (s ←∨) (ind ←∨) (hitsOnce←∨←∨ a) (hitsOnce←∨←∨ b) with (hitsOnceUnique s ind a b)
  hitsOnceUnique (s ←∨) (ind ←∨) (hitsOnce←∨←∨ a) (hitsOnce←∨←∨ .a) | refl = refl
  hitsOnceUnique (s ←∨) (∨→ ind) () b
  hitsOnceUnique (∨→ s) ↓ hitsOnce∨→↓ hitsOnce∨→↓ = refl
  hitsOnceUnique (∨→ s) (ind ←∨) () b
  hitsOnceUnique (∨→ s) (∨→ ind) (hitsOnce∨→∨→ a) (hitsOnce∨→∨→ b) with (hitsOnceUnique s ind a b)
  hitsOnceUnique (∨→ s) (∨→ ind) (hitsOnce∨→∨→ a) (hitsOnce∨→∨→ .a) | refl = refl
  hitsOnceUnique (s ←∨→ s₁) ↓ hitsOnce←∨→↓ hitsOnce←∨→↓ = refl
  hitsOnceUnique (s ←∨→ s₁) (ind ←∨) (hitsOnce←∨→←∨ a) (hitsOnce←∨→←∨ b) with (hitsOnceUnique s ind a b)
  hitsOnceUnique (s ←∨→ s₁) (ind ←∨) (hitsOnce←∨→←∨ a) (hitsOnce←∨→←∨ .a) | refl = refl
  hitsOnceUnique (s ←∨→ s₁) (∨→ ind) (hitsOnce←∨→∨→ a) (hitsOnce←∨→∨→ b) with (hitsOnceUnique s₁ ind a b)
  hitsOnceUnique (s ←∨→ s₁) (∨→ ind) (hitsOnce←∨→∨→ a) (hitsOnce←∨→∨→ .a) | refl = refl
  hitsOnceUnique (s ←∂) ↓ hitsOnce←∂↓ hitsOnce←∂↓ = refl
  hitsOnceUnique (s ←∂) (ind ←∂) (hitsOnce←∂←∂ a) (hitsOnce←∂←∂ b) with (hitsOnceUnique s ind a b)
  hitsOnceUnique (s ←∂) (ind ←∂) (hitsOnce←∂←∂ a) (hitsOnce←∂←∂ .a) | refl = refl
  hitsOnceUnique (s ←∂) (∂→ ind) () b
  hitsOnceUnique (∂→ s) ↓ hitsOnce∂→↓ hitsOnce∂→↓ = refl
  hitsOnceUnique (∂→ s) (ind ←∂) () b
  hitsOnceUnique (∂→ s) (∂→ ind) (hitsOnce∂→∂→ a) (hitsOnce∂→∂→ b) with (hitsOnceUnique s ind a b)
  hitsOnceUnique (∂→ s) (∂→ ind) (hitsOnce∂→∂→ a) (hitsOnce∂→∂→ .a) | refl = refl
  hitsOnceUnique (s ←∂→ s₁) ↓ hitsOnce←∂→↓ hitsOnce←∂→↓ = refl
  hitsOnceUnique (s ←∂→ s₁) (ind ←∂) (hitsOnce←∂→←∂ a) (hitsOnce←∂→←∂ b) with (hitsOnceUnique s ind a b)
  hitsOnceUnique (s ←∂→ s₁) (ind ←∂) (hitsOnce←∂→←∂ a) (hitsOnce←∂→←∂ .a) | refl = refl
  hitsOnceUnique (s ←∂→ s₁) (∂→ ind) (hitsOnce←∂→∂→ a) (hitsOnce←∂→∂→ b) with (hitsOnceUnique s₁ ind a b)
  hitsOnceUnique (s ←∂→ s₁) (∂→ ind) (hitsOnce←∂→∂→ a) (hitsOnce←∂→∂→ .a) | refl = refl


  exactHit¬hitsOnce→⊥ : ∀{u ll rll} → (s : SetLL {u} ll) → (ind : IndexLL {u} rll ll) → exactHit s ind → ¬ (hitsOnce s ind) → ⊥
  exactHit¬hitsOnce→⊥ ↓ ↓ ex ¬ho = ¬ho hitsOnce↓
  exactHit¬hitsOnce→⊥ ↓ (ind ←∧) () ¬ho
  exactHit¬hitsOnce→⊥ ↓ (∧→ ind) () ¬ho
  exactHit¬hitsOnce→⊥ ↓ (ind ←∨) () ¬ho
  exactHit¬hitsOnce→⊥ ↓ (∨→ ind) () ¬ho
  exactHit¬hitsOnce→⊥ ↓ (ind ←∂) () ¬ho
  exactHit¬hitsOnce→⊥ ↓ (∂→ ind) () ¬ho
  exactHit¬hitsOnce→⊥ (s ←∧) ↓ ex ¬ho = ¬ho hitsOnce←∧↓
  exactHit¬hitsOnce→⊥ (s ←∧) (ind ←∧) (exactHitC←∧←∧ ex) ¬ho with (exactHit¬hitsOnce→⊥ s ind ex (λ x → ¬ho (hitsOnce←∧←∧ x)))
  exactHit¬hitsOnce→⊥ (s ←∧) (ind ←∧) (exactHitC←∧←∧ ex) ¬ho | ()
  exactHit¬hitsOnce→⊥ (s ←∧) (∧→ ind) () ¬ho
  exactHit¬hitsOnce→⊥ (∧→ s) ↓ ex ¬ho = ¬ho hitsOnce∧→↓
  exactHit¬hitsOnce→⊥ (∧→ s) (ind ←∧) () ¬ho
  exactHit¬hitsOnce→⊥ (∧→ s) (∧→ ind) (exactHitC∧→∧→ ex) ¬ho with (exactHit¬hitsOnce→⊥ s ind ex (λ x → ¬ho (hitsOnce∧→∧→ x)))
  exactHit¬hitsOnce→⊥ (∧→ s) (∧→ ind) (exactHitC∧→∧→ ex) ¬ho | ()
  exactHit¬hitsOnce→⊥ (s ←∧→ s₁) ↓ ex ¬ho = ¬ho hitsOnce←∧→↓
  exactHit¬hitsOnce→⊥ (s ←∧→ s₁) (ind ←∧) () ¬ho
  exactHit¬hitsOnce→⊥ (s ←∧→ s₁) (∧→ ind) () ¬ho
  exactHit¬hitsOnce→⊥ (s ←∨) ↓ ex ¬ho = ¬ho hitsOnce←∨↓
  exactHit¬hitsOnce→⊥ (s ←∨) (ind ←∨) (exactHitC←∨←∨ ex) ¬ho with (exactHit¬hitsOnce→⊥ s ind ex (λ x → ¬ho (hitsOnce←∨←∨ x)))
  exactHit¬hitsOnce→⊥ (s ←∨) (ind ←∨) (exactHitC←∨←∨ ex) ¬ho | ()
  exactHit¬hitsOnce→⊥ (s ←∨) (∨→ ind) () ¬ho
  exactHit¬hitsOnce→⊥ (∨→ s) ↓ ex ¬ho = ¬ho hitsOnce∨→↓
  exactHit¬hitsOnce→⊥ (∨→ s) (ind ←∨) () ¬ho
  exactHit¬hitsOnce→⊥ (∨→ s) (∨→ ind) (exactHitC∨→∨→ ex) ¬ho with (exactHit¬hitsOnce→⊥ s ind ex (λ x → ¬ho (hitsOnce∨→∨→ x)))
  exactHit¬hitsOnce→⊥ (∨→ s) (∨→ ind) (exactHitC∨→∨→ ex) ¬ho | ()
  exactHit¬hitsOnce→⊥ (s ←∨→ s₁) ↓ ex ¬ho = ¬ho hitsOnce←∨→↓
  exactHit¬hitsOnce→⊥ (s ←∨→ s₁) (ind ←∨) () ¬ho
  exactHit¬hitsOnce→⊥ (s ←∨→ s₁) (∨→ ind) () ¬ho
  exactHit¬hitsOnce→⊥ (s ←∂) ↓ ex ¬ho = ¬ho hitsOnce←∂↓
  exactHit¬hitsOnce→⊥ (s ←∂) (ind ←∂) (exactHitC←∂←∂ ex) ¬ho with (exactHit¬hitsOnce→⊥ s ind ex (λ x → ¬ho (hitsOnce←∂←∂ x)))
  exactHit¬hitsOnce→⊥ (s ←∂) (ind ←∂) (exactHitC←∂←∂ ex) ¬ho | ()
  exactHit¬hitsOnce→⊥ (s ←∂) (∂→ ind) () ¬ho
  exactHit¬hitsOnce→⊥ (∂→ s) ↓ ex ¬ho = ¬ho hitsOnce∂→↓
  exactHit¬hitsOnce→⊥ (∂→ s) (ind ←∂) () ¬ho
  exactHit¬hitsOnce→⊥ (∂→ s) (∂→ ind) (exactHitC∂→∂→ ex) ¬ho with (exactHit¬hitsOnce→⊥ s ind ex (λ x → ¬ho (hitsOnce∂→∂→ x)))
  exactHit¬hitsOnce→⊥ (∂→ s) (∂→ ind) (exactHitC∂→∂→ ex) ¬ho | ()
  exactHit¬hitsOnce→⊥ (s ←∂→ s₁) ↓ ex ¬ho = ¬ho hitsOnce←∂→↓
  exactHit¬hitsOnce→⊥ (s ←∂→ s₁) (ind ←∂) () ¬ho
  exactHit¬hitsOnce→⊥ (s ←∂→ s₁) (∂→ ind) () ¬ho




  doesItHitOnce : ∀{u ll q} → (s : SetLL {u} ll) → (ind : IndexLL {u} q ll) → Dec (hitsOnce s ind)
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


module _ where

  open SetLLMp

-- Replace the linear logic sub-tree.
  replSetLL : ∀{u ll q} → (s : SetLL {u} ll) → (ind : IndexLL {u} q ll)
              → .{{ prf : ¬ (hitsOnce s ind) }} → (rll : LinLogic ∞ {u})
              → (SetLL (replLL ll ind rll))
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

  truncSetLL : ∀ {u ll pll} → SetLL {u} ll → (ind : IndexLL {u} pll ll)
               → MSetLL {u} pll
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

-- TODO This does not necessarily need exactHit, only hitsOnce.

  truncExSetLL : ∀ {u ll pll} → (s : SetLL {u} ll) → (ind : IndexLL {u} pll ll)
               → ⦃ prf : exactHit s ind ⦄ → SetLL {u} pll
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



module _ where

  open import Data.Bool
  
  private
    noNilFinite : ∀{u} → (ll : LinLogic ∞ {u}) → Bool
    noNilFinite ∅ = false
    noNilFinite (τ x₁) = true
    noNilFinite (y LinLogic.∧ y₁) = noNilFinite y Data.Bool.∧ noNilFinite y₁
    noNilFinite (y LinLogic.∨ y₁) = noNilFinite y Data.Bool.∧ noNilFinite y₁
    noNilFinite (y ∂ y₁) = noNilFinite y Data.Bool.∧ noNilFinite y₁
    noNilFinite (call x₁) = false

  -- TODO Do we have to do that?
  onlyOneNilOrNoNilFinite : ∀{u} → (ll : LinLogic ∞ {u}) → Bool
  onlyOneNilOrNoNilFinite ∅ = true
  onlyOneNilOrNoNilFinite (τ x) = noNilFinite (τ x)
  onlyOneNilOrNoNilFinite (x LinLogic.∧ x₁) = noNilFinite (x LinLogic.∧ x₁)
  onlyOneNilOrNoNilFinite (x LinLogic.∨ x₁) = noNilFinite (x LinLogic.∨ x₁)
  onlyOneNilOrNoNilFinite (x ∂ x₁) = noNilFinite (x ∂ x₁)
  onlyOneNilOrNoNilFinite (call x) = noNilFinite (call x)
