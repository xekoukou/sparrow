{-# OPTIONS --exact-split #-}

module LinLogic where

open import Common
open import Data.Unit

module _ where

  open import Data.Vec 
  
  mutual
    -- Linear Logic Connectives : Used to describe the input
    -- and output of an agent.
    data LinLogic (i : Size) {u} : Set (lsuc u) where
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
  
    record ∞LinLogic (i : Size) {u} : Set (lsuc u) where
      coinductive
      field
        step : {j : Size< i} → LinLogic j {u = u}
  
  open ∞LinLogic public


-- TODO. Do we need more linear transformations?

-- Transformations of the Linear Logic so as to construct
-- the correct sub-tree that is to be the input of a linear function.
data LLTr {i : Size} {u} (rll : LinLogic i {u}) : LinLogic i {u} → Set (lsuc u) where
  -- Identity
  I     : LLTr rll rll
  -- Commutative transformations for ∂, ∧ and ∨.
  ∂c    : ∀{r l} → LLTr rll (r ∂ l) → LLTr rll (l ∂ r)
  ∧c    : ∀{r l} → LLTr rll (r ∧ l) → LLTr rll (l ∧ r)
  ∨c    : ∀{r l} → LLTr rll (r ∨ l) → LLTr rll (l ∨ r)
  -- Distributive transformations.
-- The agent to whom to send r depends on the knowledge of ∂'s answer, this this is impossible.  
--  ∧∂d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∧ r) ∂ (l₂ ∧ r)) → LLTr rll ((l₁ ∂ l₂) ∧ r)                   
  -- Not possible because there are two instances of LinDepT r and we do not know which to choose.
--  ¬∧∂d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∂ l₂) ∧ r) → LLTr rll ((l₁ ∧ r) ∂ (l₂ ∧ r))                
-- The agent to whom to send r depends on the knowledge of ∨'s answer, this this is impossible.  
--  ∧∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∧ r) ∨ (l₂ ∧ r)) → LLTr rll ((l₁ ∨ l₂) ∧ r)                   
  -- Not possible because there are two instances of LinDepT r and we do not know which to choose.
--  ¬∧∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∨ l₂) ∧ r) → LLTr rll ((l₁ ∧ r) ∨ (l₂ ∧ r))
-- Not possible to duplicate resources.  
--  ∧∧d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∧ r) ∧ (l₂ ∧ r)) → LLTr rll ((l₁ ∧ l₂) ∧ r)
-- Not possible to choose which path to take if r arrives, since ∂ might not be triggered at all.
-- The two are not the same.
--   ∨∂d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∨ r) ∂ (l₂ ∨ r)) → LLTr rll ((l₁ ∂ l₂) ∨ r)
  -- Not possible because there are two instances of LinDepT r and we do not know which to choose.
--  ¬∨∂d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∂ l₂) ∨ r) → LLTr rll ((l₁ ∨ r) ∂ (l₂ ∨ r))
-- Not possible to duplicate resources.  
--  ∨∧d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∨ r) ∧ (l₂ ∨ r)) → LLTr rll ((l₁ ∧ l₂) ∨ r)
-- Not possible to choose which path to take if r arrives, since ∂ might not be triggered at all.
-- The two are not the same.
--  ∂∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∂ r) ∨ (l₂ ∂ r)) → LLTr rll ((l₁ ∨ l₂) ∂ r)                                   
  -- Not possible because there are two instances of LinDepT r and we do not know which to choose.
--  ¬∂∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∨ l₂) ∂ r) → LLTr rll ((l₁ ∂ r) ∨ (l₂ ∂ r))
-- Not possible to duplicate resources.  
--  ∂∧d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∂ r) ∧ (l₂ ∂ r)) → LLTr rll ((l₁ ∧ l₂) ∂ r)
-- Associative transformations
  ∧∧d   : ∀{l₁ l₂ r} → LLTr rll (l₁ ∧ (l₂ ∧ r)) → LLTr rll ((l₁ ∧ l₂) ∧ r)
  ¬∧∧d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∧ l₂) ∧ r) → LLTr rll (l₁ ∧ (l₂ ∧ r))
  ∨∨d   : ∀{l₁ l₂ r} → LLTr rll (l₁ ∨ (l₂ ∨ r)) → LLTr rll ((l₁ ∨ l₂) ∨ r)
  ¬∨∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∨ l₂) ∨ r) → LLTr rll (l₁ ∨ (l₂ ∨ r))
  ∂∂d   : ∀{l₁ l₂ r} → LLTr rll (l₁ ∂ (l₂ ∂ r)) → LLTr rll ((l₁ ∂ l₂) ∂ r)
  ¬∂∂d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∂ l₂) ∂ r) → LLTr rll (l₁ ∂ (l₂ ∂ r))


revTr : ∀{i u rll ll} → LLTr {i} {u} rll ll → LLTr ll rll
revTr {i} {u} {orll} {oll} ltr = revTr` ltr I where
  revTr` : ∀{x} → LLTr {i} {u} orll x → LLTr oll x → LLTr oll orll
  revTr` I nltr = nltr
  revTr` (∂c ltr) nltr = revTr` ltr (∂c nltr)
  revTr` (∧c ltr) nltr = revTr` ltr (∧c nltr)
  revTr` (∨c ltr) nltr = revTr` ltr (∨c nltr)
  revTr` (∧∧d ltr) nltr = revTr` ltr (¬∧∧d nltr)
  revTr` (¬∧∧d ltr) nltr = revTr` ltr (∧∧d nltr)
  revTr` (∨∨d ltr) nltr = revTr` ltr (¬∨∨d nltr)
  revTr` (¬∨∨d ltr) nltr = revTr` ltr (∨∨d nltr)
  revTr` (∂∂d ltr) nltr =  revTr` ltr (¬∂∂d nltr)
  revTr` (¬∂∂d ltr) nltr =  revTr` ltr (∂∂d nltr)


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
replLL : ∀{i u q} → (ll : LinLogic i {u}) → IndexLL q ll → LinLogic i {u} → LinLogic i {u}
replLL ll ↓ c            = c
replLL (l ∧ r) (li ←∧) c = (replLL l li c) ∧ r
replLL (l ∧ r) (∧→ ri) c = l ∧ (replLL r ri c)
replLL (l ∨ r) (li ←∨) c = (replLL l li c) ∨ r
replLL (l ∨ r) (∨→ ri) c = l ∨ (replLL r ri c)
replLL (l ∂ r) (li ←∂) c = (replLL l li c) ∂ r
replLL (l ∂ r) (∂→ ri) c = l ∂ (replLL r ri c)
