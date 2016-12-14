module LinDepT where

open import LinLogic public
open import Size
open import Data.Vec using (Vec)
open import Data.Sum
open import Function
open import Data.Maybe
open import Category.Monad

open import Level

mutual
-- This type is computed by the protocol specification and all input/output
-- types depend on it.
  data LinDepT {i : Size} {u} : LinLogic i {u} → Set (suc u) where
  -- Do not send anything.
    ∅    :                                  LinDepT ∅
    τ    : ∀{n} → {dt : Vec (Set u) n} → {df : genT dt} → (hv : HVec dt) → LinDepT (τ {dt = dt} df)
    _∧_  : ∀{l r} → LinDepT {i} l → LinDepT {i} r → LinDepT (l ∧ r)
    _∨_  : ∀{l r} → LinDepT {i} l → LinDepT {i} r → LinDepT (l ∨ r)
    -- ∂ takes a specific value. Only one of the two possible.
    ∂    : ∀{l r} → LinDepT {i} l ⊎ LinDepT {i} r → LinDepT (l ∂ r)
    call : ∀{∞ll} → ∞LinDepT {i} ∞ll → LinDepT (call ∞ll)

  record ∞LinDepT {i : Size} {u} (∞ll : ∞LinLogic i {u}) : Set (suc u) where
    coinductive
    field
      step : {j : Size< i} → LinDepT {j} (step ∞ll)

-- Given a linear transformation and a LinDepT,
-- this function computes the LinDepT of the transformed Linear Logic.
tran : ∀{u ll rll} → LinDepT {u = u} ll → LLTr {u = u} rll ll → LinDepT {u = u} rll
tran ldt I = ldt
tran (∂ (inj₁ l)) (∂c tr)           = tran (∂ (inj₂ l)) tr
tran (∂ (inj₂ r)) (∂c tr)           = tran (∂ (inj₁ r)) tr
tran (ldt ∧ ldt₁) (∧c tr)           = tran (ldt₁ ∧ ldt) tr
tran (ldt ∨ ldt₁) (∨c tr)           = tran (ldt₁ ∨ ldt) tr
tran (∂ (inj₁ l) ∧ ldt₁) (∧∂d tr)   = tran (∂ (inj₁ (l ∧ ldt₁))) tr
tran (∂ (inj₂ r) ∧ ldt₁) (∧∂d tr)   = tran (∂ (inj₂ (r ∧ ldt₁))) tr
tran ((ldt ∨ ldt₁) ∧ ldt₂) (∧∨d tr) = tran ((ldt ∧ ldt₂) ∨ (ldt₁ ∧ ldt₂) ) tr


-- Transform a LinDepT after a specific node pointed by the index ind.
itran : ∀{u ll pll rll} → LinDepT {u = u} ll → (ind : IndexLL pll ll) → LLTr {u = u} rll pll → LinDepT {u = u} $ replLL ll ind rll
itran ldt ↓ tr        = tran ldt tr
itran (ldt ∧ ldt₁) (ind ←∧) tr = itran ldt ind tr ∧ ldt₁
itran (ldt ∧ ldt₁) (∧→ ind) tr = ldt ∧ itran ldt₁ ind tr
itran (ldt ∨ ldt₁) (ind ←∨) tr = itran ldt ind tr ∨ ldt₁
itran (ldt ∨ ldt₁) (∨→ ind) tr = ldt ∨ itran ldt₁ ind tr
itran (∂ (inj₁ l)) (ind ←∂) tr = ∂ (inj₁ (itran l ind tr)) 
itran (∂ (inj₂ r)) (ind ←∂) tr = ∂ (inj₂ r)
itran (∂ (inj₁ l)) (∂→ ind) tr = ∂ (inj₁ l)
itran (∂ (inj₂ r)) (∂→ ind) tr = ∂ (inj₂ (itran r ind tr))


-- Truncuates the LinDepT, leaving only the node that is pointed by the index.
-- If the index points to a path that the LinDepT does not contain,
-- it returns nothing.
trunc : ∀{u ll pll} → LinDepT {u = u} ll → (ind : IndexLL pll ll) → Maybe $ LinDepT {u = u} pll
trunc ldt ↓ = just ldt
trunc (ldt ∧ ldt₁) (ind ←∧) = trunc ldt ind
trunc (ldt ∧ ldt₁) (∧→ ind) = trunc ldt₁ ind
trunc (ldt ∨ ldt₁) (ind ←∨) = trunc ldt ind
trunc (ldt ∨ ldt₁) (∨→ ind) = trunc ldt₁ ind
trunc (∂ (inj₁ l)) (ind ←∂) = trunc l ind
trunc (∂ (inj₂ r)) (ind ←∂) = nothing
trunc (∂ (inj₁ l)) (∂→ ind) = nothing
trunc (∂ (inj₂ r)) (∂→ ind) = trunc r ind

-- Replaces a node of LinDepT with another one.
replLDT : ∀{u ll q nll} → LinDepT {u = u} ll → (ind : IndexLL q ll) → LinDepT nll
          → LinDepT {u = u} $ replLL ll ind nll
replLDT ldt ↓ nldt = nldt
replLDT (ldt ∧ ldt₁) (ind ←∧) nldt = (replLDT ldt ind nldt) ∧ ldt₁
replLDT (ldt ∧ ldt₁) (∧→ ind) nldt = ldt ∧ (replLDT ldt₁ ind nldt)
replLDT (ldt ∨ ldt₁) (ind ←∨) nldt = (replLDT ldt ind nldt) ∨ ldt₁
replLDT (ldt ∨ ldt₁) (∨→ ind) nldt = ldt ∨ (replLDT ldt₁ ind nldt)
replLDT (∂ (inj₁ l)) (ind ←∂) nldt = ∂ $ inj₁ $ replLDT l ind nldt
replLDT (∂ (inj₂ r)) (ind ←∂) nldt = ∂ (inj₂ r)
replLDT (∂ (inj₁ l)) (∂→ ind) nldt = ∂ (inj₁ l)
replLDT (∂ (inj₂ r)) (∂→ ind) nldt = ∂ $ inj₂ $ replLDT r ind nldt


module _ {u : Level} where

  open RawMonad(monad {f = suc u})

-- If the index points to a path that is not part of LinDepT, then the same LinDepT can be the computation of
-- a different linear logic tree in which we replace the logic node that it does not contain.
  ifNotTruncLDT : ∀{i ll pll} → (ldt : LinDepT {u = u} ll)
                  → (ind : IndexLL pll ll) → (rll : LinLogic i)
                  →  Maybe $ LinDepT {u = u} $ replLL ll ind rll
  ifNotTruncLDT ldt ↓ rll = nothing
  ifNotTruncLDT (ldt ∧ ldt₁) (ind ←∧) rll = (ifNotTruncLDT ldt ind rll) >>= λ r → just (r ∧ ldt₁)
  ifNotTruncLDT (ldt ∧ ldt₁) (∧→ ind) rll = (ifNotTruncLDT ldt₁ ind rll) >>= λ r → just (ldt ∧ r)
  ifNotTruncLDT (ldt ∨ ldt₁) (ind ←∨) rll = (ifNotTruncLDT ldt ind rll) >>= λ r → just (r ∨ ldt₁)
  ifNotTruncLDT (ldt ∨ ldt₁) (∨→ ind) rll = (ifNotTruncLDT ldt₁ ind rll) >>= λ r → just (ldt ∨ r)
  ifNotTruncLDT (∂ (inj₁ l)) (ind ←∂) rll = (ifNotTruncLDT l ind rll) >>= λ r → just (∂ (inj₁ r))
  ifNotTruncLDT (∂ (inj₂ r)) (ind ←∂) rll = just (∂ (inj₂ r))
  ifNotTruncLDT (∂ (inj₁ l)) (∂→ ind) rll = just (∂ (inj₁ l))
  ifNotTruncLDT (∂ (inj₂ r)) (∂→ ind) rll =  (ifNotTruncLDT r ind rll) >>= λ r → just (∂ (inj₂ r))

  
