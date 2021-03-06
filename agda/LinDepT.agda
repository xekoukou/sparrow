module LinDepT where

open import Common
open import LinLogic
open import Data.Vec using (Vec)
open import Data.Sum
open import Data.Maybe
open import Category.Monad

open import Level


-- LinDepTᵢ is determined from the data of the input and needs to abide by the rules of LinLogic.
-- LinDepTᵢ is not computed by previous inputs because we are not aware of those inputs. In a multi-agent system,
-- not all information is known to all.

-- Input




data LinDepTᵢ {i u} : LinLogic i {u} → Set (lsuc u) where
  ∅     :                                  LinDepTᵢ ∅
  τ     : ∀{n} → {dt : Vec (Set u) n} → {df : genT dt} → (hv : HVec dt) → LinDepTᵢ (τ {dt = dt} df)
  _∧_   : ∀{l r} → LinDepTᵢ l → LinDepTᵢ r → LinDepTᵢ (l < ∧ > r)
  _∨_   : ∀{l r} → (ld : LinDepTᵢ l) → (rd : LinDepTᵢ r) → LinDepTᵢ (l < ∨ > r)





-- IMPORTANT LinDepTₒ is a local Data type. It only has meaning as the output of a specific Com of LinFun.
-- As soon as LinDepT is computed , we send the outputs with their type determined by LinDepT,
-- then LinDepT is forgotten.

-- Output
data LinDepTₒ {i : Size} {u} : LinLogic i {u} → Set (lsuc u) where
  ∅     :                                  LinDepTₒ ∅
  τ     : ∀{n} → {dt : Vec (Set u) n} → {df : genT dt} → (hv : HVec dt) → LinDepTₒ (τ {dt = dt} df)
  _∧_   : ∀{l r} → LinDepTₒ l → LinDepTₒ r → LinDepTₒ (l < ∧ > r)
  _∨_   : ∀{l r} → (ld : LinDepTₒ l) → (rd : LinDepTₒ r) → LinDepTₒ (l < ∨ > r)
  -- ∂ takes a specific value. Only one of the two possible.
  ∂     : ∀{l r} → LinDepTₒ l ⊎ LinDepTₒ r → LinDepTₒ (l < ∨ > r)






-- -- Given a linear transformation and a LinDepT,
-- -- this function computes the LinDepT of the transformed Linear Logic.
-- tran : ∀{i u ll rll} → LinDepT ll → LLTr {i} {u} rll ll → LinDepT rll
-- tran ldt I                            = ldt
-- tran (∂ (inj₁ l)) (∂c tr)             = tran (∂ (inj₂ l)) tr
-- tran (∂ (inj₂ r)) (∂c tr)             = tran (∂ (inj₁ r)) tr
-- tran (ldt ∧ ldt₁) (∧c tr)             = tran (ldt₁ ∧ ldt) tr
-- tran (ldt ∨ ldt₁) (∨c tr)             = tran (ldt₁ ∨ ldt) tr
-- tran (ldt ←∨) (∨c tr)                 = tran (∨→ ldt) tr
-- tran (∨→ ldt) (∨c tr)                 = tran (ldt ←∨) tr
-- -- tran (∂ (inj₁ l) ∧ ldt₁) (∧∂d tr)     = tran (∂ (inj₁ (l ∧ ldt₁))) tr
-- -- tran (∂ (inj₂ r) ∧ ldt₁) (∧∂d tr)     = tran (∂ (inj₂ (r ∧ ldt₁))) tr
-- -- tran ((ldt ∨ ldt₁) ∧ ldt₂) (∧∨d tr)   = tran ((ldt ∧ ldt₂) ∨ (ldt₁ ∧ ldt₂) ) tr
-- -- tran ((ldt ←∨ ) ∧ ldt₂) (∧∨d tr)      = tran ((ldt ∧ ldt₂) ←∨ ) tr
-- -- tran ((∨→ ldt₁) ∧ ldt₂) (∧∨d tr)      = tran (∨→ (ldt₁ ∧ ldt₂) ) tr
-- -- tran (∂ (inj₁ ldtl) ∨ ldt₁) (∨∂d tr)  = tran (∂ (inj₁ (ldtl ∨ ldt₁))) tr
-- -- tran (∂ (inj₂ ldtr) ∨ ldt₁) (∨∂d tr)  = tran (∂ (inj₂ (ldtr ∨ ldt₁))) tr
-- -- tran (∂ (inj₁ ldtl) ←∨) (∨∂d tr)      = tran (∂ (inj₁ (ldtl ←∨))) tr
-- -- tran (∂ (inj₂ ldtr) ←∨) (∨∂d tr)      = tran (∂ (inj₂ (ldtr ←∨))) tr
-- -- tran (∨→ ldt) (∨∂d tr)                = tran (∂ (inj₂ (∨→_ ldt))) tr
-- -- tran (∂ (inj₁ (l ∨ l₁))) (∂∨d tr)     = tran (∂ (inj₁ l) ∨ ∂ (inj₁ l₁)) tr
-- -- tran (∂ (inj₁ (l ←∨))) (∂∨d tr)       = tran (∂ (inj₁ l) ←∨) tr
-- -- tran (∂ (inj₁ (∨→ l))) (∂∨d tr)       = tran (∨→ (∂ (inj₁ l))) tr
-- -- tran (∂ (inj₂ r)) (∂∨d tr)            = tran ((∂ (inj₂ r)) ∨ (∂ (inj₂ r))) tr
-- tran ((ldt ∧ ldt₁) ∧ ldt₂) (∧∧d tr)   = tran (ldt ∧ (ldt₁ ∧ ldt₂)) tr
-- tran (ldt ∧ (ldt₁ ∧ ldt₂)) (¬∧∧d tr)  = tran ((ldt ∧ ldt₁) ∧ ldt₂) tr
-- tran ((ldt ∨ ldt₁) ∨ ldt₂) (∨∨d tr)   = tran (ldt ∨ (ldt₁ ∨ ldt₂)) tr
-- tran ((ldt ←∨) ∨ ldt₁) (∨∨d tr)       = tran (ldt ∨ (∨→ ldt₁)) tr
-- tran ((∨→ ldt) ∨ ldt₁) (∨∨d tr)       = tran (∨→ (ldt ∨ ldt₁)) tr
-- tran ((ldt ∨ ldt₁) ←∨) (∨∨d tr)       = tran (ldt ∨ (ldt₁ ←∨)) tr
-- tran ((ldt ←∨) ←∨) (∨∨d tr)           = tran (ldt ←∨) tr
-- tran ((∨→ ldt) ←∨) (∨∨d tr)           = tran (∨→ (ldt ←∨)) tr
-- tran (∨→ ldt) (∨∨d tr)                = tran (∨→ (∨→ ldt)) tr
-- tran (ldt ∨ (ldt₁ ∨ ldt₂)) (¬∨∨d tr)  = tran ((ldt ∨ ldt₁) ∨ ldt₂) tr
-- tran (ldt ∨ (ldt₁ ←∨)) (¬∨∨d tr) = tran ((ldt ∨ ldt₁) ←∨) tr
-- tran (ldt ∨ (∨→ ldt₁)) (¬∨∨d tr) = tran ((ldt ←∨) ∨ ldt₁) tr
-- tran (ldt ←∨) (¬∨∨d tr) = tran ((ldt ←∨) ←∨) tr
-- tran (∨→ (ldt ∨ ldt₁)) (¬∨∨d tr) = tran ((∨→ ldt) ∨ ldt₁) tr
-- tran (∨→ (ldt ←∨)) (¬∨∨d tr) = tran ((∨→ ldt) ←∨) tr
-- tran (∨→ (∨→ ldt)) (¬∨∨d tr) = tran (∨→ ldt) tr
-- tran (∂ (inj₁ (∂ (inj₁ l)))) (∂∂d tr) = tran (∂ (inj₁ l)) tr
-- tran (∂ (inj₁ (∂ (inj₂ r)))) (∂∂d tr) = tran (∂ (inj₂ (∂ (inj₁ r)))) tr
-- tran (∂ (inj₂ r)) (∂∂d tr)            = tran (∂ (inj₂ (∂ (inj₂ r)))) tr
-- tran (∂ (inj₁ l)) (¬∂∂d tr) = tran (∂ (inj₁ (∂ (inj₁ l)))) tr
-- tran (∂ (inj₂ (∂ (inj₁ l)))) (¬∂∂d tr) = tran (∂ (inj₁ (∂ (inj₂ l)))) tr
-- tran (∂ (inj₂ (∂ (inj₂ r)))) (¬∂∂d tr) = tran (∂ (inj₂ r)) tr

-- -- Transform a LinDepT after a specific node pointed by the index ind.
-- itran : ∀{i u ll pll rll} → LinDepT ll → (ind : IndexLL {i} {u} pll ll) → LLTr rll pll → LinDepT $ replLL ll ind rll
-- itran ldt ↓ tr                     = tran ldt tr
-- itran (ldt ∧ ldt₁) (ind ←∧) tr     = itran ldt ind tr ∧ ldt₁
-- itran (ldt ∧ ldt₁) (∧→ ind) tr     = ldt ∧ itran ldt₁ ind tr
-- itran (ldt ∨ ldt₁) (ind ←∨) tr = (itran ldt ind tr) ∨ ldt₁
-- itran (ldt ←∨) (ind ←∨) tr = (itran ldt ind tr) ←∨
-- itran (∨→ ldt₁) (ind ←∨) tr   = ∨→ ldt₁
-- itran (ldt ∨ ldt₁) (∨→ ind) tr = ldt ∨ (itran ldt₁ ind tr)
-- itran (ldt ←∨) (∨→ ind) tr    = ldt ←∨
-- itran (∨→ ldt₁) (∨→ ind) tr = ∨→ (itran ldt₁ ind tr)
-- itran (∂ (inj₁ l)) (ind ←∂) tr     = ∂ (inj₁ (itran l ind tr)) 
-- itran (∂ (inj₂ r)) (ind ←∂) tr     = ∂ (inj₂ r)
-- itran (∂ (inj₁ l)) (∂→ ind) tr     = ∂ (inj₁ l)
-- itran (∂ (inj₂ r)) (∂→ ind) tr     = ∂ (inj₂ (itran r ind tr))

-- -- -- TODO Should this be removed?
-- -- -- Truncuates the LinDepT, leaving only the node that is pointed by the index.
-- -- -- If the index points to a path that the LinDepT does not contain,
-- -- -- it returns nothing.
-- -- trunc : ∀{u ll pll} → LinDepT {u = u} ll → (ind : IndexLL pll ll) → Maybe $ LinDepT {u = u} pll
-- -- trunc ldt ↓ = just ldt
-- -- trunc (ldt ∧ ldt₁) (ind ←∧) = trunc ldt ind
-- -- trunc (ldt ∧ ldt₁) (∧→ ind) = trunc ldt₁ ind
-- -- trunc (def ldt ∨ ldt₁) (ind ←∨) = trunc ldt ind
-- -- trunc (undef ∨ ldt₁) (ind ←∨) = nothing
-- -- trunc (ldt ∨ def ldt₁) (∨→ ind) = trunc ldt₁ ind
-- -- trunc (ldt ∨ undef) (∨→ ind) = nothing
-- -- trunc (∂ (inj₁ l)) (ind ←∂) = trunc l ind
-- -- trunc (∂ (inj₂ r)) (ind ←∂) = nothing
-- -- trunc (∂ (inj₁ l)) (∂→ ind) = nothing
-- -- trunc (∂ (inj₂ r)) (∂→ ind) = trunc r ind
-- -- 
-- -- -- TODO Should this be removed?
-- -- -- Replaces a node of LinDepT with another one.
-- -- -- Undefined nodes remain undefined unless the index points to them.
-- -- replLDT : ∀{u ll q nll} → LinDepT {u = u} ll → (ind : IndexLL q ll) → LinDepT nll
-- --           → LinDepT {u = u} $ replLL ll ind nll
-- -- replLDT ldt ↓ nldt = nldt
-- -- replLDT (ldt ∧ ldt₁) (ind ←∧) nldt = (replLDT ldt ind nldt) ∧ ldt₁
-- -- replLDT (ldt ∧ ldt₁) (∧→ ind) nldt = ldt ∧ (replLDT ldt₁ ind nldt)
-- -- replLDT (ldt ∨ ldt₁) (ind ←∨) nldt = (replLDT ldt ind nldt) ∨ ldt₁
-- -- replLDT (ldt ∨ ldt₁) (∨→ ind) nldt = ldt ∨ (replLDT ldt₁ ind nldt)
-- -- replLDT (∂ (inj₁ l)) (ind ←∂) nldt = ∂ $ inj₁ $ replLDT l ind nldt
-- -- replLDT (∂ (inj₂ r)) (ind ←∂) nldt = ∂ (inj₂ r)
-- -- replLDT (∂ (inj₁ l)) (∂→ ind) nldt = ∂ (inj₁ l)
-- -- replLDT (∂ (inj₂ r)) (∂→ ind) nldt = ∂ $ inj₂ $ replLDT r ind nldt
-- -- 

-- module _ {u : Level} where

--   open RawMonad(monad {f = lsuc u})

-- -- TODO Should this be removed?
-- -- If the index points to a path that is not part of LinDepT, then the same LinDepT can be the computation of
-- -- a different linear logic tree in which we replace the logic node that it does not contain.
-- --   ifNotTruncLDT : ∀{i ll pll} → (ldt : LinDepT {u = u} ll)
-- --                   → (ind : IndexLL pll ll) → (rll : LinLogic i)
-- --                   →  Maybe $ LinDepT {u = u} $ replLL ll ind rll
-- --   ifNotTruncLDT ldt ↓ rll = nothing
-- --   ifNotTruncLDT (ldt ∧ ldt₁) (ind ←∧) rll = (ifNotTruncLDT ldt ind rll) >>= λ r → just (r ∧ ldt₁)
-- --   ifNotTruncLDT (ldt ∧ ldt₁) (∧→ ind) rll = (ifNotTruncLDT ldt₁ ind rll) >>= λ r → just (ldt ∧ r)
-- --   ifNotTruncLDT (ldt ∨ ldt₁) (ind ←∨) rll = (ifNotTruncLDT ldt ind rll) >>= λ r → just (r ∨ ldt₁)
-- --   ifNotTruncLDT (ldt ∨ ldt₁) (∨→ ind) rll = (ifNotTruncLDT ldt₁ ind rll) >>= λ r → just (ldt ∨ r)
-- --   ifNotTruncLDT (∂ (inj₁ l)) (ind ←∂) rll = (ifNotTruncLDT l ind rll) >>= λ r → just (∂ (inj₁ r))
-- --   ifNotTruncLDT (∂ (inj₂ r)) (ind ←∂) rll = just (∂ (inj₂ r))
-- --   ifNotTruncLDT (∂ (inj₁ l)) (∂→ ind) rll = just (∂ (inj₁ l))
-- --   ifNotTruncLDT (∂ (inj₂ r)) (∂→ ind) rll =  (ifNotTruncLDT r ind rll) >>= λ r → just (∂ (inj₂ r))


-- --module _ where
-- --
-- --  open SetLLMp
-- --
-- --  data LinState {i : Size} {u} : {ll : LinLogic i {u}} → SetLL ll → Set (suc u) where
-- --    ↓     : ∀{ll}         → LinDepT ll               → LinState (↓ {ll = ll})
-- --    _←∧   : ∀{rs ls s}    → LinState s               → LinState (_←∧ {rs = rs} {ls = ls} s)   
-- --    ∧→_   : ∀{rs ls s}    → LinState s               → LinState (∧→_ {rs = rs} {ls = ls} s)   
-- --    _←∧→_ : ∀{rs ls s s₁} → LinState s → LinState s₁ → LinState (_←∧→_ {rs = rs} {ls = ls} s s₁)   
-- --    _←∨   : ∀{rs ls s}    → LinState s               → LinState (_←∨ {rs = rs} {ls = ls} s) 
-- --    ∨→_   : ∀{rs ls s}    → LinState s               → LinState (∨→_ {rs = rs} {ls = ls} s) 
-- --    _←∂   : ∀{rs ls s}    → LinState s               → LinState (_←∂ {rs = rs} {ls = ls} s) 
-- --    ∂→_   : ∀{rs ls s}    → LinState s               → LinState (∂→_ {rs = rs} {ls = ls} s) 
-- --

-- -- We create a LinDepT in order to fill the gap for the cases that we do not have data.
-- --leftAll : All∅ ll → LinDepT

-- --all∅ : ∀{ll s} → FilledSetLL {ll = ll} s → LinDepT ll
-- --all∅ ↓ = ∅
-- --all∅ {ll = ls} (x ←∧) = {!_←∧ !}
-- --all∅ (∧→ x) = {!!}
-- --all∅ (x ←∨) = {!!}
-- --all∅ (∨→ x) = {!!}
-- --all∅ (x ←∂) = {!!}
-- --all∅ (∂→ x) = {!!}
