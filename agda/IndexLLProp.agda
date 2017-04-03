module IndexLLProp where

open import Common
open import LinLogic


updateIndex : ∀{i u rll ll} → ∀ nrll → (ind : IndexLL {i} {u} rll ll) → IndexLL {i} {u} nrll (replLL ll ind nrll)
updateIndex nrll ↓ = ↓
updateIndex nrll (ind ←∧) = (updateIndex nrll ind) ←∧
updateIndex nrll (∧→ ind) = ∧→ (updateIndex nrll ind)
updateIndex nrll (ind ←∨) = (updateIndex nrll ind) ←∨
updateIndex nrll (∨→ ind) = ∨→ (updateIndex nrll ind)
updateIndex nrll (ind ←∂) = (updateIndex nrll ind) ←∂
updateIndex nrll (∂→ ind) = ∂→ (updateIndex nrll ind)

composeInd : ∀{i u pll cll ll} → IndexLL {i} {u} pll ll → IndexLL cll pll → IndexLL cll ll
composeInd ↓ is = is
composeInd (if ←∧) is = (composeInd if is) ←∧
composeInd (∧→ if) is = ∧→ (composeInd if is)
composeInd (if ←∨) is = (composeInd if is) ←∨
composeInd (∨→ if) is = ∨→ (composeInd if is)
composeInd (if ←∂) is = (composeInd if is) ←∂
composeInd (∂→ if) is = ∂→ (composeInd if is)


