module IndexLLProp where

open import Common
open import LinLogic
open import Data.Maybe


updInd : ∀{i u rll ll} → ∀ nrll → (ind : IndexLL {i} {u} rll ll) → IndexLL {i} {u} nrll (replLL ll ind nrll)
updInd nrll ↓ = ↓
updInd nrll (ind ←∧) = (updInd nrll ind) ←∧
updInd nrll (∧→ ind) = ∧→ (updInd nrll ind)
updInd nrll (ind ←∨) = (updInd nrll ind) ←∨
updInd nrll (∨→ ind) = ∨→ (updInd nrll ind)
updInd nrll (ind ←∂) = (updInd nrll ind) ←∂
updInd nrll (∂→ ind) = ∂→ (updInd nrll ind)


-- It returns nothing if pll is transformed.
tran : ∀ {i u ll pll rll} → IndexLL pll ll → (ltr : LLTr {i} {u} rll ll)
       → Maybe $ IndexLL pll rll
tran ind I = just ind
tran ↓ (∂c ltr) = nothing
tran (ind ←∂) (∂c ltr) = tran (∂→ ind) ltr
tran (∂→ ind) (∂c ltr) = tran (ind ←∂) ltr
tran ↓ (∨c ltr) = nothing
tran (ind ←∨) (∨c ltr) = tran (∨→ ind) ltr
tran (∨→ ind) (∨c ltr) = tran (ind ←∨) ltr
tran ↓ (∧c ltr) = nothing
tran (ind ←∧) (∧c ltr) = tran (∧→ ind) ltr
tran (∧→ ind) (∧c ltr) = tran (ind ←∧) ltr
tran ↓ (∧∧d ltr) = nothing
tran (↓ ←∧) (∧∧d ltr) = nothing
tran ((ind ←∧) ←∧) (∧∧d ltr) = tran (ind ←∧) ltr
tran ((∧→ ind) ←∧) (∧∧d ltr) = tran (∧→ (ind ←∧)) ltr
tran (∧→ ↓) (∧∧d ltr) = nothing
tran (∧→ ind) (∧∧d ltr) = tran (∧→ (∧→ ind)) ltr
tran ↓ (¬∧∧d ltr) = nothing
tran (ind ←∧) (¬∧∧d ltr) = tran ((ind ←∧) ←∧) ltr
tran (∧→ ↓) (¬∧∧d ltr) = nothing
tran (∧→ (ind ←∧)) (¬∧∧d ltr) = tran ((∧→ ind) ←∧) ltr
tran (∧→ (∧→ ind)) (¬∧∧d ltr) = tran (∧→ ind) ltr
tran ↓ (∨∨d ltr) = nothing
tran (↓ ←∨) (∨∨d ltr) = nothing
tran ((ind ←∨) ←∨) (∨∨d ltr) = tran (ind ←∨) ltr
tran ((∨→ ind) ←∨) (∨∨d ltr) = tran (∨→ (ind ←∨)) ltr
tran (∨→ ↓) (∨∨d ltr) = nothing
tran (∨→ ind) (∨∨d ltr) = tran (∨→ (∨→ ind)) ltr
tran ↓ (¬∨∨d ltr) = nothing
tran (ind ←∨) (¬∨∨d ltr) = tran ((ind ←∨) ←∨) ltr
tran (∨→ ↓) (¬∨∨d ltr) = nothing
tran (∨→ (ind ←∨)) (¬∨∨d ltr) = tran ((∨→ ind) ←∨) ltr
tran (∨→ (∨→ ind)) (¬∨∨d ltr) = tran (∨→ ind) ltr
tran ↓ (∂∂d ltr) = nothing
tran (↓ ←∂) (∂∂d ltr) = nothing
tran ((ind ←∂) ←∂) (∂∂d ltr) = tran (ind ←∂) ltr
tran ((∂→ ind) ←∂) (∂∂d ltr) = tran (∂→ (ind ←∂)) ltr
tran (∂→ ↓) (∂∂d ltr) = nothing
tran (∂→ ind) (∂∂d ltr) = tran (∂→ (∂→ ind)) ltr
tran ↓ (¬∂∂d ltr) = nothing
tran (ind ←∂) (¬∂∂d ltr) = tran ((ind ←∂) ←∂) ltr
tran (∂→ ↓) (¬∂∂d ltr) = nothing
tran (∂→ (ind ←∂)) (¬∂∂d ltr) = tran ((∂→ ind) ←∂) ltr
tran (∂→ (∂→ ind)) (¬∂∂d ltr) = tran (∂→ ind) ltr

_+ᵢ_ : ∀{i u pll cll ll} → IndexLL {i} {u} pll ll → IndexLL cll pll → IndexLL cll ll
_+ᵢ_ ↓ is = is
_+ᵢ_ (if ←∧) is = (_+ᵢ_ if is) ←∧
_+ᵢ_ (∧→ if) is = ∧→ (_+ᵢ_ if is)
_+ᵢ_ (if ←∨) is = (_+ᵢ_ if is) ←∨
_+ᵢ_ (∨→ if) is = ∨→ (_+ᵢ_ if is)
_+ᵢ_ (if ←∂) is = (_+ᵢ_ if is) ←∂
_+ᵢ_ (∂→ if) is = ∂→ (_+ᵢ_ if is)


_-ᵢ_ : ∀ {i u pll cll ll} → IndexLL {i} {u} cll ll → IndexLL pll ll → Maybe $ IndexLL cll pll
a -ᵢ ↓ = just a
↓ -ᵢ (b ←∧) = nothing
(a ←∧) -ᵢ (b ←∧) = a -ᵢ b
(∧→ a) -ᵢ (b ←∧) = nothing
↓ -ᵢ (∧→ b) = nothing
(a ←∧) -ᵢ (∧→ b) = nothing
(∧→ a) -ᵢ (∧→ b) = a -ᵢ b
↓ -ᵢ (b ←∨) = nothing
(a ←∨) -ᵢ (b ←∨) = a -ᵢ b
(∨→ a) -ᵢ (b ←∨) = nothing
↓ -ᵢ (∨→ b) = nothing
(a ←∨) -ᵢ (∨→ b) = nothing
(∨→ a) -ᵢ (∨→ b) = a -ᵢ b
↓ -ᵢ (b ←∂) = nothing
(a ←∂) -ᵢ (b ←∂) = a -ᵢ b
(∂→ a) -ᵢ (b ←∂) = nothing
↓ -ᵢ (∂→ b) = nothing
(a ←∂) -ᵢ (∂→ b) = nothing
(∂→ a) -ᵢ (∂→ b) = a -ᵢ b

revUpdInd : ∀{i u ll cll ell pll} → (b : IndexLL pll ll) → (a : IndexLL {i} {u} cll (replLL ll b ell)) → a -ᵢ (updInd ell b) ≡ nothing → (updInd ell b) -ᵢ a ≡ nothing → IndexLL cll ll
revUpdInd ↓ a () b-a
revUpdInd (b ←∧) ↓ refl ()
revUpdInd (b ←∧) (a ←∧) a-b b-a = revUpdInd b a a-b b-a ←∧
revUpdInd (b ←∧) (∧→ a) a-b b-a = ∧→ a
revUpdInd (∧→ b) ↓ refl ()
revUpdInd (∧→ b) (a ←∧) a-b b-a = a ←∧
revUpdInd (∧→ b) (∧→ a) a-b b-a = ∧→ revUpdInd b a a-b b-a
revUpdInd (b ←∨) ↓ refl ()
revUpdInd (b ←∨) (a ←∨) a-b b-a = revUpdInd b a a-b b-a ←∨
revUpdInd (b ←∨) (∨→ a) a-b b-a = ∨→ a
revUpdInd (∨→ b) ↓ refl ()
revUpdInd (∨→ b) (a ←∨) a-b b-a = a ←∨
revUpdInd (∨→ b) (∨→ a) a-b b-a = ∨→ revUpdInd b a a-b b-a
revUpdInd (b ←∂) ↓ refl ()
revUpdInd (b ←∂) (a ←∂) a-b b-a = revUpdInd b a a-b b-a ←∂
revUpdInd (b ←∂) (∂→ a) a-b b-a = ∂→ a
revUpdInd (∂→ b) ↓ refl ()
revUpdInd (∂→ b) (a ←∂) a-b b-a = a ←∂
revUpdInd (∂→ b) (∂→ a) a-b b-a = ∂→ revUpdInd b a a-b b-a

