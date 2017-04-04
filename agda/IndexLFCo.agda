module IndexLFCo where

open import Common
open import LinLogic
open import LinLogicProp
open import LinFun
open import IndexLLProp
-- open import SetLL
open import Data.Maybe


-- reverseTran returns nothing if during the reversion, it finds a com.
-- or if the cll is transformed.

reverseTran : ∀{i u ll cll rll} → LFun ll rll → IndexLL {i} {u} cll rll → Maybe $ IndexLL cll ll
reverseTran I i = just i
reverseTran (_⊂_ {ell = ell} {ind = ind} lf lf₁) i with (reverseTran lf₁ i)
reverseTran (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) i | just x with (inspect (x -ᵢ (updInd ell ind)))
reverseTran (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) i | just x | ((just x₁) with-≡ eq₁) with (reverseTran lf x₁)
reverseTran (_⊂_ {pll} {ll} {ell} {_} {ind} lf lf₁) i | just x | ((just x₁) with-≡ eq₁) | (just x₂) = just $ ind +ᵢ x₂
reverseTran (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) i | just x | ((just x₁) with-≡ eq₁) | nothing = nothing
reverseTran (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) i | just x | (nothing with-≡ eq₁) with (inspect ((updInd ell ind) -ᵢ x))
reverseTran (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) i₁ | just x | (nothing with-≡ eq₁) | ((just x₁) with-≡ eq₂) = nothing -- We do not accept transformations that change the cll. The cll definitely changes here. (unless lf only has I).
reverseTran (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) i₁ | just x | (nothing with-≡ eq₁) | (nothing with-≡ eq₂) = just $ revUpdInd ind x eq₁ eq₂
reverseTran (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) i | nothing = nothing
reverseTran (tr ltr lf) i with (reverseTran lf i)
reverseTran (tr ltr lf) i₁ | just x = tran x $ revTr ltr
reverseTran (tr ltr lf) i₁ | nothing = nothing
reverseTran (com df lf) i = nothing
reverseTran (call x) i = nothing 


-- This is almost the same code as above but it is required in IndexLFCo.
indRevNoComs : ∀{i u ll pll ell cll} → (ind : IndexLL {i} {u} pll ll) → IndexLL cll (replLL ll ind ell) → LFun pll ell → Maybe $ IndexLL cll ll
indRevNoComs {ell = ell} ind lind lf with (inspect (lind -ᵢ (updInd ell ind)))
indRevNoComs {_} {_} {_} {_} {ell} ind lind lf | just x with-≡ eq with (reverseTran lf x)
indRevNoComs {_} {_} {_} {_} {ell} ind lind lf | just x with-≡ eq | (just x₁) = just $ ind +ᵢ x₁
indRevNoComs {_} {_} {_} {_} {ell} ind lind lf | just x with-≡ eq | nothing = nothing
indRevNoComs {_} {_} {_} {_} {ell} ind lind lf | nothing with-≡ eq with (inspect ((updInd ell ind) -ᵢ lind))
indRevNoComs {_} {_} {_} {_} {ell} ind lind lf | nothing with-≡ eq | (just x with-≡ eq₁) = nothing
indRevNoComs {_} {_} {_} {_} {ell} ind lind lf | nothing with-≡ eq | (nothing with-≡ eq₁) = just $ revUpdInd ind lind eq eq₁
 

data IndexLFCo {i u cll} (frll : LinLogic i {u}) : ∀{ll rll} → IndexLL cll ll → LFun {i} {u} ll rll → Set (u) where
  _←⊂ : ∀{rll pll ell ll ind elf lf lind}
         → IndexLFCo frll lind elf
         → IndexLFCo frll (ind +ᵢ lind) (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  ⊂→_ : ∀{rll pll ell ll ind elf lf lind rs}
         → IndexLFCo frll lind lf
         → {prf : just rs ≡ indRevNoComs ind lind elf}
         → IndexLFCo frll rs (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  tr   : ∀{ll orll rll lind rs} → {ltr : LLTr orll ll} → {lf : LFun {i} {u} orll rll}
         → IndexLFCo frll lind lf
         → {prf : just rs ≡ tran lind (revTr ltr) }
         → IndexLFCo frll rs (tr ltr lf) 
  ↓  : ∀{rll prfi prfo df lf}
         → IndexLFCo  frll ↓ (com {i} {u} {rll} {cll} {frll} {{prfi}} {{prfo}} df lf)
