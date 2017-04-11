{-# OPTIONS --exact-split #-}
module IndexLFCo where

open import Common
open import LinLogic
open import LinLogicProp
open import LinFun
open import IndexLLProp
open import Data.Maybe

module _ where

  open import Relation.Binary.PropositionalEquality using (sym)
  open  Relation.Binary.PropositionalEquality.Deprecated-inspect


  -- reverseTran returns nothing if during the reversion, it finds a com.
  -- or if the cll is transformed.
  


  mutual
    data ReverseTranT {i u} : ∀{ll cll rll} → LFun ll rll → IndexLL {i} {u} cll rll → Set u where
      cr1 : ∀{cll rll} → {iind : IndexLL {i} {u} cll rll} → ReverseTranT I iind
      cr2 : ∀{ll cll rll ell pll ind lf₁ lf x₁} → {iind : IndexLL {i} {u} cll rll} → (rvT₁ : ReverseTranT lf₁ iind) → let x = reverseTran lf₁ iind rvT₁ in (just x₁ ≡ x -ₘᵢ (updInd ell ind)) → (rvT₂ : ReverseTranT lf x₁) → ReverseTranT (_⊂_ {pll = pll} {ll = ll} {ell = ell} {rll = rll} {ind = ind} lf lf₁) iind
      cr3 : ∀{ll cll rll ell pll ind lf₁ lf} → {iind : IndexLL {i} {u} cll rll} → (rvT₁ : ReverseTranT lf₁ iind) → let x = reverseTran lf₁ iind rvT₁ in (eq₁ : (x -ₘᵢ (updInd ell ind) ≡ nothing)) → (eq₂ :((updInd ell ind) -ₘᵢ x ≡ nothing)) → ReverseTranT (_⊂_ {pll = pll} {ll = ll} {ell = ell} {rll = rll} {ind = ind} lf lf₁) iind
      cr4 : ∀{ll cll orll rll lf x} → {ltr : LLTr orll ll} → {iind : IndexLL {i} {u} cll rll} → (rvT₁ : ReverseTranT lf iind) → (just x ≡ tran (reverseTran lf iind rvT₁) (revTr ltr)) → ReverseTranT (tr ltr lf) iind



    -- reverseTran returns nothing if during the reversion, it finds a com.
    -- or if the cll is transformed.
  
    reverseTran : ∀{i u ll cll rll} → (lf : LFun ll rll) → (iind : IndexLL {i} {u} cll rll) → ReverseTranT lf iind → IndexLL cll ll
    reverseTran .I iind cr1 = iind
    reverseTran (_⊂_ {ind = ind} lf lf₁) iind (cr2 {x₁ = x₁} pr x pr₁) =  ind +ᵢ (reverseTran lf x₁ pr₁)
    reverseTran (_⊂_ {ind = ind} _ lf₁) iind (cr3 pr eq₁ eq₂) = revUpdInd ind (reverseTran lf₁ iind pr) eq₁ eq₂
    reverseTran (tr ltr lf) iind (cr4 {x = x} pr eq) = x


  getReverseTranT : ∀{i u ll cll rll} → (lf : LFun ll rll) → (iind : IndexLL {i} {u} cll rll) → Maybe $ ReverseTranT lf iind
  getReverseTranT I iind = just cr1
  getReverseTranT (_⊂_ {ell = ell} {ind = ind} lf lf₁) iind with (getReverseTranT lf₁ iind)
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind | just x with (inspect ((reverseTran lf₁ iind x) -ₘᵢ (updInd ell ind)))
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind | just x | ((just x₁) with-≡ eq) with (getReverseTranT lf x₁)
  getReverseTranT (_⊂_ {pll} {ll} {ell} {rll} {ind} lf lf₁) iind | just x | (just x₁ with-≡ eq) | (just x₂) = just (cr2 x (sym eq) x₂)
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind | just x | (just x₁ with-≡ eq) | nothing = nothing
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind | just x | (nothing with-≡ eq) with (inspect ((updInd ell ind) -ₘᵢ (reverseTran lf₁ iind x)))
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind | just x | (nothing with-≡ eq) | (just x₁ with-≡ eq₁) = nothing -- We do not accept transformations that change the cll. The cll definitely changes here. (unless lf only has iind).
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind | just x | (nothing with-≡ eq) | (nothing with-≡ eq₁) = just (cr3 x eq eq₁)
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind | nothing = nothing
  getReverseTranT (tr ltr lf) iind with (getReverseTranT lf iind)
  getReverseTranT (tr ltr lf) iind | just x with (inspect (tran (reverseTran lf iind x) (revTr ltr)))
  getReverseTranT (tr ltr lf) iind | just x | (just x₁ with-≡ eq) = just (cr4 x (sym eq))
  getReverseTranT (tr ltr lf) iind | just x | (nothing with-≡ eq) = nothing
  getReverseTranT (tr ltr lf) iind | nothing = nothing
  getReverseTranT (com df lf) iind = nothing
  getReverseTranT (call x) iind = nothing

  data IndRevNoComsT {i u ll pll ell cll} {ind : IndexLL {i} {u} pll ll} {lind : IndexLL cll (replLL ll ind ell)} {lf : LFun pll ell} : Set u where
    c1 : ∀{x} → (just x ≡ lind -ₘᵢ (updInd ell ind)) → (ReverseTranT lf x) → IndRevNoComsT
    c2 : (lind -ₘᵢ (updInd ell ind) ≡ nothing) → ((updInd ell ind) -ₘᵢ lind ≡ nothing) → IndRevNoComsT


  indRevNoComs : ∀{i u ll pll ell cll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll (replLL ll ind ell)) → (lf : LFun pll ell) → IndRevNoComsT {ind = ind} {lind = lind} {lf = lf} → IndexLL cll ll
  indRevNoComs ind lind lf (c1 {x = x} b pr) = ind +ᵢ (reverseTran lf x pr)
  indRevNoComs ind lind lf (c2 eq₁ eq₂) = revUpdInd ind lind eq₁ eq₂


-- This is almost the same code as above but it is required in IndexLFCo.
  getIndRevNoComsT : ∀{i u ll pll ell cll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll (replLL ll ind ell)) → (lf : LFun pll ell) → Maybe $ IndRevNoComsT {ind = ind} {lind = lind} {lf = lf}
  getIndRevNoComsT {ell = ell} ind lind lf with (inspect (lind -ₘᵢ (updInd ell ind)))
  getIndRevNoComsT {_} {_} {_} {_} {ell} ind lind lf | just x with-≡ eq with (getReverseTranT lf x)
  getIndRevNoComsT {_} {_} {_} {_} {ell} ind lind lf | just x with-≡ eq | (just x₁) = just (c1 (sym eq) x₁)
  getIndRevNoComsT {_} {_} {_} {_} {ell} ind lind lf | just x with-≡ eq | nothing = nothing
  getIndRevNoComsT {_} {_} {_} {_} {ell} ind lind lf | nothing with-≡ eq with (inspect ((updInd ell ind) -ₘᵢ lind))
  getIndRevNoComsT {_} {_} {_} {_} {ell} ind lind lf | nothing with-≡ eq | (just x with-≡ eq₁) = nothing
  getIndRevNoComsT {_} {_} {_} {_} {ell} ind lind lf | nothing with-≡ eq | (nothing with-≡ eq₁) = just (c2 eq eq₁)

  
data IndexLFCo {i u cll} (frll : LinLogic i {u}) : ∀{ll rll} → IndexLL cll ll → LFun {i} {u} ll rll → Set (u) where
  _←⊂ : ∀{rll pll ell ll ind elf lf lind}
         → IndexLFCo frll lind elf
         → IndexLFCo frll (ind +ᵢ lind) (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  ⊂→_ : ∀{rll pll ell ll ind elf lf lind rs}
         → IndexLFCo frll lind lf
         → (irnc : IndRevNoComsT {ind = ind} {lind = lind} {lf = elf})
         → {prf : rs ≡ indRevNoComs ind lind elf irnc}
         → IndexLFCo frll rs (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  tr  : ∀{ll orll rll lind rs} → {ltr : LLTr orll ll} → {lf : LFun {i} {u} orll rll}
         → IndexLFCo frll lind lf
         → {prf : just rs ≡ tran lind (revTr ltr) }
         → IndexLFCo frll rs (tr ltr lf) 
  ↓  : ∀{rll prfi prfo df lf}
         → IndexLFCo  frll ↓ (com {i} {u} {rll} {cll} {frll} {{prfi}} {{prfo}} df lf)



data SetLFCoRem {i u oll orll} (olf : LFun {i} {u} oll orll) : LinLogic i {u} → Set (lsuc u) where
  ↓    : ∀{ll cll frll} → {ind : IndexLL {i} {u} cll oll} → IndexLFCo frll ind olf → SetLFCoRem olf ll
  _←∧   : ∀{rs ls} → SetLFCoRem olf ls                   → SetLFCoRem olf (ls ∧ rs)
  ∧→_   : ∀{rs ls} → SetLFCoRem olf rs                   → SetLFCoRem olf (ls ∧ rs)
  _←∧→_ : ∀{rs ls} → SetLFCoRem olf ls → SetLFCoRem olf rs → SetLFCoRem olf (ls ∧ rs)
  _←∨   : ∀{rs ls} → SetLFCoRem olf ls                   → SetLFCoRem olf (ls ∨ rs)
  ∨→_   : ∀{rs ls} → SetLFCoRem olf rs                   → SetLFCoRem olf (ls ∨ rs)
  _←∨→_ : ∀{rs ls} → SetLFCoRem olf ls → SetLFCoRem olf rs → SetLFCoRem olf (ls ∨ rs)
  _←∂   : ∀{rs ls} → SetLFCoRem olf ls                   → SetLFCoRem olf (ls ∂ rs)
  ∂→_   : ∀{rs ls} → SetLFCoRem olf rs                   → SetLFCoRem olf (ls ∂ rs)
  _←∂→_ : ∀{rs ls} → SetLFCoRem olf ls → SetLFCoRem olf rs → SetLFCoRem olf (ls ∂ rs)

data MSetLFCoRem {i u oll orll} (olf : LFun {i} {u} oll orll) : LinLogic i {u} → Set (lsuc u) where
  ∅   : ∀{ll}            → MSetLFCoRem olf ll
  ¬∅  : ∀{ll} → SetLFCoRem olf ll → MSetLFCoRem olf ll

∅-addLFCoRem : ∀{i u ll pll oll orll frll cll} → {iind : IndexLL cll oll} → {olf : LFun {i} {u} oll orll} → (ind : IndexLL {i} {u} pll ll) → IndexLFCo frll iind olf
        → SetLFCoRem olf ll
∅-addLFCoRem ↓ m = ↓ m
∅-addLFCoRem (ind ←∧) m = (∅-addLFCoRem ind m) ←∧
∅-addLFCoRem (∧→ ind) m = ∧→ (∅-addLFCoRem ind m)
∅-addLFCoRem (ind ←∨) m = (∅-addLFCoRem ind m) ←∨
∅-addLFCoRem (∨→ ind) m = ∨→ (∅-addLFCoRem ind m)
∅-addLFCoRem (ind ←∂) m = (∅-addLFCoRem ind m) ←∂
∅-addLFCoRem (∂→ ind) m = ∂→ (∅-addLFCoRem ind m)

addLFCoRem : ∀{i u ll pll oll orll frll cll} → {iind : IndexLL cll oll} → {olf : LFun {i} {u} oll orll} → SetLFCoRem olf ll → (ind : IndexLL {i} {u} pll ll) → IndexLFCo frll iind olf
        → SetLFCoRem olf ll
addLFCoRem (↓ rm) ind m          = ↓ m
addLFCoRem (x ←∧) ↓ m            = ↓ m
addLFCoRem (∧→ x) ↓ m            = ↓ m --TODO Here we lose the information that is at lower levels.
addLFCoRem (x ←∧→ x₁) ↓ m        = ↓ m
addLFCoRem (x ←∨) ↓ m            = ↓ m
addLFCoRem (∨→ x) ↓ m            = ↓ m
addLFCoRem (x ←∨→ x₁) ↓ m        = ↓ m
addLFCoRem (x ←∂) ↓ m            = ↓ m
addLFCoRem (∂→ x) ↓ m            = ↓ m
addLFCoRem (x ←∂→ x₁) ↓ m        = ↓ m
addLFCoRem (s ←∧) (ind ←∧) m     = (addLFCoRem s ind m) ←∧
addLFCoRem (s ←∧) (∧→ ind) m     = s ←∧→ (∅-addLFCoRem ind m)
addLFCoRem (∧→ s) (ind ←∧) m     = (∅-addLFCoRem ind m) ←∧→ s
addLFCoRem (∧→ s) (∧→ ind) m     = ∧→ addLFCoRem s ind m
addLFCoRem (s ←∧→ s₁) (ind ←∧) m = (addLFCoRem s ind m) ←∧→ s₁
addLFCoRem (s ←∧→ s₁) (∧→ ind) m = s ←∧→ (addLFCoRem s₁ ind m)
addLFCoRem (s ←∨) (ind ←∨) m     = (addLFCoRem s ind m) ←∨
addLFCoRem (s ←∨) (∨→ ind) m     = s ←∨→ (∅-addLFCoRem ind m)
addLFCoRem (∨→ s) (ind ←∨) m     = (∅-addLFCoRem ind m) ←∨→ s
addLFCoRem (∨→ s) (∨→ ind) m     = ∨→ addLFCoRem s ind m
addLFCoRem (s ←∨→ s₁) (ind ←∨) m = (addLFCoRem s ind m) ←∨→ s₁
addLFCoRem (s ←∨→ s₁) (∨→ ind) m = s ←∨→ (addLFCoRem s₁ ind m)
addLFCoRem (s ←∂) (ind ←∂) m     = (addLFCoRem s ind m) ←∂
addLFCoRem (s ←∂) (∂→ ind) m     = s ←∂→ (∅-addLFCoRem ind m)
addLFCoRem (∂→ s) (ind ←∂) m     = (∅-addLFCoRem ind m) ←∂→ s
addLFCoRem (∂→ s) (∂→ ind) m     = ∂→ addLFCoRem s ind m
addLFCoRem (s ←∂→ s₁) (ind ←∂) m = (addLFCoRem s ind m) ←∂→ s₁
addLFCoRem (s ←∂→ s₁) (∂→ ind) m = s ←∂→ (addLFCoRem s₁ ind m)

maddLFCoRem : ∀{i u ll pll oll orll frll cll} → {iind : IndexLL cll oll} → {olf : LFun {i} {u} oll orll} → MSetLFCoRem olf ll → (ind : IndexLL {i} {u} pll ll) → IndexLFCo frll iind olf
      → MSetLFCoRem olf ll
maddLFCoRem ∅ ind m = ¬∅ (∅-addLFCoRem ind m)
maddLFCoRem (¬∅ x) ind m = ¬∅ (addLFCoRem x ind m)


truncSetLFCoRem : ∀{i} → ∀{u ll oll orll q} → {olf : LFun {i} {u} oll orll} → MSetLFCoRem {i} {u} olf ll → (ind : IndexLL {i} {u} q ll) → MSetLFCoRem {i} olf q
truncSetLFCoRem ∅ ind = ∅
truncSetLFCoRem (¬∅ x) ↓ = ¬∅ x
truncSetLFCoRem (¬∅ (↓ x)) (ind ←∧) = ∅
truncSetLFCoRem (¬∅ (x ←∧)) (ind ←∧) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (∧→ x)) (ind ←∧) = ∅
truncSetLFCoRem (¬∅ (x ←∧→ x₁)) (ind ←∧) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (↓ x)) (∧→ ind) = ∅
truncSetLFCoRem (¬∅ (x ←∧)) (∧→ ind) = ∅
truncSetLFCoRem (¬∅ (∧→ x)) (∧→ ind) =  truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (x ←∧→ x₁)) (∧→ ind) =  truncSetLFCoRem (¬∅ x₁) ind
truncSetLFCoRem (¬∅ (↓ x)) (ind ←∨) = ∅
truncSetLFCoRem (¬∅ (x ←∨)) (ind ←∨) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (∨→ x)) (ind ←∨) = ∅
truncSetLFCoRem (¬∅ (x ←∨→ x₁)) (ind ←∨) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (↓ x)) (∨→ ind) = ∅
truncSetLFCoRem (¬∅ (x ←∨)) (∨→ ind) = ∅
truncSetLFCoRem (¬∅ (∨→ x)) (∨→ ind) =  truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (x ←∨→ x₁)) (∨→ ind) =  truncSetLFCoRem (¬∅ x₁) ind
truncSetLFCoRem (¬∅ (↓ x)) (ind ←∂) = ∅
truncSetLFCoRem (¬∅ (x ←∂)) (ind ←∂) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (∂→ x)) (ind ←∂) = ∅
truncSetLFCoRem (¬∅ (x ←∂→ x₁)) (ind ←∂) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (↓ x)) (∂→ ind) = ∅
truncSetLFCoRem (¬∅ (x ←∂)) (∂→ ind) = ∅
truncSetLFCoRem (¬∅ (∂→ x)) (∂→ ind) =  truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (x ←∂→ x₁)) (∂→ ind) =  truncSetLFCoRem (¬∅ x₁) ind

delLFCoRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → SetLFCoRem {i} olf ll → (ind : IndexLL {i} {u} pll ll) → (rll : LinLogic i)
      → MSetLFCoRem {i} olf (replLL ll ind rll)
delLFCoRem s ↓ rll = ∅
delLFCoRem (↓ x) (ind ←∧) rll = ∅ -- We loose Information.
delLFCoRem (s ←∧) (ind ←∧) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∧) (ind ←∧) rll | ∅ = ∅
delLFCoRem (s ←∧) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧)
delLFCoRem (∧→ s) (ind ←∧) rll = ¬∅ (∧→ (s))
delLFCoRem (s ←∧→ s₁) (ind ←∧) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∧→ s₁) (ind ←∧) rll | ∅ = ¬∅ (∧→ (s₁))
delLFCoRem (s ←∧→ s₁) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧→ (s₁))
delLFCoRem (↓ x) (∧→ ind) rll = ∅ --
delLFCoRem (s ←∧) (∧→ ind) rll = ¬∅ ((s) ←∧)
delLFCoRem (∧→ s) (∧→ ind) rll with (delLFCoRem s ind rll)
delLFCoRem (∧→ s) (∧→ ind) rll | ∅ = ∅
delLFCoRem (∧→ s) (∧→ ind) rll | ¬∅ x = ¬∅ (∧→ x)
delLFCoRem (s ←∧→ s₁) (∧→ ind) rll with (delLFCoRem s₁ ind rll)
delLFCoRem (s ←∧→ s₁) (∧→ ind) rll | ∅ = ¬∅ ((s) ←∧)
delLFCoRem (s ←∧→ s₁) (∧→ ind) rll | ¬∅ x = ¬∅ ((s) ←∧→ x)
delLFCoRem (↓ x) (ind ←∨) rll = ∅
delLFCoRem (s ←∨) (ind ←∨) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∨) (ind ←∨) rll | ∅ = ∅
delLFCoRem (s ←∨) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨)
delLFCoRem (∨→ s) (ind ←∨) rll = ¬∅ (∨→ (s))
delLFCoRem (s ←∨→ s₁) (ind ←∨) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∨→ s₁) (ind ←∨) rll | ∅ = ¬∅ (∨→ (s₁))
delLFCoRem (s ←∨→ s₁) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨→ (s₁))
delLFCoRem (↓ x) (∨→ ind) rll = ∅
delLFCoRem (s ←∨) (∨→ ind) rll = ¬∅ ((s) ←∨)
delLFCoRem (∨→ s) (∨→ ind) rll with (delLFCoRem s ind rll)
delLFCoRem (∨→ s) (∨→ ind) rll | ∅ = ∅
delLFCoRem (∨→ s) (∨→ ind) rll | ¬∅ x = ¬∅ (∨→ x)
delLFCoRem (s ←∨→ s₁) (∨→ ind) rll with (delLFCoRem s₁ ind rll)
delLFCoRem (s ←∨→ s₁) (∨→ ind) rll | ∅ = ¬∅ ((s) ←∨)
delLFCoRem (s ←∨→ s₁) (∨→ ind) rll | ¬∅ x = ¬∅ ((s) ←∨→ x)
delLFCoRem (↓ x) (ind ←∂) rll = ∅
delLFCoRem (s ←∂) (ind ←∂) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∂) (ind ←∂) rll | ∅ = ∅
delLFCoRem (s ←∂) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂)
delLFCoRem (∂→ s) (ind ←∂) rll = ¬∅ (∂→ (s))
delLFCoRem (s ←∂→ s₁) (ind ←∂) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∂→ s₁) (ind ←∂) rll | ∅ = ¬∅ (∂→ (s₁))
delLFCoRem (s ←∂→ s₁) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂→ (s₁))
delLFCoRem (↓ x) (∂→ ind) rll = ∅
delLFCoRem (s ←∂) (∂→ ind) rll = ¬∅ ((s) ←∂)
delLFCoRem (∂→ s) (∂→ ind) rll with (delLFCoRem s ind rll)
delLFCoRem (∂→ s) (∂→ ind) rll | ∅ = ∅
delLFCoRem (∂→ s) (∂→ ind) rll | ¬∅ x = ¬∅ (∂→ x)
delLFCoRem (s ←∂→ s₁) (∂→ ind) rll with (delLFCoRem s₁ ind rll)
delLFCoRem (s ←∂→ s₁) (∂→ ind) rll | ∅ = ¬∅ ((s) ←∂)
delLFCoRem (s ←∂→ s₁) (∂→ ind) rll | ¬∅ x = ¬∅ ((s) ←∂→ x)

mdelLFCoRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → MSetLFCoRem {i} olf ll → (ind : IndexLL {i} {u} pll ll) → (rll : LinLogic i)
             → MSetLFCoRem {i} olf (replLL ll ind rll)
mdelLFCoRem ∅ ind rll = ∅
mdelLFCoRem (¬∅ x) ind rll = delLFCoRem x ind rll

tranLFCoRem : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → SetLFCoRem {i} olf ll → (tr : LLTr {i} {u} rll ll)
       → SetLFCoRem olf rll
tranLFCoRem s I                           = s
tranLFCoRem (s ←∂) (∂c ltr)                = tranLFCoRem (∂→ s) ltr
tranLFCoRem (↓ x) (∂c ltr)                = ↓ x
tranLFCoRem (∂→ s) (∂c ltr)                = tranLFCoRem (s ←∂) ltr
tranLFCoRem (s ←∂→ s₁) (∂c ltr)            = tranLFCoRem (s₁ ←∂→ s) ltr
tranLFCoRem (s ←∨) (∨c ltr)                = tranLFCoRem (∨→ s) ltr
tranLFCoRem (↓ x) (∨c ltr)                = ↓ x
tranLFCoRem (∨→ s) (∨c ltr)                = tranLFCoRem (s ←∨) ltr
tranLFCoRem (s ←∨→ s₁) (∨c ltr)            = tranLFCoRem (s₁ ←∨→ s) ltr
tranLFCoRem (s ←∧) (∧c ltr)                = tranLFCoRem (∧→ s) ltr
tranLFCoRem (↓ x) (∧c ltr)                = ↓ x
tranLFCoRem (∧→ s) (∧c ltr)                = tranLFCoRem (s ←∧) ltr
tranLFCoRem (s ←∧→ s₁) (∧c ltr)            = tranLFCoRem (s₁ ←∧→ s) ltr
tranLFCoRem ((s ←∧) ←∧) (∧∧d ltr)          = tranLFCoRem (s ←∧) ltr
tranLFCoRem (↓ x) (∧∧d ltr)          = ↓ x
tranLFCoRem ((↓ x) ←∧) (∧∧d ltr)          = tranLFCoRem ((↓ x) ←∧→ ((↓ x) ←∧)) ltr
tranLFCoRem ((∧→ s) ←∧) (∧∧d ltr)          = tranLFCoRem (∧→ (s ←∧)) ltr
tranLFCoRem ((s ←∧→ s₁) ←∧) (∧∧d ltr)      = tranLFCoRem (s ←∧→ (s₁ ←∧)) ltr
tranLFCoRem (∧→ s) (∧∧d ltr)               = tranLFCoRem (∧→ (∧→ s)) ltr
tranLFCoRem ((↓ x) ←∧→ s₁) (∧∧d ltr)      = tranLFCoRem ((↓ x) ←∧→ ((↓ x) ←∧→ s₁)) ltr
tranLFCoRem ((s ←∧) ←∧→ s₁) (∧∧d ltr)      = tranLFCoRem (s ←∧→ (∧→ s₁)) ltr
tranLFCoRem ((∧→ s) ←∧→ s₁) (∧∧d ltr)      = tranLFCoRem (∧→ (s ←∧→ s₁)) ltr
tranLFCoRem ((s ←∧→ s₁) ←∧→ s₂) (∧∧d ltr)  = tranLFCoRem (s ←∧→ (s₁ ←∧→ s₂)) ltr
tranLFCoRem (s ←∧) (¬∧∧d ltr)              = tranLFCoRem ((s ←∧) ←∧) ltr
tranLFCoRem (↓ x) (¬∧∧d ltr)              = ↓ x
tranLFCoRem (∧→ (↓ x)) (¬∧∧d ltr)         = tranLFCoRem ((∧→ (↓ x)) ←∧→ (↓ x)) ltr
tranLFCoRem (∧→ (s ←∧)) (¬∧∧d ltr)         = tranLFCoRem ((∧→ s) ←∧) ltr
tranLFCoRem (∧→ (∧→ s)) (¬∧∧d ltr)         = tranLFCoRem (∧→ s) ltr
tranLFCoRem (∧→ (s ←∧→ s₁)) (¬∧∧d ltr)     = tranLFCoRem ((∧→ s) ←∧→ s₁) ltr
tranLFCoRem (s ←∧→ (↓ x)) (¬∧∧d ltr)     = tranLFCoRem ((s ←∧→ (↓ x)) ←∧→ (↓ x)) ltr
tranLFCoRem (s ←∧→ (s₁ ←∧)) (¬∧∧d ltr)     = tranLFCoRem ((s ←∧→ s₁) ←∧) ltr
tranLFCoRem (s ←∧→ (∧→ s₁)) (¬∧∧d ltr)     = tranLFCoRem ((s ←∧) ←∧→ s₁) ltr
tranLFCoRem (s ←∧→ (s₁ ←∧→ s₂)) (¬∧∧d ltr) = tranLFCoRem ((s ←∧→ s₁) ←∧→ s₂) ltr
tranLFCoRem ((s ←∨) ←∨) (∨∨d ltr)          = tranLFCoRem (s ←∨) ltr
tranLFCoRem (↓ x) (∨∨d ltr)          = ↓ x
tranLFCoRem ((↓ x) ←∨) (∨∨d ltr)          = tranLFCoRem ((↓ x) ←∨→ ((↓ x) ←∨)) ltr
tranLFCoRem ((∨→ s) ←∨) (∨∨d ltr)          = tranLFCoRem (∨→ (s ←∨)) ltr
tranLFCoRem ((s ←∨→ s₁) ←∨) (∨∨d ltr)      = tranLFCoRem (s ←∨→ (s₁ ←∨)) ltr
tranLFCoRem (∨→ s) (∨∨d ltr)               = tranLFCoRem (∨→ (∨→ s)) ltr
tranLFCoRem ((↓ x) ←∨→ s₁) (∨∨d ltr)      = tranLFCoRem ((↓ x) ←∨→ ((↓ x) ←∨→ s₁)) ltr
tranLFCoRem ((s ←∨) ←∨→ s₁) (∨∨d ltr)      = tranLFCoRem (s ←∨→ (∨→ s₁)) ltr
tranLFCoRem ((∨→ s) ←∨→ s₁) (∨∨d ltr)      = tranLFCoRem (∨→ (s ←∨→ s₁)) ltr
tranLFCoRem ((s ←∨→ s₁) ←∨→ s₂) (∨∨d ltr)  = tranLFCoRem (s ←∨→ (s₁ ←∨→ s₂)) ltr
tranLFCoRem (s ←∨) (¬∨∨d ltr)              = tranLFCoRem ((s ←∨) ←∨) ltr
tranLFCoRem (↓ x) (¬∨∨d ltr)              = ↓ x
tranLFCoRem (∨→ (↓ x)) (¬∨∨d ltr)         = tranLFCoRem ((∨→ (↓ x)) ←∨→ (↓ x)) ltr
tranLFCoRem (∨→ (s ←∨)) (¬∨∨d ltr)         = tranLFCoRem ((∨→ s) ←∨) ltr
tranLFCoRem (∨→ (∨→ s)) (¬∨∨d ltr)         = tranLFCoRem (∨→ s) ltr
tranLFCoRem (∨→ (s ←∨→ s₁)) (¬∨∨d ltr)     = tranLFCoRem ((∨→ s) ←∨→ s₁) ltr
tranLFCoRem (s ←∨→ (↓ x)) (¬∨∨d ltr)     = tranLFCoRem ((s ←∨→ (↓ x)) ←∨→ (↓ x)) ltr
tranLFCoRem (s ←∨→ (s₁ ←∨)) (¬∨∨d ltr)     = tranLFCoRem ((s ←∨→ s₁) ←∨) ltr
tranLFCoRem (s ←∨→ (∨→ s₁)) (¬∨∨d ltr)     = tranLFCoRem ((s ←∨) ←∨→ s₁) ltr
tranLFCoRem (s ←∨→ (s₁ ←∨→ s₂)) (¬∨∨d ltr) = tranLFCoRem ((s ←∨→ s₁) ←∨→ s₂) ltr
tranLFCoRem ((s ←∂) ←∂) (∂∂d ltr)          = tranLFCoRem (s ←∂) ltr
tranLFCoRem (↓ x) (∂∂d ltr)          = ↓ x
tranLFCoRem ((↓ x) ←∂) (∂∂d ltr)          = tranLFCoRem ((↓ x) ←∂→ ((↓ x) ←∂)) ltr
tranLFCoRem ((∂→ s) ←∂) (∂∂d ltr)          = tranLFCoRem (∂→ (s ←∂)) ltr
tranLFCoRem ((s ←∂→ s₁) ←∂) (∂∂d ltr)      = tranLFCoRem (s ←∂→ (s₁ ←∂)) ltr
tranLFCoRem (∂→ s) (∂∂d ltr)               = tranLFCoRem (∂→ (∂→ s)) ltr
tranLFCoRem ((↓ x) ←∂→ s₁) (∂∂d ltr)      = tranLFCoRem ((↓ x) ←∂→ ((↓ x) ←∂→ s₁)) ltr
tranLFCoRem ((s ←∂) ←∂→ s₁) (∂∂d ltr)      = tranLFCoRem (s ←∂→ (∂→ s₁)) ltr
tranLFCoRem ((∂→ s) ←∂→ s₁) (∂∂d ltr)      = tranLFCoRem (∂→ (s ←∂→ s₁)) ltr
tranLFCoRem ((s ←∂→ s₁) ←∂→ s₂) (∂∂d ltr)  = tranLFCoRem (s ←∂→ (s₁ ←∂→ s₂)) ltr
tranLFCoRem (s ←∂) (¬∂∂d ltr)              = tranLFCoRem ((s ←∂) ←∂) ltr
tranLFCoRem (∂→ (s ←∂)) (¬∂∂d ltr)         = tranLFCoRem ((∂→ s) ←∂) ltr
tranLFCoRem (↓ x) (¬∂∂d ltr)         = ↓ x
tranLFCoRem (∂→ (↓ x)) (¬∂∂d ltr)         = tranLFCoRem ((∂→ (↓ x)) ←∂→ (↓ x)) ltr
tranLFCoRem (∂→ (∂→ s)) (¬∂∂d ltr)         = tranLFCoRem (∂→ s) ltr
tranLFCoRem (∂→ (s ←∂→ s₁)) (¬∂∂d ltr)     = tranLFCoRem ((∂→ s) ←∂→ s₁) ltr
tranLFCoRem (s ←∂→ (↓ x)) (¬∂∂d ltr)     = tranLFCoRem ((s ←∂→ (↓ x)) ←∂→ (↓ x)) ltr
tranLFCoRem (s ←∂→ (s₁ ←∂)) (¬∂∂d ltr)     = tranLFCoRem ((s ←∂→ s₁) ←∂) ltr
tranLFCoRem (s ←∂→ (∂→ s₁)) (¬∂∂d ltr)     = tranLFCoRem ((s ←∂) ←∂→ s₁) ltr
tranLFCoRem (s ←∂→ (s₁ ←∂→ s₂)) (¬∂∂d ltr) = tranLFCoRem ((s ←∂→ s₁) ←∂→ s₂) ltr


extendLFCoRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → IndexLL {i} {u} pll ll → SetLFCoRem {i} olf pll → SetLFCoRem olf ll
extendLFCoRem ↓ sr = sr
extendLFCoRem (ind ←∧) sr = (extendLFCoRem ind sr) ←∧
extendLFCoRem (∧→ ind) sr = ∧→ (extendLFCoRem ind sr)
extendLFCoRem (ind ←∨) sr = (extendLFCoRem ind sr) ←∨
extendLFCoRem (∨→ ind) sr = ∨→ (extendLFCoRem ind sr)
extendLFCoRem (ind ←∂) sr = (extendLFCoRem ind sr) ←∂
extendLFCoRem (∂→ ind) sr = ∂→ (extendLFCoRem ind sr)

replaceLFCoRem : ∀{i u oll orll ll pll rll} → {olf : LFun {i} {u} oll orll} → (ind : IndexLL {i} {u} pll ll) → SetLFCoRem {i} olf rll → SetLFCoRem olf ll → SetLFCoRem olf (replLL ll ind rll)
replaceLFCoRem ↓ esr sr = esr
replaceLFCoRem {rll = rll} (ind ←∧) esr (↓ x) = (extendLFCoRem (updInd rll ind) esr) ←∧
replaceLFCoRem {rll = rll} (ind ←∧) esr (sr ←∧) = replaceLFCoRem ind esr sr ←∧
replaceLFCoRem {rll = rll} (ind ←∧) esr (∧→ sr) = (extendLFCoRem (updInd rll ind) esr) ←∧→ sr
replaceLFCoRem {rll = rll} (ind ←∧) esr (sr ←∧→ sr₁) = (replaceLFCoRem ind esr sr) ←∧→ sr₁
replaceLFCoRem {rll = rll} (∧→ ind) esr (↓ x) = ∧→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∧→ ind) esr (sr ←∧) = sr ←∧→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∧→ ind) esr (∧→ sr) = ∧→ replaceLFCoRem ind esr sr
replaceLFCoRem {rll = rll} (∧→ ind) esr (sr ←∧→ sr₁) = sr ←∧→ replaceLFCoRem ind esr sr₁
replaceLFCoRem {rll = rll} (ind ←∨) esr (↓ x) = (extendLFCoRem (updInd rll ind) esr) ←∨
replaceLFCoRem {rll = rll} (ind ←∨) esr (sr ←∨) = replaceLFCoRem ind esr sr ←∨
replaceLFCoRem {rll = rll} (ind ←∨) esr (∨→ sr) = (extendLFCoRem (updInd rll ind) esr) ←∨→ sr
replaceLFCoRem {rll = rll} (ind ←∨) esr (sr ←∨→ sr₁) = (replaceLFCoRem ind esr sr) ←∨→ sr₁
replaceLFCoRem {rll = rll} (∨→ ind) esr (↓ x) = ∨→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∨→ ind) esr (sr ←∨) = sr ←∨→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∨→ ind) esr (∨→ sr) = ∨→ replaceLFCoRem ind esr sr
replaceLFCoRem {rll = rll} (∨→ ind) esr (sr ←∨→ sr₁) = sr ←∨→ replaceLFCoRem ind esr sr₁
replaceLFCoRem {rll = rll} (ind ←∂) esr (↓ x) = (extendLFCoRem (updInd rll ind) esr) ←∂
replaceLFCoRem {rll = rll} (ind ←∂) esr (sr ←∂) = replaceLFCoRem ind esr sr ←∂
replaceLFCoRem {rll = rll} (ind ←∂) esr (∂→ sr) = (extendLFCoRem (updInd rll ind) esr) ←∂→ sr
replaceLFCoRem {rll = rll} (ind ←∂) esr (sr ←∂→ sr₁) = (replaceLFCoRem ind esr sr) ←∂→ sr₁
replaceLFCoRem {rll = rll} (∂→ ind) esr (↓ x) = ∂→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∂→ ind) esr (sr ←∂) = sr ←∂→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∂→ ind) esr (∂→ sr) = ∂→ replaceLFCoRem ind esr sr
replaceLFCoRem {rll = rll} (∂→ ind) esr (sr ←∂→ sr₁) = sr ←∂→ replaceLFCoRem ind esr sr₁


mreplaceLFCoRem :  ∀{i u oll orll ll pll rll} → {olf : LFun {i} {u} oll orll} → (ind : IndexLL {i} {u} pll ll) → MSetLFCoRem {i} olf rll → MSetLFCoRem olf ll → MSetLFCoRem olf (replLL ll ind rll)
mreplaceLFCoRem ind ∅ ∅ = ∅
mreplaceLFCoRem {rll = rll} ind ∅ (¬∅ x) = delLFCoRem x ind rll
mreplaceLFCoRem {rll = rll} ind (¬∅ x) ∅ = ¬∅ (extendLFCoRem (updInd rll ind) x)
mreplaceLFCoRem ind (¬∅ x) (¬∅ x₁) = ¬∅ (replaceLFCoRem ind x x₁)
