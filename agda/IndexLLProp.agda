{-# OPTIONS --exact-split #-}
module IndexLLProp where

open import Common
open import LinLogic
open import Data.Maybe
open import Data.Product


data _≤ᵢ_ {i u gll fll} : ∀{ll} → IndexLL {i} {u} gll ll → IndexLL {i} {u} fll ll → Set where
  ≤ᵢ↓ : {ind : IndexLL fll gll} → ↓ ≤ᵢ ind
  ≤ᵢ←∧ : ∀{li ri} → {sind : IndexLL gll li} → {bind : IndexLL fll li} → (sind ≤ᵢ bind) → _≤ᵢ_ {ll = li ∧ ri} (sind ←∧) (bind ←∧)
  ≤ᵢ∧→ : ∀{li ri} → {sind : IndexLL gll ri} → {bind : IndexLL fll ri} → (sind ≤ᵢ bind) → _≤ᵢ_ {ll = li ∧ ri} (∧→ sind) (∧→ bind)
  ≤ᵢ←∨ : ∀{li ri} → {sind : IndexLL gll li} → {bind : IndexLL fll li} → (sind ≤ᵢ bind) → _≤ᵢ_ {ll = li ∨ ri} (sind ←∨) (bind ←∨)
  ≤ᵢ∨→ : ∀{li ri} → {sind : IndexLL gll ri} → {bind : IndexLL fll ri} → (sind ≤ᵢ bind) → _≤ᵢ_ {ll = li ∨ ri} (∨→ sind) (∨→ bind)
  ≤ᵢ←∂ : ∀{li ri} → {sind : IndexLL gll li} → {bind : IndexLL fll li} → (sind ≤ᵢ bind) → _≤ᵢ_ {ll = li ∂ ri} (sind ←∂) (bind ←∂)
  ≤ᵢ∂→ : ∀{li ri} → {sind : IndexLL gll ri} → {bind : IndexLL fll ri} → (sind ≤ᵢ bind) → _≤ᵢ_ {ll = li ∂ ri} (∂→ sind) (∂→ bind)







-- postulate
--  eqLL⇒↓ : ∀{i u ll} → (g : IndexLL {i} {u} ll ll) → g ≡ ↓ 

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
{-# CATCHALL #-}
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
{-# CATCHALL #-}
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
{-# CATCHALL #-}
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

+ᵢ⇒l≤ᵢ+ᵢ : ∀{i u pll cll ll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll) → ind ≤ᵢ (ind +ᵢ lind)
+ᵢ⇒l≤ᵢ+ᵢ ↓ lind = ≤ᵢ↓
+ᵢ⇒l≤ᵢ+ᵢ (ind ←∧) lind = ≤ᵢ←∧ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
+ᵢ⇒l≤ᵢ+ᵢ (∧→ ind) lind = ≤ᵢ∧→ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
+ᵢ⇒l≤ᵢ+ᵢ (ind ←∨) lind = ≤ᵢ←∨ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
+ᵢ⇒l≤ᵢ+ᵢ (∨→ ind) lind = ≤ᵢ∨→ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
+ᵢ⇒l≤ᵢ+ᵢ (ind ←∂) lind = ≤ᵢ←∂ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
+ᵢ⇒l≤ᵢ+ᵢ (∂→ ind) lind = ≤ᵢ∂→ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)


updIndGen : ∀{i u pll ll cll} → ∀ nrll → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll) → IndexLL {i} {u} (replLL pll lind nrll) (replLL ll (ind +ᵢ lind) nrll)
updIndGen nrll ↓ lind = ↓
updIndGen nrll (ind ←∧) lind = (updIndGen nrll ind lind) ←∧
updIndGen nrll (∧→ ind) lind = ∧→ (updIndGen nrll ind lind)
updIndGen nrll (ind ←∨) lind = (updIndGen nrll ind lind) ←∨
updIndGen nrll (∨→ ind) lind = ∨→ (updIndGen nrll ind lind)
updIndGen nrll (ind ←∂) lind = (updIndGen nrll ind lind) ←∂
updIndGen nrll (∂→ ind) lind = ∂→ (updIndGen nrll ind lind)


_-ₘᵢ_ : ∀ {i u pll cll ll} → IndexLL {i} {u} cll ll → IndexLL pll ll → Maybe $ IndexLL cll pll
a -ₘᵢ ↓ = just a
↓ -ₘᵢ (b ←∧) = nothing
(a ←∧) -ₘᵢ (b ←∧) = a -ₘᵢ b
(∧→ a) -ₘᵢ (b ←∧) = nothing
↓ -ₘᵢ (∧→ b) = nothing
(a ←∧) -ₘᵢ (∧→ b) = nothing
(∧→ a) -ₘᵢ (∧→ b) = a -ₘᵢ b
↓ -ₘᵢ (b ←∨) = nothing
(a ←∨) -ₘᵢ (b ←∨) = a -ₘᵢ b
(∨→ a) -ₘᵢ (b ←∨) = nothing
↓ -ₘᵢ (∨→ b) = nothing
(a ←∨) -ₘᵢ (∨→ b) = nothing
(∨→ a) -ₘᵢ (∨→ b) = a -ₘᵢ b
↓ -ₘᵢ (b ←∂) = nothing
(a ←∂) -ₘᵢ (b ←∂) = a -ₘᵢ b
(∂→ a) -ₘᵢ (b ←∂) = nothing
↓ -ₘᵢ (∂→ b) = nothing
(a ←∂) -ₘᵢ (∂→ b) = nothing
(∂→ a) -ₘᵢ (∂→ b) = a -ₘᵢ b

_-ᵢ_ : ∀ {i u pll cll ll} → (bind : IndexLL {i} {u} cll ll) → (sind : IndexLL pll ll) → (sind ≤ᵢ bind) → IndexLL cll pll
(bind -ᵢ .↓) ≤ᵢ↓ = bind
((bind ←∧) -ᵢ (sind ←∧)) (≤ᵢ←∧ eq) = (bind -ᵢ sind) eq
((∧→ bind) -ᵢ (∧→ sind)) (≤ᵢ∧→ eq) = (bind -ᵢ sind) eq
((bind ←∨) -ᵢ (sind ←∨)) (≤ᵢ←∨ eq) = (bind -ᵢ sind) eq
((∨→ bind) -ᵢ (∨→ sind)) (≤ᵢ∨→ eq) = (bind -ᵢ sind) eq
((bind ←∂) -ᵢ (sind ←∂)) (≤ᵢ←∂ eq) = (bind -ᵢ sind) eq
((∂→ bind) -ᵢ (∂→ sind)) (≤ᵢ∂→ eq) = (bind -ᵢ sind) eq


b-s≡j⇒s≤ᵢb : ∀ {i u pll cll ll} → (bind : IndexLL {i} {u} cll ll) → (sind : IndexLL pll ll) →  Σ (IndexLL {i} {u} cll pll) (λ x → (bind -ₘᵢ sind) ≡ just x) → sind ≤ᵢ bind
b-s≡j⇒s≤ᵢb bind ↓ (rs , x) = ≤ᵢ↓
b-s≡j⇒s≤ᵢb ↓ (sind ←∧) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∧) (sind ←∧) (rs , x) = ≤ᵢ←∧ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
b-s≡j⇒s≤ᵢb (∧→ bind) (sind ←∧) (rs , ())
b-s≡j⇒s≤ᵢb ↓ (∧→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∧) (∧→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (∧→ bind) (∧→ sind) (rs , x) = ≤ᵢ∧→ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
b-s≡j⇒s≤ᵢb ↓ (sind ←∨) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∨) (sind ←∨) (rs , x) = ≤ᵢ←∨ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
b-s≡j⇒s≤ᵢb (∨→ bind) (sind ←∨) (rs , ())
b-s≡j⇒s≤ᵢb ↓ (∨→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∨) (∨→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (∨→ bind) (∨→ sind) (rs , x) =  ≤ᵢ∨→ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
b-s≡j⇒s≤ᵢb ↓ (sind ←∂) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∂) (sind ←∂) (rs , x) = ≤ᵢ←∂ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
b-s≡j⇒s≤ᵢb (∂→ bind) (sind ←∂) (rs , ())
b-s≡j⇒s≤ᵢb ↓ (∂→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (bind ←∂) (∂→ sind) (rs , ())
b-s≡j⇒s≤ᵢb (∂→ bind) (∂→ sind) (rs , x) = ≤ᵢ∂→ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)


revUpdInd : ∀{i u ll cll ell pll} → (b : IndexLL pll ll) → (a : IndexLL {i} {u} cll (replLL ll b ell)) → a -ₘᵢ (updInd ell b) ≡ nothing → (updInd ell b) -ₘᵢ a ≡ nothing → IndexLL cll ll
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



updIndPart : ∀{i u ll cll ell pll} → (b : IndexLL pll ll) → (a : IndexLL {i} {u} cll ll) → a -ₘᵢ b ≡ nothing → b -ₘᵢ a ≡ nothing → IndexLL cll (replLL ll b ell)
updIndPart ↓ a () eq2
updIndPart (b ←∧) ↓ refl ()
updIndPart (b ←∧) (a ←∧) eq1 eq2 = updIndPart b a eq1 eq2 ←∧
updIndPart (b ←∧) (∧→ a) eq1 eq2 = ∧→ a
updIndPart (∧→ b) ↓ refl ()
updIndPart (∧→ b) (a ←∧) eq1 eq2 = a ←∧
updIndPart (∧→ b) (∧→ a) eq1 eq2 = ∧→ updIndPart b a eq1 eq2
updIndPart (b ←∨) ↓ refl ()
updIndPart (b ←∨) (a ←∨) eq1 eq2 = updIndPart b a eq1 eq2 ←∨
updIndPart (b ←∨) (∨→ a) eq1 eq2 = ∨→ a
updIndPart (∨→ b) ↓ refl ()
updIndPart (∨→ b) (a ←∨) eq1 eq2 = a ←∨
updIndPart (∨→ b) (∨→ a) eq1 eq2 = ∨→ updIndPart b a eq1 eq2
updIndPart (b ←∂) ↓ refl ()
updIndPart (b ←∂) (a ←∂) eq1 eq2 = updIndPart b a eq1 eq2 ←∂
updIndPart (b ←∂) (∂→ a) eq1 eq2 = ∂→ a
updIndPart (∂→ b) ↓ refl ()
updIndPart (∂→ b) (a ←∂) eq1 eq2 = a ←∂
updIndPart (∂→ b) (∂→ a) eq1 eq2 = ∂→ updIndPart b a eq1 eq2


rev⇒rs-i≡n : ∀{i u ll cll ell pll} → (ind : IndexLL pll ll) → (lind : IndexLL {i} {u} cll (replLL ll ind ell))
             → (eq₁ : (lind -ₘᵢ (updInd ell ind) ≡ nothing)) → (eq₂ : ((updInd ell ind) -ₘᵢ lind ≡ nothing))
             → let rs = revUpdInd ind lind eq₁ eq₂ in ((rs -ₘᵢ ind) ≡ nothing) × ((ind -ₘᵢ rs) ≡ nothing)
rev⇒rs-i≡n ↓ lind () eq2
rev⇒rs-i≡n (ind ←∧) ↓ eq1 ()
rev⇒rs-i≡n (ind ←∧) (lind ←∧) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
rev⇒rs-i≡n (ind ←∧) (∧→ lind) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∧→ ind) ↓ eq1 ()
rev⇒rs-i≡n (∧→ ind) (lind ←∧) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∧→ ind) (∧→ lind) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
rev⇒rs-i≡n (ind ←∨) ↓ eq1 ()
rev⇒rs-i≡n (ind ←∨) (lind ←∨) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
rev⇒rs-i≡n (ind ←∨) (∨→ lind) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∨→ ind) ↓ eq1 ()
rev⇒rs-i≡n (∨→ ind) (lind ←∨) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∨→ ind) (∨→ lind) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
rev⇒rs-i≡n (ind ←∂) ↓ eq1 ()
rev⇒rs-i≡n (ind ←∂) (lind ←∂) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
rev⇒rs-i≡n (ind ←∂) (∂→ lind) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∂→ ind) ↓ eq1 ()
rev⇒rs-i≡n (∂→ ind) (lind ←∂) eq1 eq2 = refl , refl
rev⇒rs-i≡n (∂→ ind) (∂→ lind) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2



drepl=>repl+ : ∀{i u pll ll cll frll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll) → (replLL ll ind (replLL pll lind frll)) ≡ replLL ll (ind +ᵢ lind) frll
drepl=>repl+ ↓ lind = refl
drepl=>repl+ {pll = pll} {ll = li ∧ ri} {frll = frll} (ind ←∧) lind with (replLL li ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∧ ri} {_} {frll} (ind ←∧) lind | .(replLL li (ind +ᵢ lind) frll) | refl = refl
drepl=>repl+ {pll = pll} {ll = li ∧ ri} {frll = frll} (∧→ ind) lind with (replLL ri ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∧ ri} {_} {frll} (∧→ ind) lind | .(replLL ri (ind +ᵢ lind) frll) | refl = refl
drepl=>repl+ {pll = pll} {ll = li ∨ ri} {frll = frll} (ind ←∨) lind with (replLL li ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∨ ri} {_} {frll} (ind ←∨) lind | .(replLL li (ind +ᵢ lind) frll) | refl = refl
drepl=>repl+ {pll = pll} {ll = li ∨ ri} {frll = frll} (∨→ ind) lind with (replLL ri ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∨ ri} {_} {frll} (∨→ ind) lind | .(replLL ri (ind +ᵢ lind) frll) | refl = refl
drepl=>repl+ {pll = pll} {ll = li ∂ ri} {frll = frll} (ind ←∂) lind with (replLL li ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∂ ri} {_} {frll} (ind ←∂) lind | .(replLL li (ind +ᵢ lind) frll) | refl = refl
drepl=>repl+ {pll = pll} {ll = li ∂ ri} {frll = frll} (∂→ ind) lind with (replLL ri ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
drepl=>repl+ {_} {_} {pll} {li ∂ ri} {_} {frll} (∂→ ind) lind | .(replLL ri (ind +ᵢ lind) frll) | refl = refl




remRepl : ∀{i u ll frll ell pll cll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll) → replLL (replLL ll (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell ≡ replLL ll ind ell
remRepl ↓ lind = refl
remRepl {ll = li ∧ ri} {frll = frll} {ell = ell} (ind ←∧) lind with (replLL (replLL li (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell) | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∧ ri} {frll} {ell} (ind ←∧) lind | .(replLL li ind ell) | refl = refl
remRepl {ll = li ∧ ri} {frll = frll} {ell = ell} (∧→ ind) lind with (replLL (replLL ri (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell) | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∧ ri} {frll} {ell} (∧→ ind) lind | .(replLL ri ind ell) | refl = refl
remRepl {ll = li ∨ ri} {frll = frll} {ell = ell} (ind ←∨) lind with (replLL (replLL li (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell) | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∨ ri} {frll} {ell} (ind ←∨) lind | .(replLL li ind ell) | refl = refl
remRepl {ll = li ∨ ri} {frll = frll} {ell = ell} (∨→ ind) lind with (replLL (replLL ri (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell) | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∨ ri} {frll} {ell} (∨→ ind) lind | .(replLL ri ind ell) | refl = refl
remRepl {ll = li ∂ ri} {frll = frll} {ell = ell} (ind ←∂) lind with (replLL (replLL li (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell) | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∂ ri} {frll} {ell} (ind ←∂) lind | .(replLL li ind ell) | refl = refl
remRepl {ll = li ∂ ri} {frll = frll} {ell = ell} (∂→ ind) lind with (replLL (replLL ri (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell) | (remRepl {frll = frll} {ell = ell} ind lind)
remRepl {_} {_} {li ∂ ri} {frll} {ell} (∂→ ind) lind | .(replLL ri ind ell) | refl = refl
