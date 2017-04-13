{-# OPTIONS --exact-split #-}
module LinLogicProp where

open import Common
open import LinLogic
open import IndexLLProp
import Data.Bool

data StructEqLL {i u} : LinLogic i {u} → LinLogic i {u} → Set (lsuc u) where
 ∅∅   : StructEqLL ∅ ∅
 ττ   : ∀{nx ny dtx dty x y} → StructEqLL (τ {i} {u} {nx} {dtx} x) (τ {i} {u} {ny} {dty} y)
 _∧∧_ : ∀{lix rix liy riy} → StructEqLL lix liy  → StructEqLL rix riy
        → StructEqLL (lix ∧ rix) (liy ∧ riy)
 _∨∨_ : ∀{lix rix liy riy} → StructEqLL lix liy  → StructEqLL rix riy
        → StructEqLL (lix ∨ rix) (liy ∨ riy)
 _∂∂_  : ∀{lix rix liy riy} → StructEqLL lix liy  → StructEqLL rix riy
        → StructEqLL (lix ∂ rix) (liy ∂ riy)
 cc   : ∀{∞llx ∞lly} → StructEqLL (call ∞llx) (call ∞lly)
 


isEqLL : ∀{i u} → (ll : LinLogic i {u}) → (oll : LinLogic i {u}) → Dec (StructEqLL ll oll)
isEqLL ∅ ∅ = yes ∅∅
isEqLL ∅ (τ x) = no (λ ())
isEqLL ∅ (oll ∧ oll₁) = no (λ ())
isEqLL ∅ (oll ∨ oll₁) = no (λ ())
isEqLL ∅ (oll ∂ oll₁) = no (λ ())
isEqLL ∅ (call x) = no (λ ())
isEqLL (τ x) ∅ = no (λ ())
isEqLL (τ x) (τ x₁) = yes ττ
isEqLL (τ x) (oll ∧ oll₁) = no (λ ())
isEqLL (τ x) (oll ∨ oll₁) = no (λ ())
isEqLL (τ x) (oll ∂ oll₁) = no (λ ())
isEqLL (τ x) (call x₁) = no (λ ())
isEqLL (ll ∧ ll₁) ∅ = no (λ ())
isEqLL (ll ∧ ll₁) (τ x) = no (λ ())
isEqLL (ll ∧ ll₁) (oll ∧ oll₁) with (isEqLL ll oll) | (isEqLL ll₁ oll₁)
isEqLL (ll ∧ ll₁) (oll ∧ oll₁) | yes p | (yes p₁) = yes (p ∧∧ p₁)
isEqLL (ll ∧ ll₁) (oll ∧ oll₁) | yes p | (no ¬p) = no (λ {(_ ∧∧ p₁) → ¬p p₁})
isEqLL (ll ∧ ll₁) (oll ∧ oll₁) | no ¬p | g = no (λ {(p ∧∧ _) → ¬p p})
isEqLL (ll ∧ ll₁) (oll ∨ oll₁) = no (λ ())
isEqLL (ll ∧ ll₁) (oll ∂ oll₁) = no (λ ())
isEqLL (ll ∧ ll₁) (call x) = no (λ ())
isEqLL (ll ∨ ll₁) ∅ = no (λ ())
isEqLL (ll ∨ ll₁) (τ x) = no (λ ())
isEqLL (ll ∨ ll₁) (oll ∧ oll₁) = no (λ ())
isEqLL (ll ∨ ll₁) (oll ∨ oll₁) with (isEqLL ll oll) | (isEqLL ll₁ oll₁)
isEqLL (ll ∨ ll₁) (oll ∨ oll₁) | yes p | (yes p₁) = yes (p ∨∨ p₁)
isEqLL (ll ∨ ll₁) (oll ∨ oll₁) | yes p | (no ¬p) = no (λ {(_ ∨∨ p₁) → ¬p p₁})
isEqLL (ll ∨ ll₁) (oll ∨ oll₁) | no ¬p | g = no (λ {(p ∨∨ _) → ¬p p})
isEqLL (ll ∨ ll₁) (oll ∂ oll₁) = no (λ ())
isEqLL (ll ∨ ll₁) (call x) = no (λ ())
isEqLL (ll ∂ ll₁) ∅ = no (λ ())
isEqLL (ll ∂ ll₁) (τ x) = no (λ ())
isEqLL (ll ∂ ll₁) (oll ∧ oll₁) = no (λ ())
isEqLL (ll ∂ ll₁) (oll ∨ oll₁) = no (λ ())
isEqLL (ll ∂ ll₁) (oll ∂ oll₁) with (isEqLL ll oll) | (isEqLL ll₁ oll₁)
isEqLL (ll ∂ ll₁) (oll ∂ oll₁) | yes p | (yes p₁) = yes (p ∂∂ p₁)
isEqLL (ll ∂ ll₁) (oll ∂ oll₁) | yes p | (no ¬p) = no (λ {(_ ∂∂ p₁) → ¬p p₁})
isEqLL (ll ∂ ll₁) (oll ∂ oll₁) | no ¬p | g = no (λ {(p ∂∂ _) → ¬p p})
isEqLL (ll ∂ ll₁) (call x) = no (λ ())
isEqLL (call x) ∅ = no (λ ())
isEqLL (call x) (τ x₁) = no (λ ())
isEqLL (call x) (oll ∧ oll₁) = no (λ ())
isEqLL (call x) (oll ∨ oll₁) = no (λ ())
isEqLL (call x) (oll ∂ oll₁) = no (λ ())
isEqLL (call x) (call x₁) = yes cc

-- TODO Maybe we need to use a catchall here?
replLL-id : ∀{i u q} → (ll : LinLogic i {u}) → (ind : IndexLL q ll) → (s : LinLogic i {u}) → q ≡ s → replLL ll ind s ≡ ll
replLL-id ll ↓ .ll refl = refl
replLL-id (li ∧ _) (ind ←∧) s prf with (replLL li ind s) | (replLL-id li ind s prf)
replLL-id (li ∧ _) (ind ←∧) s prf | .li | refl = refl
replLL-id (_ ∧ ri) (∧→ ind) s prf with (replLL ri ind s) | (replLL-id ri ind s prf)
replLL-id (_ ∧ ri) (∧→ ind) s prf | .ri | refl = refl
replLL-id (li ∨ _) (ind ←∨) s prf with (replLL li ind s) | (replLL-id li ind s prf)
replLL-id (li ∨ _) (ind ←∨) s prf | .li | refl = refl
replLL-id (_ ∨ ri) (∨→ ind) s prf with (replLL ri ind s) | (replLL-id ri ind s prf)
replLL-id (_ ∨ ri) (∨→ ind) s prf | .ri | refl = refl
replLL-id (li ∂ _) (ind ←∂) s prf with (replLL li ind s) | (replLL-id li ind s prf)
replLL-id (li ∂ _) (ind ←∂) s prf | .li | refl = refl
replLL-id (_ ∂ ri) (∂→ ind) s prf with (replLL ri ind s) | (replLL-id ri ind s prf)
replLL-id (_ ∂ ri) (∂→ ind) s prf | .ri | refl = refl


module _ where

  open import Data.Bool
  
  private
    noNilFinite : ∀{i u} → (ll : LinLogic i {u}) → Bool
    noNilFinite ∅ = false
    noNilFinite (τ x₁) = true
    noNilFinite (y LinLogic.∧ y₁) = noNilFinite y Data.Bool.∧ noNilFinite y₁
    noNilFinite (y LinLogic.∨ y₁) = noNilFinite y Data.Bool.∧ noNilFinite y₁
    noNilFinite (y ∂ y₁) = noNilFinite y Data.Bool.∧ noNilFinite y₁
    noNilFinite (call x₁) = false

  onlyOneNilOrNoNilFinite : ∀{i u} → (ll : LinLogic i {u}) → Bool
  onlyOneNilOrNoNilFinite ∅ = true
  onlyOneNilOrNoNilFinite (τ x) = noNilFinite (τ x)
  onlyOneNilOrNoNilFinite (x LinLogic.∧ x₁) = noNilFinite (x LinLogic.∧ x₁)
  onlyOneNilOrNoNilFinite (x LinLogic.∨ x₁) = noNilFinite (x LinLogic.∨ x₁)
  onlyOneNilOrNoNilFinite (x ∂ x₁) = noNilFinite (x ∂ x₁)
  onlyOneNilOrNoNilFinite (call x) = noNilFinite (call x)


-- We unfold all calls once. Used in LinFun.
unfold : ∀{i u} → {j : Size< i} → LinLogic i {u} → LinLogic j {u}
unfold ∅ = ∅
unfold (τ x) = τ x 
unfold (ll ∧ ll₁) = (unfold ll) ∧ (unfold ll₁)
unfold (ll ∨ ll₁) = (unfold ll) ∨ (unfold ll₁)
unfold (ll ∂ ll₁) = (unfold ll) ∂ (unfold ll₁)
unfold (call x) = step x

notOnlyCall : ∀{i u} → LinLogic i {u} → Data.Bool.Bool
notOnlyCall ∅ = Data.Bool.Bool.true
notOnlyCall (τ x) = Data.Bool.Bool.true
notOnlyCall (ll ∧ ll₁) = (notOnlyCall ll) Data.Bool.∨ (notOnlyCall ll₁)
notOnlyCall (ll ∨ ll₁) =  (notOnlyCall ll) Data.Bool.∨ (notOnlyCall ll₁)
notOnlyCall (ll ∂ ll₁) =  (notOnlyCall ll) Data.Bool.∨ (notOnlyCall ll₁)
notOnlyCall (call x) = Data.Bool.Bool.false



