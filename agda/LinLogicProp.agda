{-# OPTIONS --exact-split #-}
module LinLogicProp where

open import Common
open import LinLogic
open import IndexLLProp
import Data.Bool


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


replLL-inv : ∀{i u ll ell pll} → (ind : IndexLL {i} {u} pll ll) → replLL (replLL ll ind ell) (updInd ell ind) pll ≡ ll
replLL-inv ↓ = refl
replLL-inv {ll = li ∧ ri} {ell = ell} {pll = pll} (ind ←∧) with (replLL (replLL li ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∧ ri} {ell} {pll} (ind ←∧) | .li | refl = refl
replLL-inv {ll = li ∧ ri} {ell = ell} {pll = pll} (∧→ ind) with (replLL (replLL ri ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∧ ri} {ell} {pll} (∧→ ind) | .ri | refl = refl
replLL-inv {ll = li ∨ ri} {ell = ell} {pll = pll} (ind ←∨) with (replLL (replLL li ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∨ ri} {ell} {pll} (ind ←∨) | .li | refl = refl
replLL-inv {ll = li ∨ ri} {ell = ell} {pll = pll} (∨→ ind) with (replLL (replLL ri ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∨ ri} {ell} {pll} (∨→ ind) | .ri | refl = refl
replLL-inv {ll = li ∂ ri} {ell = ell} {pll = pll} (ind ←∂) with (replLL (replLL li ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∂ ri} {ell} {pll} (ind ←∂) | .li | refl = refl
replLL-inv {ll = li ∂ ri} {ell = ell} {pll = pll} (∂→ ind) with (replLL (replLL ri ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
replLL-inv {_} {_} {li ∂ ri} {ell} {pll} (∂→ ind) | .ri | refl = refl

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



