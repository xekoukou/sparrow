{-# OPTIONS --exact-split #-}
-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS --show-irrelevant #-}

module LinFunContruct where

open import Common
open import LinLogic
open import IndexLLProp
open import LinFun
open import SetLL
open import SetLLProp

open import Relation.Binary.PropositionalEquality
open import Data.Product

shrink : ∀{i u} → ∀ ll → (s : SetLL {i} {u} ll) → ¬ ((contruct s) ≡ ↓) → LinLogic i {u}
shrink ll s eq with complLₛ s | ¬contruct↓⇒¬compl∅ s eq
shrink ll s eq | ∅ | e = ⊥-elim (e refl)
shrink ll s eq | ¬∅ x | e = shrink` ll x where
  shrink` : ∀{i u} → ∀ ll → SetLL {i} {u} ll → LinLogic i {u}
  shrink` ∅ ↓ = ∅
  shrink` (τ x) ↓ = τ x
  shrink` (li ∧ ri) ↓ = li ∧ ri
  shrink` (li ∧ ri) (s ←∧) = (shrink` li s)
  shrink` (li ∧ ri) (∧→ s) = (shrink` ri s)
  shrink` (li ∧ ri) (s ←∧→ s₁) = (shrink` li s) ∧ (shrink` ri s₁)
  shrink` (li ∨ ri) ↓ = li ∨ ri
  shrink` (li ∨ ri) (s ←∨) = (shrink` li s)
  shrink` (li ∨ ri) (∨→ s) = (shrink` ri s)
  shrink` (li ∨ ri) (s ←∨→ s₁) = (shrink` li s) ∨ (shrink` ri s₁)
  shrink` (li ∂ ri) ↓ = li ∂ ri
  shrink` (li ∂ ri) (s ←∂) = (shrink` li s)
  shrink` (li ∂ ri) (∂→ s) = (shrink` ri s)
  shrink` (li ∂ ri) (s ←∂→ s₁) = (shrink` li s) ∂ (shrink` ri s₁)
  shrink` (call x) ↓ = call x




tranLFMSetLL : ∀{i u ll rll} → (lf : LFun {i} {u} ll rll) → MSetLL ll → MSetLL rll
tranLFMSetLL lf ∅ = ∅
tranLFMSetLL I (¬∅ x) = ¬∅ x
tranLFMSetLL (_⊂_ {ind = ind} lf lf₁) (¬∅ x) = tranLFMSetLL lf₁ nmx where
  tlf = tranLFMSetLL lf (truncSetLL x ind)
  nmx = mreplacePartOf (¬∅ x) to tlf at ind
tranLFMSetLL (tr ltr lf) (¬∅ x) = tranLFMSetLL lf (¬∅ (SetLL.tran x ltr))
tranLFMSetLL (com df lf) (¬∅ x) = ∅
tranLFMSetLL (call x) (¬∅ x₁) = ∅


data MLFun {i u ll rll pll} (cll : LinLogic i {u}) (ind : IndexLL {i} {u} pll ll) (s : SetLL ll) (lf : LFun {i} {u} ll rll) : Set (lsuc u) where
  ∅ :  MLFun cll ind s lf
  ¬∅¬∅ : ∀{ts tsind ns nts} → ¬∅ ts ≡ (tranLFMSetLL lf (¬∅ s)) 
         → ¬∅ ns ≡ del s ind cll → (ieq : ¬ (contruct ns ≡ ↓)) → ¬∅ tsind ≡ tranLFMSetLL lf (¬∅ (subst (λ x → SetLL x) (replLL-id ll ind pll refl) (∅-add ind pll)))
         → let tind = proj₂ (pickOne tsind) in
         ¬∅ nts ≡ del ts tind cll → (req : ¬ (contruct nts ≡ ↓)) → LFun (shrink (replLL ll ind cll) ns ieq) (shrink (replLL rll tind cll) nts req) → MLFun cll ind s lf
  ¬∅∅ : ∀{ns} → (¬∅ ns ≡ del s ind cll) → (ieq : ¬ (contruct ns ≡ ↓)) → ∅ ≡ (tranLFMSetLL lf (¬∅ s)) → LFun (shrink (replLL ll ind cll) ns ieq) rll → MLFun cll ind s lf
  -- TODO Maybe change this : This is when ind is not inside the embedded LFun.



data MLFun¬ind {i u ll rll} (s : SetLL ll) (lf : LFun {i} {u} ll rll) : Set (lsuc u) where
  ¬∅¬∅ : ∀{ts} → ¬∅ ts ≡ (tranLFMSetLL lf (¬∅ s)) 
           → (ieq : ¬ (contruct s ≡ ↓))
           → (req : ¬ (contruct ts ≡ ↓)) → LFun (shrink ll s ieq) (shrink rll ts req) → MLFun¬ind s lf
  ¬∅∅ : (ieq : ¬ (contruct s ≡ ↓))
        → LFun (shrink ll s ieq) rll → MLFun¬ind s lf



module _ where
 
  
  trunc≡∅⇒¬mrpls≡∅ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → (truncSetLL s ind ≡ ∅) → ¬ (mreplacePartOf (¬∅ s) to (∅ {ll = fll}) at ind ≡ ∅)
  trunc≡∅⇒¬mrpls≡∅ s ↓ ()
  trunc≡∅⇒¬mrpls≡∅ ↓ (ind ←∧) ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (s ←∧) (ind ←∧) eq with del s ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind eq
  ... | ∅ | r = ⊥-elim (r refl)
  ... | ¬∅ x | r = λ ()
  trunc≡∅⇒¬mrpls≡∅ (∧→ s) (ind ←∧) eq = λ ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (s ←∧→ s₁) (ind ←∧) eq with del s ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind eq
  ... | ∅ | r = λ ()
  ... | ¬∅ x | r = λ ()
  trunc≡∅⇒¬mrpls≡∅ ↓ (∧→ ind) ()
  trunc≡∅⇒¬mrpls≡∅ (s ←∧) (∧→ ind) eq = λ ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (∧→ s) (∧→ ind) eq with del s ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind eq
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (s ←∧→ s₁) (∧→ ind) eq with del s₁ ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s₁ ind eq
  ... | ∅ | r = λ ()
  ... | ¬∅ x | r = λ ()
  trunc≡∅⇒¬mrpls≡∅ ↓ (ind ←∨) ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (s ←∨) (ind ←∨) eq with del s ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind eq
  ... | ∅ | r = ⊥-elim (r refl)
  ... | ¬∅ x | r = λ ()
  trunc≡∅⇒¬mrpls≡∅ (∨→ s) (ind ←∨) eq = λ ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (s ←∨→ s₁) (ind ←∨) eq with del s ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind eq
  ... | ∅ | r = λ ()
  ... | ¬∅ x | r = λ ()
  trunc≡∅⇒¬mrpls≡∅ ↓ (∨→ ind) ()
  trunc≡∅⇒¬mrpls≡∅ (s ←∨) (∨→ ind) eq = λ ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (∨→ s) (∨→ ind) eq with del s ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind eq
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (s ←∨→ s₁) (∨→ ind) eq with del s₁ ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s₁ ind eq
  ... | ∅ | r = λ ()
  ... | ¬∅ x | r = λ ()
  trunc≡∅⇒¬mrpls≡∅ ↓ (ind ←∂) ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (s ←∂) (ind ←∂) eq with del s ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind eq
  ... | ∅ | r = ⊥-elim (r refl)
  ... | ¬∅ x | r = λ ()
  trunc≡∅⇒¬mrpls≡∅ (∂→ s) (ind ←∂) eq = λ ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (s ←∂→ s₁) (ind ←∂) eq with del s ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind eq
  ... | ∅ | r = λ ()
  ... | ¬∅ x | r = λ ()
  trunc≡∅⇒¬mrpls≡∅ ↓ (∂→ ind) ()
  trunc≡∅⇒¬mrpls≡∅ (s ←∂) (∂→ ind) eq = λ ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (∂→ s) (∂→ ind) eq with del s ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind eq
  ... | ∅ | r = λ _ → r refl
  ... | ¬∅ x | r = λ ()
  trunc≡∅⇒¬mrpls≡∅ {fll = fll} (s ←∂→ s₁) (∂→ ind) eq with del s₁ ind fll | trunc≡∅⇒¬mrpls≡∅ {fll = fll} s₁ ind eq
  ... | ∅ | r = λ ()
  ... | ¬∅ x | r = λ ()





  ¬contr≡↓⇒¬contrdel≡↓ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → (ind : IndexLL rll ll) → ∀{x} → del s ind fll ≡ ¬∅ x → ¬ (contruct x ≡ ↓)
  ¬contr≡↓⇒¬contrdel≡↓ s eq ↓ ()
  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∧) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) deq with del s ind fll 
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) refl | ¬∅ di = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ (∧→ s) eq (ind ←∧) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) deq with del s ind fll | inspect (λ x → del s x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ∅ | [ eq1 ] = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∧ rs} {fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
    hf : ¬ (contruct s₁ ≡ ↓)
    hf x with contruct s₁
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∧→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
    hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
    hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
    hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
    hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
    hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∧→ s₁)) ≡ ↓)
    hf t eq x with contruct t | isEq (contruct t) ↓
    hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | g ←∧ | no ¬p
    hf t eq₁ () | ∧→ g | no ¬p
    hf t eq₁ () | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | g ←∨ | no ¬p 
    hf t eq₁ () | ∨→ g | no ¬p 
    hf t eq₁ () | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | g ←∂ | no ¬p 
    hf t eq₁ () | ∂→ g | no ¬p 
    hf t eq₁ () | g ←∂→ g₁ | no ¬p 
  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∧→ ind) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ (s ←∧) eq (∧→ ind) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) deq with del s ind fll
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) refl | ¬∅ x = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ∅ | r = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
    hf : ¬ (contruct s ≡ ↓)
    hf x with contruct s
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∧→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | isEq (contruct e) ↓
    hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
    hf2 t e eq₂ () | ce ←∧ | no ¬p
    hf2 t e eq₂ () | ∧→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∨ | no ¬p 
    hf2 t e eq₂ () | ∨→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∂ | no ¬p 
    hf2 t e eq₂ () | ∂→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∧→ t)) ≡ ↓)
    hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
    hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | ↓ | g ←∧ | no ¬p
    hf t eq₁ () | ↓ | ∧→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∨ | no ¬p 
    hf t eq₁ () | ↓ | ∨→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∂ | no ¬p 
    hf t eq₁ () | ↓ | ∂→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf t eq₁ () | r ←∧ | g | no ¬p 
    hf t eq₁ () | ∧→ r | g | no ¬p 
    hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∨ | g | no ¬p 
    hf t eq₁ () | ∨→ r | g | no ¬p 
    hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∂ | g | no ¬p 
    hf t eq₁ () | ∂→ r | g | no ¬p 
    hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∨) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) deq with del s ind fll 
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) refl | ¬∅ di = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ (∨→ s) eq (ind ←∨) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) deq with del s ind fll | inspect (λ x → del s x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ∅ | [ eq1 ] = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∨ rs} {fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
    hf : ¬ (contruct s₁ ≡ ↓)
    hf x with contruct s₁
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∨→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
    hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
    hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
    hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
    hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
    hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∨→ s₁)) ≡ ↓)
    hf t eq x with contruct t | isEq (contruct t) ↓
    hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | g ←∧ | no ¬p
    hf t eq₁ () | ∧→ g | no ¬p
    hf t eq₁ () | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | g ←∨ | no ¬p 
    hf t eq₁ () | ∨→ g | no ¬p 
    hf t eq₁ () | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | g ←∂ | no ¬p 
    hf t eq₁ () | ∂→ g | no ¬p 
    hf t eq₁ () | g ←∂→ g₁ | no ¬p 
  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∨→ ind) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ (s ←∨) eq (∨→ ind) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) deq with del s ind fll
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) refl | ¬∅ x = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ∅ | r = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
    hf : ¬ (contruct s ≡ ↓)
    hf x with contruct s
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∨→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | isEq (contruct e) ↓
    hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
    hf2 t e eq₂ () | ce ←∧ | no ¬p
    hf2 t e eq₂ () | ∧→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∨ | no ¬p 
    hf2 t e eq₂ () | ∨→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∂ | no ¬p 
    hf2 t e eq₂ () | ∂→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∨→ t)) ≡ ↓)
    hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
    hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | ↓ | g ←∧ | no ¬p
    hf t eq₁ () | ↓ | ∧→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∨ | no ¬p 
    hf t eq₁ () | ↓ | ∨→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∂ | no ¬p 
    hf t eq₁ () | ↓ | ∂→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf t eq₁ () | r ←∧ | g | no ¬p 
    hf t eq₁ () | ∧→ r | g | no ¬p 
    hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∨ | g | no ¬p 
    hf t eq₁ () | ∨→ r | g | no ¬p 
    hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∂ | g | no ¬p 
    hf t eq₁ () | ∂→ r | g | no ¬p 
    hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∂) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) deq with del s ind fll 
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) refl | ¬∅ di = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ (∂→ s) eq (ind ←∂) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) deq with del s ind fll | inspect (λ x → del s x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ∅ | [ eq1 ] = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∂ rs} {fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
    hf : ¬ (contruct s₁ ≡ ↓)
    hf x with contruct s₁
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∂→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
    hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
    hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
    hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
    hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
    hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
    hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
    hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
    hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∂→ s₁)) ≡ ↓)
    hf t eq x with contruct t | isEq (contruct t) ↓
    hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | g ←∧ | no ¬p
    hf t eq₁ () | ∧→ g | no ¬p
    hf t eq₁ () | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | g ←∨ | no ¬p 
    hf t eq₁ () | ∨→ g | no ¬p 
    hf t eq₁ () | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | g ←∂ | no ¬p 
    hf t eq₁ () | ∂→ g | no ¬p 
    hf t eq₁ () | g ←∂→ g₁ | no ¬p 
  ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∂→ ind) deq = ⊥-elim (eq refl)
  ¬contr≡↓⇒¬contrdel≡↓ (s ←∂) eq (∂→ ind) refl = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) deq with del s ind fll
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) () | ∅
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) refl | ¬∅ x = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ∅ | r = λ ()
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
  ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
    hf : ¬ (contruct s ≡ ↓)
    hf x with contruct s
    hf refl | .↓ = ⊥-elim (eq refl)

    hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∂→ t)) ≡ ↓)
    hf2 t e eq x with contruct e | isEq (contruct e) ↓
    hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
    hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
    hf2 t e eq₂ () | ce ←∧ | no ¬p
    hf2 t e eq₂ () | ∧→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∨ | no ¬p 
    hf2 t e eq₂ () | ∨→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
    hf2 t e eq₂ () | ce ←∂ | no ¬p 
    hf2 t e eq₂ () | ∂→ ce | no ¬p 
    hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

  ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
    is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
    hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∂→ t)) ≡ ↓)
    hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
    hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
    hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
    hf t eq₁ () | ↓ | g ←∧ | no ¬p
    hf t eq₁ () | ↓ | ∧→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∨ | no ¬p 
    hf t eq₁ () | ↓ | ∨→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
    hf t eq₁ () | ↓ | g ←∂ | no ¬p 
    hf t eq₁ () | ↓ | ∂→ g | no ¬p 
    hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
    hf t eq₁ () | r ←∧ | g | no ¬p 
    hf t eq₁ () | ∧→ r | g | no ¬p 
    hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∨ | g | no ¬p 
    hf t eq₁ () | ∨→ r | g | no ¬p 
    hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
    hf t eq₁ () | r ←∂ | g | no ¬p 
    hf t eq₁ () | ∂→ r | g | no ¬p 
    hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 


  ¬contr≡↓&trunc≡∅⇒¬contrdel≡↓ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → (ind : IndexLL rll ll) → (truncSetLL s ind ≡ ∅)
                                 → Σ (SetLL (replLL ll ind fll)) (λ x → (del s ind fll ≡ ¬∅ x) × (¬ (contruct x ≡ ↓)))
  ¬contr≡↓&trunc≡∅⇒¬contrdel≡↓ {fll = fll} s ceq ind treq with del s ind fll | inspect (λ x → del s x fll) ind
  ... | ∅ | [ eq ] = ⊥-elim (d eq) where
    d = trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind treq
  ... | ¬∅ x | [ eq ] = (x , refl , c) where
    c = ¬contr≡↓⇒¬contrdel≡↓ s ceq ind eq

  trunc≡∅-shrmorph : ∀{i u rll ll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → (ceq : ¬ ((contruct s) ≡ ↓)) → (truncSetLL s ind ≡ ∅) → IndexLL rll (shrink ll s ceq)
  trunc≡∅-shrmorph s ind ceq treq with complLₛ s | ¬contruct↓⇒¬compl∅ s ceq
  trunc≡∅-shrmorph s ind ceq treq | ∅ | r = ⊥-elim (r refl)
  trunc≡∅-shrmorph s ind ceq treq | ¬∅ x | r = trunc≡∅-shrmorph` x ind where
    trunc≡∅-shrmorph` : ∀{i u rll ll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → (truncSetLL s ind ≡ ∅) → IndexLL rll (shrink ll s ceq)
    trunc≡∅-shrmorph` {ll = ∅} s ind treq | ¬∅ ↓ | r = ind
    trunc≡∅-shrmorph` {ll = τ y} s ind treq | ¬∅ ↓ | r = ind
    trunc≡∅-shrmorph` {ll = ll ∧ rl} s ind treq | ¬∅ ↓ | r = ind
    trunc≡∅-shrmorph` {ll = ll ∧ rl} s ind treq | ¬∅ (x ←∧) | r = {!!}
    trunc≡∅-shrmorph` {ll = ll ∧ rl} s ind treq | ¬∅ (∧→ x) | r = {!!}
    trunc≡∅-shrmorph` {ll = ll ∧ rl} s ind treq | ¬∅ (x ←∧→ x₁) | r = {!!}
    trunc≡∅-shrmorph` {ll = ll ∨ rl} s ind treq | ¬∅ x | r = {!!}
    trunc≡∅-shrmorph` {ll = ll ∂ rl} s ind treq | ¬∅ x | r = {!!}
    trunc≡∅-shrmorph` {ll = call y} s ind treq | ¬∅ x | r = {!!}
  
  


  shrLF : ∀{i u rll ll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → (lf : LFun ll rll) → MLFun¬ind s lf
  shrLF s eq I = ¬∅¬∅ refl eq eq I
  shrLF {rll = rll} s eq (_⊂_ {ell = ell} {ind = ind} lf lf₁) with truncSetLL s ind | inspect (λ x → truncSetLL s x) ind
  ... | ¬∅ x | g = {!!}
  ... | ∅ | [ eq₁ ] with mrp | inspect mrpx ind where
    mrp = mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at ind
    mrpx = λ x → mreplacePartOf (¬∅ s) to (∅ {ll = ell}) at x
  ... | ∅ | [ eq₂ ] = ⊥-elim ((trunc≡∅⇒¬mrpls≡∅ s ind eq₁) eq₂)
  ... | ¬∅ x | [ eq₂ ] with shrLF x xc lf₁ where
    xc = ¬contr≡↓⇒¬contrdel≡↓ s eq ind eq₂
  ... | ¬∅¬∅ tseq ieq req slf₁ = ¬∅¬∅ {!!} eq {!!} (_⊂_ {ind = {!!}} lf slf₁) where
    ts = tranLFMSetLL (_⊂_ {ind = ind} lf lf₁) (¬∅ s)
    w = {!ts!}
  ... | ¬∅∅ ieq x₁ = {!!}
--     srlF = shrLF lf
--     srlF = shrLF (truncSetLL s ind ? ?) lf
  shrLF s eq (tr ltr lf) = {!!}
  shrLF s eq (com df lf) = {!!}
  shrLF s eq (call x) = {!!}

  -- s here does contain the ind.
test : ∀{i u rll ll n dt df} → (cll : LinLogic i {u}) → (ind : IndexLL {i} {u} (τ {i} {u} {n} {dt} df) ll) → (s : SetLL ll) → (lf : LFun ll rll) → MLFun cll ind s lf
test cll iind s I with mns | inspect mnsx cll where
  mns = del s iind cll
  mnsx = λ x → del s iind x
test cll iind s I | ∅ | nseq = ∅
test cll iind s I | ¬∅ x | [ eq ] with isEq (contruct x) ↓
test cll iind s I | ¬∅ x | [ eq ] | yes p = ∅
test {i} {u} {rll} {ll} {df = df} cll iind s I | ¬∅ ns | [ eqns ] | no ¬p = ¬∅¬∅ {ts = s} {tsind = tsind} refl (sym eqns) ¬p refl (proj₁ $ proj₂ hf) (proj₁ $ proj₂ $ proj₂ hf) (proj₂ $ proj₂ $ proj₂ hf)  where
  pll = τ df
  tsind = (subst (λ x → SetLL x) (replLL-id ll iind pll refl) (∅-add iind pll))
  tindf = (pickOne tsind)
  tind = proj₂ tindf
  hf : Σ (SetLL (replLL rll tind cll)) (λ nts
       → (¬∅ nts ≡ del s tind cll) × (Σ (¬ (contruct nts ≡ ↓)) (λ req →
           LFun (shrink (replLL ll iind cll) ns ¬p) (shrink (replLL rll tind cll) nts req))))
  hf with tindf | pickadd-id iind
  hf | .(_ , _) | refl = (ns , sym eqns , ¬p , I)
test {i} {u} {rll} {ll} {df = df} cll iind s (_⊂_ {ind = ind} lf lf₁) with isLTi ind iind 
... | yes le = {!!}
... | no ¬le with isLTi iind ind
... | yes ge = ⊥-elim (indτ⇒¬le iind ind ¬le ge) 
... | no ¬ge = {!!}
test cll iind s (tr ltr lf) = {!!}
test cll iind s (com df lf) = {!!}
test cll iind s (call x) = {!!}




---- s here does contain the ind.
--test : ∀{i u pll rll ll} → (cll : LinLogic i {u}) → (ind : IndexLL {i} {u} pll ll) → (s : SetLL ll) → (lf : LFun ll rll) → MLFun cll ind s lf
--test cll iind s I with mns | inspect mnsx cll where
--  mns = del s iind cll
--  mnsx = λ x → del s iind x
--test cll iind s I | ∅ | nseq = ∅
--test cll iind s I | ¬∅ x | [ eq ] with isEq (contruct x) ↓
--test cll iind s I | ¬∅ x | [ eq ] | yes p = ∅
--test cll iind s I | ¬∅ x | [ eq ] | no ¬p with mts | inspect mtsx s where
--  mts = tranLFMSetLL I (¬∅ s)
--  mtsx =  λ x → tranLFMSetLL I (¬∅ x)
--test cll iind s I | ¬∅ x | [ eq ] | no ¬p | ∅ | [ () ]
--test {pll = pll} {ll = ll} cll iind s I | ¬∅ x₁ | [ eq ] | no ¬p | ¬∅ x | [ eq₁ ] with mtsind | inspect mtsindx I  where
--  mtsind = tranLFMSetLL I (¬∅ (subst (λ x → SetLL x) (replLL-id ll iind pll refl) (∅-add iind pll)))
--  mtsindx = λ y → tranLFMSetLL y (¬∅ (subst (λ x → SetLL x) (replLL-id ll iind pll refl) (∅-add iind pll)))
--test cll iind s I | ¬∅ x₁ | [ eq ] | no ¬p | ¬∅ x | [ eq₁ ] | ∅ | g = ∅ where
--test cll iind s I | ¬∅ ns | [ eqns ] | no ¬p | ¬∅ ts | [ eqts ] | ¬∅ tsind | [ eqtsind ] with mnts | inspect mntsx cll where
--  tind = proj₂ (pickOne tsind)
--  mnts = del ts tind cll
--  mntsx = del ts tind
--  w = {!!}
--test cll iind s I | ¬∅ ns | [ eqns ] | no ¬p | ¬∅ ts | [ eqts ] | ¬∅ tsind | [ eqtsind ] | ∅ | g = ∅
--test cll iind s I | ¬∅ ns | [ eqns ] | no ¬p | ¬∅ ts | [ eqts ] | ¬∅ tsind | [ eqtsind ] | ¬∅ nts | [ eqnts ] with isEq (contruct nts) ↓
--test cll iind s I | ¬∅ ns | [ eqns ] | no ¬p | ¬∅ ts | [ eqts ] | ¬∅ tsind | [ eqtsind ] | ¬∅ nts | [ eqnts ] | yes cnts = ∅
--test {rll = rll} cll iind s I | ¬∅ ns | [ eqns ] | no ¬p | ¬∅ ts | [ eqts ] | ¬∅ tsind | [ eqtsind ] | ¬∅ nts | [ eqnts ] | no ¬cnts = {!!} where -- ¬∅¬∅ (sym eqts) (sym eqns) ¬p eqtsind (sym eqnts) ¬cnts {!!} where
--  tind = proj₂ (pickOne tsind)
--  g : LFun
--        (shrink (replLL rll iind cll) ns ¬p) 
--        (shrink (replLL rll tind cll) nts ¬cnts)
--  g = {!!}
--test cll iind s (lf ⊂ lf₁) = {!!}
--test cll iind s (tr ltr lf) = {!!}
--test cll iind s (com df lf) = {!!}
--test cll iind s (call x) = {!!}
--
