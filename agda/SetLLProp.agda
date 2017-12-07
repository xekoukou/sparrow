module SetLLProp where

open import Common
open import LinLogic
open import SetLL
open import IndexLLProp

open import Relation.Binary.PropositionalEquality
import Data.Product


compl-tr-com-abs : ∀ {i u} {rll : LinLogic i {u}} (w : MSetLL rll) →
                   w ≡ (w >>=ₛ ¬∅)
compl-tr-com-abs ∅ = refl
compl-tr-com-abs (¬∅ x) = refl


compl-tr-com-abs3 : ∀ {ds d} →
                    ds ≡ ~ict d →
                    ∀ (w : DecICT (~ict ds) d) {i u} {l r rll : LinLogic i {u}}
                      {ind : IndexLL rll (pickLL d l r)} →
                    ¬∅ fillAllLower ≡ truncₛ-abs fillAllLower ind w
compl-tr-com-abs3 x (yes refl) {ind = ind} = sym (tr-fAL ind)
compl-tr-com-abs3 refl (no p) = ⊥-elim (~ict-eq⇒¬ (sym p))

compl-tr-com-abs2 : ∀ {ds d i u} {l : LinLogic i} {il}
                      {r rll : LinLogic i {u}} {ind : IndexLL rll (pickLL d l r)} →
                    ds ≡ ~ict d →
                    (w : MSetLL (pickLL ds l r)) →
                    ¬∅ fillAllLower ≡ (complLₛ-abs {il = il} {ds} w >>=ₛ (λ z → truncₛ z (ic d ind)))
compl-tr-com-abs2 {ds} {d} x ∅ = compl-tr-com-abs3 x (isEqICT (~ict ds) d) 
compl-tr-com-abs2 {d = ic←} {ind = ind} refl (¬∅ cs) = sym (tr-fAL ind)
compl-tr-com-abs2 {d = ic→} {ind = ind} refl (¬∅ cs) = sym (tr-fAL ind)

mutual

  compl-tr-com-abs6 : ∀ {i u} {l : LinLogic i {u}} {il}
                      {r rll : LinLogic i} {s : SetLL l} {s₁ : SetLL r} {d}
                      {ind : IndexLL rll (pickLL d l r)} (w : MSetLL l) ( eq : w ≡ complLₛ s) (w₁ : MSetLL r) (eq1 : w₁ ≡ complLₛ s₁) →
                    mcomplLₛ (truncₛ (sbc {il = il} s s₁) (ic d ind)) ≡
                    (sbcm {il = il} w w₁ >>=ₛ (λ z → truncₛ z (ic d ind)))
  compl-tr-com-abs6 {s = s} {d = ic←} {ind} ∅ eq ∅ eq1 = trans (compl-tr-com s ind) (cong (λ k → k >>=ₛ (λ z → truncₛ z ind)) (sym eq))
  compl-tr-com-abs6 {s₁ = s₁} {d = ic→} {ind = ind} ∅ eq ∅ eq1 = trans (compl-tr-com s₁ ind) (cong (λ k → k >>=ₛ (λ z → truncₛ z ind)) (sym eq1))
  compl-tr-com-abs6 {s = s} {d = ic←} {ind} ∅ eq (¬∅ x) eq1 = trans (compl-tr-com s ind) (cong (λ k → k >>=ₛ (λ z → truncₛ z ind)) (sym eq))
  compl-tr-com-abs6 {s₁ = s₁} {d = ic→} {ind = ind} ∅ eq (¬∅ x) eq1 = trans (compl-tr-com s₁ ind) (cong (λ k → k >>=ₛ (λ z → truncₛ z ind)) (sym eq1))
  compl-tr-com-abs6 {s = s} {d = ic←} {ind} (¬∅ x) eq ∅ eq1 = trans (compl-tr-com s ind) (cong (λ k → k >>=ₛ (λ z → truncₛ z ind)) (sym eq))
  compl-tr-com-abs6 {s₁ = s₁} {d = ic→} {ind = ind} (¬∅ x) eq ∅ eq1 = trans (compl-tr-com s₁ ind) (cong (λ k → k >>=ₛ (λ z → truncₛ z ind)) (sym eq1))
  compl-tr-com-abs6 {s = s} {d = ic←} {ind} (¬∅ x) eq (¬∅ x₁) eq1 = trans (compl-tr-com s ind) (cong (λ k → k >>=ₛ (λ z → truncₛ z ind)) (sym eq))
  compl-tr-com-abs6 {s₁ = s₁} {d = ic→} {ind = ind} (¬∅ x) eq (¬∅ x₁) eq1 = trans (compl-tr-com s₁ ind) (cong (λ k → k >>=ₛ (λ z → truncₛ z ind)) (sym eq1))

  compl-tr-com-abs5 : ∀ {ds i u} {l r rll : LinLogic i {u}}
                        {s : SetLL (pickLL ds l r)} →
                      ∅ ≡ complLₛ s →
                      (w : DecICT (~ict ds) ds) {ind : IndexLL rll (pickLL ds l r)} →
                      mcomplLₛ (truncₛ s ind) ≡ truncₛ-abs fillAllLower ind w
  compl-tr-com-abs5 eq (yes x) = ⊥-elim (~ict-eq⇒¬ (sym x))
  compl-tr-com-abs5 {s = s} eq (no x) {ind = ind} = trans (compl-tr-com s ind) (cong (λ k → k >>=ₛ (λ z → truncₛ z ind)) (sym eq))
  
  compl-tr-com-abs4 : ∀ {ds i u} {l : LinLogic i {u}} {il}
                        {r rll : LinLogic i} {s : SetLL (pickLL ds l r)}
                        {ind : IndexLL rll (pickLL ds l r)} (w : MSetLL (pickLL ds l r)) → (w ≡ complLₛ s) →
                      mcomplLₛ (truncₛ s ind) ≡
                      (complLₛ-abs {il = il} {ds} w >>=ₛ (λ z → truncₛ z (ic ds ind)))
  compl-tr-com-abs4 {ds} ∅ eq = compl-tr-com-abs5 eq (isEqICT (~ict ds) ds)  
  compl-tr-com-abs4 {ic←} {s = s} {ind = ind} (¬∅ x) eq = trans (compl-tr-com s ind) (cong (λ k → k >>=ₛ (λ z → truncₛ z ind)) (sym eq))
  compl-tr-com-abs4 {ic→} {s = s} {ind = ind} (¬∅ x) eq = trans (compl-tr-com s ind) (cong (λ k → k >>=ₛ (λ z → truncₛ z ind)) (sym eq))


  compl-tr-com-abs1 : ∀ {ds d} (w : DecICT ds d) {i u}
                      {l : LinLogic i {u}} {il} {r rll : LinLogic i}
                      {s : SetLL (pickLL ds l r)} {ind : IndexLL rll (pickLL d l r)} →
                    mcomplLₛ (truncₛ-abs s ind w) ≡
                    (complLₛ-abs {il = il} {ds} (complLₛ s) >>=ₛ (λ z → truncₛ z (ic d ind)))
  compl-tr-com-abs1 {ds} (yes refl) {s = s} =  compl-tr-com-abs4 {ds = ds} (complLₛ s) refl
  compl-tr-com-abs1 (no x) {s = s} = compl-tr-com-abs2 x (complLₛ s)

  compl-tr-com : ∀{i u rll ll} → (s : SetLL {i} {u} ll) 
                      → (ind : IndexLL rll ll)
                      → mcomplLₛ (truncₛ s ind) ≡ (complLₛ s >>=ₛ (λ z → truncₛ z ind))
  compl-tr-com s ↓ = compl-tr-com-abs (complLₛ s)
  compl-tr-com ↓ (ic d ind) = refl
  compl-tr-com (sic ds s) (ic d ind) =  compl-tr-com-abs1 (isEqICT ds d) 
  compl-tr-com (sbc s s₁) (ic d ind) = compl-tr-com-abs6 (complLₛ s) refl (complLₛ s₁) refl                





mutual

  trunc≡¬∅⇒ho-abs : ∀ {i u} {l : LinLogic i {u}} {il}
                    {r rll : LinLogic i} {trs : SetLL rll} {ds}
                    {s : SetLL (pickLL ds l r)} {d} {ind : IndexLL rll (pickLL d l r)}
                    (w : DecICT ds d) →
                  truncₛ-abs s ind w ≡ ¬∅ trs → hitsAtLeastOnce (sic {il = il} ds s) (ic d ind)
  trunc≡¬∅⇒ho-abs (yes refl) eq = hLOsic {{ieq = trunc≡¬∅⇒ho eq}}
  trunc≡¬∅⇒ho-abs (no x) ()
  
  trunc≡¬∅⇒ho : ∀{i u rll ll trs} → {s : SetLL {i} {u} ll} → {ind : IndexLL rll ll} → (truncₛ s ind ≡ ¬∅ trs) → hitsAtLeastOnce s ind
  trunc≡¬∅⇒ho {s = s} {↓} eq = hLOs↓
  trunc≡¬∅⇒ho {s = ↓} {ic d ind} eq = hLO↓ic
  trunc≡¬∅⇒ho {s = sic ds s} {ic d ind} eq = trunc≡¬∅⇒ho-abs (isEqICT ds d) eq
  trunc≡¬∅⇒ho {s = sbc s s₁} {ic d ind} eq = hLOsbc {{ieq = trunc≡¬∅⇒ho eq}}


module _ where

  open Data.Product

  ho⇒trunc≡¬∅-abs : ∀ {i u} {l r : LinLogic i {u}} {ds}
                    {s : SetLL (pickLL ds l r)} {rll : LinLogic i}
                    (ind : IndexLL rll (pickLL ds l r)) (w : DecICT ds ds) →
                   Σ (SetLL rll) (λ trs → truncₛ s ind ≡ ¬∅ trs) →
                  Σ (SetLL rll) (λ trs → truncₛ-abs s ind w ≡ ¬∅ trs)
  ho⇒trunc≡¬∅-abs {ds = ds} ind (yes refl) is = is
  ho⇒trunc≡¬∅-abs {ds = ds} ind (no x) is = ⊥-elim (~ict-eq⇒¬ x)


  ho⇒trunc≡¬∅ : ∀{i u rll ll} → {s : SetLL {i} {u} ll} → (ind : IndexLL rll ll) → {{eq : hitsAtLeastOnce s ind}} → Σ (SetLL rll) (λ trs → truncₛ s ind ≡ ¬∅ trs)
  ho⇒trunc≡¬∅ {s = s} ↓ {{eq}} = s , refl
  ho⇒trunc≡¬∅ {s = ↓} (ic d ind) {{eq}} = ↓ , refl
  ho⇒trunc≡¬∅ {s = sic ds s} (ic .ds ind) {{hLOsic}} = ho⇒trunc≡¬∅-abs ind (isEqICT ds ds) (ho⇒trunc≡¬∅ ind)
  ho⇒trunc≡¬∅ {s = sbc s s₁} (ic d ind) {{hLOsbc}} = ho⇒trunc≡¬∅ ind 



-- This is equal if we first contruct them.
--  tr-repl⇒id2 : ∀{i u ll pll} → {s : SetLL ll} → (ind : IndexLL {i} {u} pll ll)
--             → mreplacePartOf (¬∅ s) to (truncₛ s ind) at ind ≡ ¬∅ s


compl-ext⇒id : ∀ {i u} {ll rll : LinLogic i {u}} {s : SetLL rll} (ind : IndexLL rll ll)
                 → mapₛ (s-extend ind) (complLₛ s) ≡ complLₛ (s-extend ind s)
compl-ext⇒id {s = s} ↓ = mapₛ-id (complLₛ s)
compl-ext⇒id {s = s} (ic d ind) = {!!}

mutual

  compl-repl⇒id-abs : ∀ {i u} {ll rll : LinLogic i {u}} {s : SetLL ll}
                  {vs : SetLL rll} (ind : IndexLL rll ll) (w : MSetLL ll) (eq : w ≡ complLₛ s)
                  (w₁ : MSetLL rll) (eq₁ : w₁ ≡ complLₛ vs) → (w₂ : MSetLL ll) → (eq₂ : w₂ ≡ del s ind) →
                (mreplacePartOf w to w₁ at ind) ≡
                complLₛ (replacePartOf-abs {b = vs} ind w₂)
  compl-repl⇒id-abs ind ∅ eq _ refl ∅ eq2 = compl-ext⇒id ind
  compl-repl⇒id-abs ind ∅ eq w1 eq1 (¬∅ x) eq2 = {!!}
  compl-repl⇒id-abs ind (¬∅ x) eq w1 eq1 w2 eq2 = {!!}

  compl-repl⇒id : ∀{i u ll rll} → {s : SetLL ll} → {vs : SetLL {i} rll} → (ind : IndexLL {i} {u} rll ll)
                       → mreplacePartOf (complLₛ s) to (complLₛ vs) at ind ≡ complLₛ (replacePartOf s to vs at ind) 
  compl-repl⇒id {s = s} {vs} ind = compl-repl⇒id-abs ind (complLₛ s) refl (complLₛ vs) refl (del s ind) refl


-- module _ where

--   open import Data.Product

--   compl≡¬∅⇒replace-compl≡¬∅ : ∀{i u ll ell pll x trs} → (s : SetLL ll) → (lind : IndexLL {i} {u} pll ll)
--           → (eq : complLₛ s ≡ ¬∅ x)
--           → (teq : truncSetLL s lind ≡ ¬∅ trs)
--           → complLₛ trs ≡ ∅
--           → (vs : SetLL ell) 
--           → let mx = replacePartOf s to vs at lind in
--           Σ (SetLL (replLL ll lind ell)) (λ cs → complLₛ mx ≡ ¬∅ cs)
--   compl≡¬∅⇒replace-compl≡¬∅ s ↓ eq refl ceq vs with complLₛ s
--   compl≡¬∅⇒replace-compl≡¬∅ s ↓ () refl refl vs | .∅
--   compl≡¬∅⇒replace-compl≡¬∅ ↓ (lind ←∧) () teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) eq teq ceq vs with complLₛ mx where
--     mx = replacePartOf s to vs at lind 
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) eq teq ceq vs | ∅ = (∧→ fillAllLower rll) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) eq teq ceq vs | ¬∅ x = (x ←∧→ fillAllLower rll) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (∧→ s) (lind ←∧) eq () ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs with complLₛ s₁
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ∅ with complLₛ s | inspect complLₛ s 
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) () teq ceq vs | ∅ | ∅ | [ e ]
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
--     is = compl≡¬∅⇒replace-compl≡¬∅ s lind e teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (x ←∧) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ¬∅ x with complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ¬∅ x | ∅ = (∧→ x) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x ←∧→ x₁) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ ↓ (∧→ lind) () teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧) (∧→ lind) eq () ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rrl} (∧→ s) (∧→ lind) eq teq ceq vs with complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rrl} (∧→ s) (∧→ lind) eq teq ceq vs | ∅ = (fillAllLower lll ←∧) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rrl} (∧→ s) (∧→ lind) eq teq ceq vs | ¬∅ x = (fillAllLower lll ←∧→ x) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs with complLₛ s
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ∅ with complLₛ s₁ | inspect complLₛ s₁
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) () teq ceq vs | ∅ | ∅ | e
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
--     is = compl≡¬∅⇒replace-compl≡¬∅ s₁ lind e teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
--     mx = replacePartOf s₁ to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (∧→ x) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ¬∅ x with complLₛ mx where
--     mx = replacePartOf s₁ to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ¬∅ x | ∅ = (x ←∧) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x₁ ←∧→ x) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ ↓ (lind ←∨) () teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) eq teq ceq vs with complLₛ mx where
--     mx = replacePartOf s to vs at lind 
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) eq teq ceq vs | ∅ = (∨→ fillAllLower rll) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) eq teq ceq vs | ¬∅ x = (x ←∨→ fillAllLower rll) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (∨→ s) (lind ←∨) eq () ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs with complLₛ s₁
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ∅ with complLₛ s | inspect complLₛ s 
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) () teq ceq vs | ∅ | ∅ | [ e ]
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
--     is = compl≡¬∅⇒replace-compl≡¬∅ s lind e teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (x ←∨) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ¬∅ x with complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ¬∅ x | ∅ = (∨→ x) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x ←∨→ x₁) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ ↓ (∨→ lind) () teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨) (∨→ lind) eq () ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rrl} (∨→ s) (∨→ lind) eq teq ceq vs with complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rrl} (∨→ s) (∨→ lind) eq teq ceq vs | ∅ = (fillAllLower lll ←∨) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rrl} (∨→ s) (∨→ lind) eq teq ceq vs | ¬∅ x = (fillAllLower lll ←∨→ x) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs with complLₛ s
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ∅ with complLₛ s₁ | inspect complLₛ s₁
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) () teq ceq vs | ∅ | ∅ | e
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
--     is = compl≡¬∅⇒replace-compl≡¬∅ s₁ lind e teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
--     mx = replacePartOf s₁ to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (∨→ x) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ¬∅ x with complLₛ mx where
--     mx = replacePartOf s₁ to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ¬∅ x | ∅ = (x ←∨) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x₁ ←∨→ x) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ ↓ (lind ←∂) () teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) eq teq ceq vs with complLₛ mx where
--     mx = replacePartOf s to vs at lind 
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) eq teq ceq vs | ∅ = (∂→ fillAllLower rll) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) eq teq ceq vs | ¬∅ x = (x ←∂→ fillAllLower rll) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (∂→ s) (lind ←∂) eq () ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs with complLₛ s₁
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ∅ with complLₛ s | inspect complLₛ s 
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) () teq ceq vs | ∅ | ∅ | [ e ]
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
--     is = compl≡¬∅⇒replace-compl≡¬∅ s lind e teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (x ←∂) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ¬∅ x with complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ¬∅ x | ∅ = (∂→ x) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x ←∂→ x₁) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ ↓ (∂→ lind) () teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂) (∂→ lind) eq () ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rrl} (∂→ s) (∂→ lind) eq teq ceq vs with complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rrl} (∂→ s) (∂→ lind) eq teq ceq vs | ∅ = (fillAllLower lll ←∂) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rrl} (∂→ s) (∂→ lind) eq teq ceq vs | ¬∅ x = (fillAllLower lll ←∂→ x) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs with complLₛ s
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ∅ with complLₛ s₁ | inspect complLₛ s₁
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) () teq ceq vs | ∅ | ∅ | e
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
--     is = compl≡¬∅⇒replace-compl≡¬∅ s₁ lind e teq ceq vs
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
--     mx = replacePartOf s₁ to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (∂→ x) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ¬∅ x with complLₛ mx where
--     mx = replacePartOf s₁ to vs at lind
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ¬∅ x | ∅ = (x ←∂) , refl
--   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x₁ ←∂→ x) , refl
  
  
    
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ : ∀{i u ll ell pll} → (s : SetLL ll) → (lind : IndexLL {i} {u} pll ll)
--           → (vs : SetLL ell) 
--           → complLₛ vs ≡ ∅
--           → let mx = replacePartOf s to vs at lind in
--           ∀{cs} → 
--           (cmeq : complLₛ mx ≡ ¬∅ cs) →
--           Σ (SetLL ll) (λ x → complLₛ s ≡ ¬∅ x)
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s ↓ vs cv cmeq with complLₛ vs
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s ↓ vs refl () | .∅
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∧) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf ↓ to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∧) vs cv () | ∅ | [ e ]
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∧) vs cv cmeq | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∧) vs cv cmeq | ¬∅ x | [ e ] | proj3 , ()
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) vs cv cmeq  with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) vs cv cmeq | ∅ = (∧→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) vs cv cmeq | ¬∅ x = (x ←∧→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (∧→ s) (lind ←∧) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∧ rll} (∧→ s) (lind ←∧) vs cv cmeq | ∅ = (fillAllLower lll ←∧) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∧ rll} (∧→ s) (lind ←∧) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∧→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq with complLₛ s₁
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv () | ∅ | ∅ | e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (x ←∧) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ¬∅ x with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ¬∅ x | ∅ = (∧→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x ←∧→ x₁) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∧→ lind) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf ↓ to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∧→ lind) vs cv () | ∅ | e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∧→ lind) vs cv cmeq | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∧→ lind) vs cv cmeq | ¬∅ x | [ e ] | proj₃ , ()
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (∧→ lind) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (∧→ lind) vs cv cmeq | ∅ = (∧→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (∧→ lind) vs cv cmeq | ¬∅ x = (x ←∧→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (∧→ s) (∧→ lind) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∧ rll} (∧→ s) (∧→ lind) vs cv cmeq | ∅ = (fillAllLower lll ←∧) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∧ rll} (∧→ s) (∧→ lind) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∧→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf s₁ to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv () | ∅ | ∅ | e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s₁ lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s₁
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (∧→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ¬∅ x with complLₛ s₁
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ¬∅ x | ∅ = (x ←∧) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x₁ ←∧→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∨) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf ↓ to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∨) vs cv () | ∅ | [ e ]
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∨) vs cv cmeq | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∨) vs cv cmeq | ¬∅ x | [ e ] | proj3 , ()
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) vs cv cmeq  with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) vs cv cmeq | ∅ = (∨→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) vs cv cmeq | ¬∅ x = (x ←∨→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (∨→ s) (lind ←∨) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∨ rll} (∨→ s) (lind ←∨) vs cv cmeq | ∅ = (fillAllLower lll ←∨) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∨ rll} (∨→ s) (lind ←∨) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∨→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq with complLₛ s₁
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv () | ∅ | ∅ | e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (x ←∨) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ¬∅ x with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ¬∅ x | ∅ = (∨→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x ←∨→ x₁) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∨→ lind) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf ↓ to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∨→ lind) vs cv () | ∅ | e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∨→ lind) vs cv cmeq | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∨→ lind) vs cv cmeq | ¬∅ x | [ e ] | proj₃ , ()
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (∨→ lind) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (∨→ lind) vs cv cmeq | ∅ = (∨→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (∨→ lind) vs cv cmeq | ¬∅ x = (x ←∨→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (∨→ s) (∨→ lind) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∨ rll} (∨→ s) (∨→ lind) vs cv cmeq | ∅ = (fillAllLower lll ←∨) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∨ rll} (∨→ s) (∨→ lind) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∨→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf s₁ to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv () | ∅ | ∅ | e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s₁ lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s₁
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (∨→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ¬∅ x with complLₛ s₁
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ¬∅ x | ∅ = (x ←∨) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x₁ ←∨→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∂) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf ↓ to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∂) vs cv () | ∅ | [ e ]
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∂) vs cv cmeq | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∂) vs cv cmeq | ¬∅ x | [ e ] | proj3 , ()
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) vs cv cmeq  with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) vs cv cmeq | ∅ = (∂→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) vs cv cmeq | ¬∅ x = (x ←∂→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (∂→ s) (lind ←∂) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∂ rll} (∂→ s) (lind ←∂) vs cv cmeq | ∅ = (fillAllLower lll ←∂) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∂ rll} (∂→ s) (lind ←∂) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∂→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq with complLₛ s₁
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf s to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv () | ∅ | ∅ | e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (x ←∂) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ¬∅ x with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ¬∅ x | ∅ = (∂→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x ←∂→ x₁) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∂→ lind) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf ↓ to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∂→ lind) vs cv () | ∅ | e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∂→ lind) vs cv cmeq | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∂→ lind) vs cv cmeq | ¬∅ x | [ e ] | proj₃ , ()
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (∂→ lind) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (∂→ lind) vs cv cmeq | ∅ = (∂→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (∂→ lind) vs cv cmeq | ¬∅ x = (x ←∂→ fillAllLower rll) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (∂→ s) (∂→ lind) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∂ rll} (∂→ s) (∂→ lind) vs cv cmeq | ∅ = (fillAllLower lll ←∂) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∂ rll} (∂→ s) (∂→ lind) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∂→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq with complLₛ s
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
--     mx = replacePartOf s₁ to vs at lind
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv () | ∅ | ∅ | e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
--     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s₁ lind vs cv e
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s₁
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (∂→ x) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ¬∅ x with complLₛ s₁
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ¬∅ x | ∅ = (x ←∂) , refl
--   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x₁ ←∂→ x) , refl
  
  
  
  


-- ¬contruct↓⇒¬compl∅ : ∀{i u ll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → ¬ (complLₛ s ≡ ∅)
-- ¬contruct↓⇒¬compl∅ ↓ eq = ⊥-elim (eq refl)
-- ¬contruct↓⇒¬compl∅ (s ←∧) eq with (complLₛ s)
-- ¬contruct↓⇒¬compl∅ (s ←∧) eq | ∅ = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∧) eq | ¬∅ x = λ ()
-- ¬contruct↓⇒¬compl∅ (∧→ s) eq with (complLₛ s)
-- ¬contruct↓⇒¬compl∅ (∧→ s) eq | ∅ = λ ()
-- ¬contruct↓⇒¬compl∅ (∧→ s) eq | ¬∅ x = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
-- ¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | yes g with contruct s | contruct s₁ 
-- ¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes refl | yes refl | .↓ | .↓ = ⊥-elim (eq refl)
-- ¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g with ¬contruct↓⇒¬compl∅ s₁ ¬g
-- ... | w with complLₛ s | complLₛ s₁
-- ¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | w | r | ∅ = ⊥-elim (w refl) 
-- ¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | w | ∅ | ¬∅ x = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | w | ¬∅ x | ¬∅ x₁ = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g with ¬contruct↓⇒¬compl∅ s ¬p
-- ... | w with complLₛ s | complLₛ s₁
-- ¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g | w | ∅ | e = ⊥-elim (w refl)
-- ¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g | w | ¬∅ x | ∅ = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∧→ s₁) eq | no ¬p | g | w | ¬∅ x | ¬∅ x₁ = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∨) eq with (complLₛ s)
-- ¬contruct↓⇒¬compl∅ (s ←∨) eq | ∅ = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∨) eq | ¬∅ x = λ ()
-- ¬contruct↓⇒¬compl∅ (∨→ s) eq with (complLₛ s)
-- ¬contruct↓⇒¬compl∅ (∨→ s) eq | ∅ = λ ()
-- ¬contruct↓⇒¬compl∅ (∨→ s) eq | ¬∅ x = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
-- ¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | yes g with contruct s | contruct s₁ 
-- ¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes refl | yes refl | .↓ | .↓ = ⊥-elim (eq refl)
-- ¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g with ¬contruct↓⇒¬compl∅ s₁ ¬g
-- ... | w with complLₛ s | complLₛ s₁
-- ¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | w | r | ∅ = ⊥-elim (w refl) 
-- ¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | w | ∅ | ¬∅ x = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | w | ¬∅ x | ¬∅ x₁ = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g with ¬contruct↓⇒¬compl∅ s ¬p
-- ... | w with complLₛ s | complLₛ s₁
-- ¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g | w | ∅ | e = ⊥-elim (w refl)
-- ¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g | w | ¬∅ x | ∅ = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∨→ s₁) eq | no ¬p | g | w | ¬∅ x | ¬∅ x₁ = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∂) eq with (complLₛ s)
-- ¬contruct↓⇒¬compl∅ (s ←∂) eq | ∅ = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∂) eq | ¬∅ x = λ ()
-- ¬contruct↓⇒¬compl∅ (∂→ s) eq with (complLₛ s)
-- ¬contruct↓⇒¬compl∅ (∂→ s) eq | ∅ = λ ()
-- ¬contruct↓⇒¬compl∅ (∂→ s) eq | ¬∅ x = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
-- ¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | yes g with contruct s | contruct s₁ 
-- ¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes refl | yes refl | .↓ | .↓ = ⊥-elim (eq refl)
-- ¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g with ¬contruct↓⇒¬compl∅ s₁ ¬g
-- ... | w with complLₛ s | complLₛ s₁
-- ¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | w | r | ∅ = ⊥-elim (w refl) 
-- ¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | w | ∅ | ¬∅ x = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | w | ¬∅ x | ¬∅ x₁ = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g with ¬contruct↓⇒¬compl∅ s ¬p
-- ... | w with complLₛ s | complLₛ s₁
-- ¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g | w | ∅ | e = ⊥-elim (w refl)
-- ¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g | w | ¬∅ x | ∅ = λ ()
-- ¬contruct↓⇒¬compl∅ (s ←∂→ s₁) eq | no ¬p | g | w | ¬∅ x | ¬∅ x₁ = λ ()


-- module _ where

--   open Data.Product
  
--   contruct↓⇒compl∅ : ∀{i u ll} → (s : SetLL {i} {u} ll) → (contruct s ≡ ↓) → (complLₛ s ≡ ∅)
--   contruct↓⇒compl∅ ↓ eq = refl
--   contruct↓⇒compl∅ (s ←∧) ()
--   contruct↓⇒compl∅ (∧→ s) ()
--   contruct↓⇒compl∅ (s ←∧→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
--   contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g with complLₛ s | inspect complLₛ s | complLₛ s₁ |  inspect complLₛ s₁
--   contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ∅ | [ eq2 ] = refl
--   contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ¬∅ x | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s₁ g)) eq2
--   ... | ()
--   contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | yes g | ¬∅ x | [ eq1 ] | r | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s p)) eq1
--   ... | ()
--   contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | no ¬g with contruct s | contruct s₁
--   contruct↓⇒compl∅ (s ←∧→ s₁) eq | yes p | no ¬g | ↓ | ↓ = ⊥-elim (¬g refl)
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∧
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | ∧→ r 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∧→ r₁ 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∨ 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | ∨→ r 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∨→ r₁ 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∂ 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | ∂→ r 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ↓ | r ←∂→ r₁ 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∧ | r 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ∧→ e | r 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∧→ e₁ | r 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∨ | r 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ∨→ e | r 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∨→ e₁ | r 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∂ | r 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | ∂→ e | r 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | yes p | no ¬g | e ←∂→ e₁ | r 

--   contruct↓⇒compl∅ (s ←∧→ s₁) eq | no ¬p | r with contruct s | contruct s₁
--   contruct↓⇒compl∅ (s ←∧→ s₁) eq | no ¬p | r | ↓ | w = ⊥-elim (¬p refl)
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∧ | w 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | ∧→ e | w 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∧→ e₁ | w 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∨ | w 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | ∨→ e | w 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∨→ e₁ | w 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∂ | w 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | ∂→ e | w 
--   contruct↓⇒compl∅ (s ←∧→ s₁) () | no ¬p | r | e ←∂→ e₁ | w 

--   contruct↓⇒compl∅ (s ←∨) ()
--   contruct↓⇒compl∅ (∨→ s) ()
--   contruct↓⇒compl∅ (s ←∨→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
--   contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g with complLₛ s | inspect complLₛ s | complLₛ s₁ |  inspect complLₛ s₁
--   contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ∅ | [ eq2 ] = refl
--   contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ¬∅ x | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s₁ g)) eq2
--   ... | ()
--   contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | yes g | ¬∅ x | [ eq1 ] | r | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s p)) eq1
--   ... | ()
--   contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | no ¬g with contruct s | contruct s₁
--   contruct↓⇒compl∅ (s ←∨→ s₁) eq | yes p | no ¬g | ↓ | ↓ = ⊥-elim (¬g refl)
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∧
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | ∧→ r 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∧→ r₁ 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∨ 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | ∨→ r 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∨→ r₁ 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∂ 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | ∂→ r 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ↓ | r ←∂→ r₁ 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∧ | r 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ∧→ e | r 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∧→ e₁ | r 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∨ | r 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ∨→ e | r 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∨→ e₁ | r 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∂ | r 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | ∂→ e | r 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | yes p | no ¬g | e ←∂→ e₁ | r 

--   contruct↓⇒compl∅ (s ←∨→ s₁) eq | no ¬p | r with contruct s | contruct s₁
--   contruct↓⇒compl∅ (s ←∨→ s₁) eq | no ¬p | r | ↓ | w = ⊥-elim (¬p refl)
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∧ | w 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | ∧→ e | w 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∧→ e₁ | w 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∨ | w 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | ∨→ e | w 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∨→ e₁ | w 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∂ | w 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | ∂→ e | w 
--   contruct↓⇒compl∅ (s ←∨→ s₁) () | no ¬p | r | e ←∂→ e₁ | w 

--   contruct↓⇒compl∅ (s ←∂) ()
--   contruct↓⇒compl∅ (∂→ s) ()
--   contruct↓⇒compl∅ (s ←∂→ s₁) eq with isEq (contruct s) ↓ | isEq (contruct s₁) ↓
--   contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g with complLₛ s | inspect complLₛ s | complLₛ s₁ |  inspect complLₛ s₁
--   contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ∅ | [ eq2 ] = refl
--   contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g | ∅ | [ eq1 ] | ¬∅ x | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s₁ g)) eq2
--   ... | ()
--   contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | yes g | ¬∅ x | [ eq1 ] | r | [ eq2 ] with trans (sym (contruct↓⇒compl∅ s p)) eq1
--   ... | ()
--   contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | no ¬g with contruct s | contruct s₁
--   contruct↓⇒compl∅ (s ←∂→ s₁) eq | yes p | no ¬g | ↓ | ↓ = ⊥-elim (¬g refl)
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∧
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | ∧→ r 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∧→ r₁ 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∨ 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | ∨→ r 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∨→ r₁ 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∂ 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | ∂→ r 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ↓ | r ←∂→ r₁ 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∧ | r 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ∧→ e | r 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∧→ e₁ | r 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∨ | r 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ∨→ e | r 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∨→ e₁ | r 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∂ | r 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | ∂→ e | r 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | yes p | no ¬g | e ←∂→ e₁ | r 

--   contruct↓⇒compl∅ (s ←∂→ s₁) eq | no ¬p | r with contruct s | contruct s₁
--   contruct↓⇒compl∅ (s ←∂→ s₁) eq | no ¬p | r | ↓ | w = ⊥-elim (¬p refl)
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∧ | w 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | ∧→ e | w 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∧→ e₁ | w 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∨ | w 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | ∨→ e | w 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∨→ e₁ | w 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∂ | w 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | ∂→ e | w 
--   contruct↓⇒compl∅ (s ←∂→ s₁) () | no ¬p | r | e ←∂→ e₁ | w 





--   compl∅⇒contruct↓ : ∀{i u ll} → (s : SetLL {i} {u} ll) → (complLₛ s ≡ ∅) → (contruct s ≡ ↓)
--   compl∅⇒contruct↓ s eq with isEq (contruct s) ↓
--   compl∅⇒contruct↓ s eq | yes p = p
--   compl∅⇒contruct↓ s eq | no ¬p = ⊥-elim (¬contruct↓⇒¬compl∅ s ¬p eq)

--   ¬compl∅⇒¬contruct↓ : ∀{i u ll} → (s : SetLL {i} {u} ll) → ¬ (complLₛ s ≡ ∅) → ¬ (contruct s ≡ ↓)
--   ¬compl∅⇒¬contruct↓ s neq with isEq (contruct s) ↓
--   ¬compl∅⇒¬contruct↓ s neq | yes p = ⊥-elim (neq (contruct↓⇒compl∅ s p))
--   ¬compl∅⇒¬contruct↓ s neq | no ¬p = ¬p






-- module _ where


--   data onlyInside {i u rll} : ∀{ll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → Set where
--     onlyInsideCs↓ : ∀{s} → onlyInside {ll = rll} s ↓
--     onlyInsideC←∧←∧ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = ll ∧ q} (s ←∧) (ind ←∧)
--     onlyInsideC∧→∧→ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = q ∧ ll} (∧→ s) (∧→ ind)
--     onlyInsideC←∨←∨ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = ll ∨ q} (s ←∨) (ind ←∨)
--     onlyInsideC∨→∨→ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = q ∨ ll} (∨→ s) (∨→ ind)
--     onlyInsideC←∂←∂ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = ll ∂ q} (s ←∂) (ind ←∂)
--     onlyInsideC∂→∂→ : ∀{ll q s ind} → onlyInside s ind → onlyInside {ll = q ∂ ll} (∂→ s) (∂→ ind)




--   onlyInsideUnique : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) 
--                    → (a : onlyInside s ind) → (b : onlyInside s ind)
--                    → a ≡ b
--   onlyInsideUnique ↓ ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
--   onlyInsideUnique ↓ (ind ←∧) () b
--   onlyInsideUnique ↓ (∧→ ind) () b
--   onlyInsideUnique ↓ (ind ←∨) () b
--   onlyInsideUnique ↓ (∨→ ind) () b
--   onlyInsideUnique ↓ (ind ←∂) () b
--   onlyInsideUnique ↓ (∂→ ind) () b
--   onlyInsideUnique (s ←∧) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
--   onlyInsideUnique (s ←∧) (ind ←∧) (onlyInsideC←∧←∧ a) (onlyInsideC←∧←∧ b) with (onlyInsideUnique s ind a b)
--   onlyInsideUnique (s ←∧) (ind ←∧) (onlyInsideC←∧←∧ a) (onlyInsideC←∧←∧ .a) | refl = refl
--   onlyInsideUnique (s ←∧) (∧→ ind) () b
--   onlyInsideUnique (∧→ s) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
--   onlyInsideUnique (∧→ s) (ind ←∧) () b
--   onlyInsideUnique (∧→ s) (∧→ ind) (onlyInsideC∧→∧→ a) (onlyInsideC∧→∧→ b) with (onlyInsideUnique s ind a b)
--   onlyInsideUnique (∧→ s) (∧→ ind) (onlyInsideC∧→∧→ a) (onlyInsideC∧→∧→ .a) | refl = refl
--   onlyInsideUnique (s ←∧→ s₁) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
--   onlyInsideUnique (s ←∧→ s₁) (ind ←∧) () b
--   onlyInsideUnique (s ←∧→ s₁) (∧→ ind) () b
--   onlyInsideUnique (s ←∨) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
--   onlyInsideUnique (s ←∨) (ind ←∨) (onlyInsideC←∨←∨ a) (onlyInsideC←∨←∨ b) with (onlyInsideUnique s ind a b)
--   onlyInsideUnique (s ←∨) (ind ←∨) (onlyInsideC←∨←∨ a) (onlyInsideC←∨←∨ .a) | refl = refl
--   onlyInsideUnique (s ←∨) (∨→ ind) () b
--   onlyInsideUnique (∨→ s) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
--   onlyInsideUnique (∨→ s) (ind ←∨) () b
--   onlyInsideUnique (∨→ s) (∨→ ind) (onlyInsideC∨→∨→ a) (onlyInsideC∨→∨→ b) with (onlyInsideUnique s ind a b)
--   onlyInsideUnique (∨→ s) (∨→ ind) (onlyInsideC∨→∨→ a) (onlyInsideC∨→∨→ .a) | refl = refl
--   onlyInsideUnique (s ←∨→ s₁) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
--   onlyInsideUnique (s ←∨→ s₁) (ind ←∨) () b
--   onlyInsideUnique (s ←∨→ s₁) (∨→ ind) () b
--   onlyInsideUnique (s ←∂) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
--   onlyInsideUnique (s ←∂) (ind ←∂) (onlyInsideC←∂←∂ a) (onlyInsideC←∂←∂ b) with (onlyInsideUnique s ind a b)
--   onlyInsideUnique (s ←∂) (ind ←∂) (onlyInsideC←∂←∂ a) (onlyInsideC←∂←∂ .a) | refl = refl
--   onlyInsideUnique (s ←∂) (∂→ ind) () b
--   onlyInsideUnique (∂→ s) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
--   onlyInsideUnique (∂→ s) (ind ←∂) () b
--   onlyInsideUnique (∂→ s) (∂→ ind) (onlyInsideC∂→∂→ a) (onlyInsideC∂→∂→ b) with (onlyInsideUnique s ind a b)
--   onlyInsideUnique (∂→ s) (∂→ ind) (onlyInsideC∂→∂→ a) (onlyInsideC∂→∂→ .a) | refl = refl
--   onlyInsideUnique (s ←∂→ s₁) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
--   onlyInsideUnique (s ←∂→ s₁) (ind ←∂) () b
--   onlyInsideUnique (s ←∂→ s₁) (∂→ ind) () b


--   isOnlyInside : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → Dec (onlyInside s ind)
--   isOnlyInside ↓ ↓ = yes onlyInsideCs↓
--   isOnlyInside ↓ (ind ←∧) = no (λ ())
--   isOnlyInside ↓ (∧→ ind) = no (λ ())
--   isOnlyInside ↓ (ind ←∨) = no (λ ())
--   isOnlyInside ↓ (∨→ ind) = no (λ ())
--   isOnlyInside ↓ (ind ←∂) = no (λ ())
--   isOnlyInside ↓ (∂→ ind) = no (λ ())
--   isOnlyInside (s ←∧) ↓ = yes onlyInsideCs↓
--   isOnlyInside (s ←∧) (ind ←∧) with (isOnlyInside s ind)
--   isOnlyInside (s ←∧) (ind ←∧) | yes p = yes (onlyInsideC←∧←∧ p)
--   isOnlyInside (s ←∧) (ind ←∧) | no ¬p = no (λ {(onlyInsideC←∧←∧ x) → ¬p x})
--   isOnlyInside (s ←∧) (∧→ ind) = no (λ ())
--   isOnlyInside (∧→ s) ↓ = yes onlyInsideCs↓
--   isOnlyInside (∧→ s) (ind ←∧) = no (λ ())
--   isOnlyInside (∧→ s) (∧→ ind) with (isOnlyInside s ind)
--   isOnlyInside (∧→ s) (∧→ ind) | yes p = yes (onlyInsideC∧→∧→ p)
--   isOnlyInside (∧→ s) (∧→ ind) | no ¬p = no (λ { (onlyInsideC∧→∧→ x) → ¬p x})
--   isOnlyInside (s ←∧→ s₁) ↓ = yes onlyInsideCs↓
--   isOnlyInside (s ←∧→ s₁) (ind ←∧) = no (λ ())
--   isOnlyInside (s ←∧→ s₁) (∧→ ind) = no (λ ())
--   isOnlyInside (s ←∨) ↓ = yes onlyInsideCs↓
--   isOnlyInside (s ←∨) (ind ←∨) with (isOnlyInside s ind)
--   isOnlyInside (s ←∨) (ind ←∨) | yes p = yes (onlyInsideC←∨←∨ p)
--   isOnlyInside (s ←∨) (ind ←∨) | no ¬p = no ( λ { (onlyInsideC←∨←∨ x) → ¬p x})
--   isOnlyInside (s ←∨) (∨→ ind) = no (λ ())
--   isOnlyInside (∨→ s) ↓ = yes onlyInsideCs↓
--   isOnlyInside (∨→ s) (ind ←∨) = no (λ ())
--   isOnlyInside (∨→ s) (∨→ ind) with (isOnlyInside s ind)
--   isOnlyInside (∨→ s) (∨→ ind) | yes p = yes (onlyInsideC∨→∨→ p)
--   isOnlyInside (∨→ s) (∨→ ind) | no ¬p = no ( λ { (onlyInsideC∨→∨→ x) → ¬p x})
--   isOnlyInside (s ←∨→ s₁) ↓ = yes onlyInsideCs↓
--   isOnlyInside (s ←∨→ s₁) (ind ←∨) = no (λ ())
--   isOnlyInside (s ←∨→ s₁) (∨→ ind) = no (λ ())
--   isOnlyInside (s ←∂) ↓ = yes onlyInsideCs↓
--   isOnlyInside (s ←∂) (ind ←∂) with (isOnlyInside s ind)
--   isOnlyInside (s ←∂) (ind ←∂) | yes p = yes (onlyInsideC←∂←∂ p)
--   isOnlyInside (s ←∂) (ind ←∂) | no ¬p = no ( λ { (onlyInsideC←∂←∂ x) → ¬p x})
--   isOnlyInside (s ←∂) (∂→ ind) = no (λ ())
--   isOnlyInside (∂→ s) ↓ = yes onlyInsideCs↓
--   isOnlyInside (∂→ s) (ind ←∂) = no (λ ())
--   isOnlyInside (∂→ s) (∂→ ind) with (isOnlyInside s ind)
--   isOnlyInside (∂→ s) (∂→ ind) | yes p = yes (onlyInsideC∂→∂→ p)
--   isOnlyInside (∂→ s) (∂→ ind) | no ¬p = no (λ { (onlyInsideC∂→∂→ x) → ¬p x})
--   isOnlyInside (s ←∂→ s₁) ↓ = yes onlyInsideCs↓
--   isOnlyInside (s ←∂→ s₁) (ind ←∂) = no (λ ())
--   isOnlyInside (s ←∂→ s₁) (∂→ ind) = no (λ ())




--   hitsAtLeastOnceUnique : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → (a : hitsAtLeastOnce s ind) → (b : hitsAtLeastOnce s ind) → a ≡ b
--   hitsAtLeastOnceUnique ↓ ind hitsAtLeastOnce↓ hitsAtLeastOnce↓ = refl
--   hitsAtLeastOnceUnique (s ←∧) ↓ hitsAtLeastOnce←∧↓ hitsAtLeastOnce←∧↓ = refl
--   hitsAtLeastOnceUnique (s ←∧) (ind ←∧) (hitsAtLeastOnce←∧←∧ a) (hitsAtLeastOnce←∧←∧ b) with (hitsAtLeastOnceUnique s ind a b)
--   hitsAtLeastOnceUnique (s ←∧) (ind ←∧) (hitsAtLeastOnce←∧←∧ a) (hitsAtLeastOnce←∧←∧ .a) | refl = refl
--   hitsAtLeastOnceUnique (s ←∧) (∧→ ind) () b
--   hitsAtLeastOnceUnique (∧→ s) ↓ hitsAtLeastOnce∧→↓ hitsAtLeastOnce∧→↓ = refl
--   hitsAtLeastOnceUnique (∧→ s) (ind ←∧) () b
--   hitsAtLeastOnceUnique (∧→ s) (∧→ ind) (hitsAtLeastOnce∧→∧→ a) (hitsAtLeastOnce∧→∧→ b) with (hitsAtLeastOnceUnique s ind a b)
--   hitsAtLeastOnceUnique (∧→ s) (∧→ ind) (hitsAtLeastOnce∧→∧→ a) (hitsAtLeastOnce∧→∧→ .a) | refl = refl
--   hitsAtLeastOnceUnique (s ←∧→ s₁) ↓ hitsAtLeastOnce←∧→↓ hitsAtLeastOnce←∧→↓ = refl
--   hitsAtLeastOnceUnique (s ←∧→ s₁) (ind ←∧) (hitsAtLeastOnce←∧→←∧ a) (hitsAtLeastOnce←∧→←∧ b) with (hitsAtLeastOnceUnique s ind a b)
--   hitsAtLeastOnceUnique (s ←∧→ s₁) (ind ←∧) (hitsAtLeastOnce←∧→←∧ a) (hitsAtLeastOnce←∧→←∧ .a) | refl = refl
--   hitsAtLeastOnceUnique (s ←∧→ s₁) (∧→ ind) (hitsAtLeastOnce←∧→∧→ a) (hitsAtLeastOnce←∧→∧→ b) with (hitsAtLeastOnceUnique s₁ ind a b)
--   hitsAtLeastOnceUnique (s ←∧→ s₁) (∧→ ind) (hitsAtLeastOnce←∧→∧→ a) (hitsAtLeastOnce←∧→∧→ .a) | refl = refl
--   hitsAtLeastOnceUnique (s ←∨) ↓ hitsAtLeastOnce←∨↓ hitsAtLeastOnce←∨↓ = refl
--   hitsAtLeastOnceUnique (s ←∨) (ind ←∨) (hitsAtLeastOnce←∨←∨ a) (hitsAtLeastOnce←∨←∨ b) with (hitsAtLeastOnceUnique s ind a b)
--   hitsAtLeastOnceUnique (s ←∨) (ind ←∨) (hitsAtLeastOnce←∨←∨ a) (hitsAtLeastOnce←∨←∨ .a) | refl = refl
--   hitsAtLeastOnceUnique (s ←∨) (∨→ ind) () b
--   hitsAtLeastOnceUnique (∨→ s) ↓ hitsAtLeastOnce∨→↓ hitsAtLeastOnce∨→↓ = refl
--   hitsAtLeastOnceUnique (∨→ s) (ind ←∨) () b
--   hitsAtLeastOnceUnique (∨→ s) (∨→ ind) (hitsAtLeastOnce∨→∨→ a) (hitsAtLeastOnce∨→∨→ b) with (hitsAtLeastOnceUnique s ind a b)
--   hitsAtLeastOnceUnique (∨→ s) (∨→ ind) (hitsAtLeastOnce∨→∨→ a) (hitsAtLeastOnce∨→∨→ .a) | refl = refl
--   hitsAtLeastOnceUnique (s ←∨→ s₁) ↓ hitsAtLeastOnce←∨→↓ hitsAtLeastOnce←∨→↓ = refl
--   hitsAtLeastOnceUnique (s ←∨→ s₁) (ind ←∨) (hitsAtLeastOnce←∨→←∨ a) (hitsAtLeastOnce←∨→←∨ b) with (hitsAtLeastOnceUnique s ind a b)
--   hitsAtLeastOnceUnique (s ←∨→ s₁) (ind ←∨) (hitsAtLeastOnce←∨→←∨ a) (hitsAtLeastOnce←∨→←∨ .a) | refl = refl
--   hitsAtLeastOnceUnique (s ←∨→ s₁) (∨→ ind) (hitsAtLeastOnce←∨→∨→ a) (hitsAtLeastOnce←∨→∨→ b) with (hitsAtLeastOnceUnique s₁ ind a b)
--   hitsAtLeastOnceUnique (s ←∨→ s₁) (∨→ ind) (hitsAtLeastOnce←∨→∨→ a) (hitsAtLeastOnce←∨→∨→ .a) | refl = refl
--   hitsAtLeastOnceUnique (s ←∂) ↓ hitsAtLeastOnce←∂↓ hitsAtLeastOnce←∂↓ = refl
--   hitsAtLeastOnceUnique (s ←∂) (ind ←∂) (hitsAtLeastOnce←∂←∂ a) (hitsAtLeastOnce←∂←∂ b) with (hitsAtLeastOnceUnique s ind a b)
--   hitsAtLeastOnceUnique (s ←∂) (ind ←∂) (hitsAtLeastOnce←∂←∂ a) (hitsAtLeastOnce←∂←∂ .a) | refl = refl
--   hitsAtLeastOnceUnique (s ←∂) (∂→ ind) () b
--   hitsAtLeastOnceUnique (∂→ s) ↓ hitsAtLeastOnce∂→↓ hitsAtLeastOnce∂→↓ = refl
--   hitsAtLeastOnceUnique (∂→ s) (ind ←∂) () b
--   hitsAtLeastOnceUnique (∂→ s) (∂→ ind) (hitsAtLeastOnce∂→∂→ a) (hitsAtLeastOnce∂→∂→ b) with (hitsAtLeastOnceUnique s ind a b)
--   hitsAtLeastOnceUnique (∂→ s) (∂→ ind) (hitsAtLeastOnce∂→∂→ a) (hitsAtLeastOnce∂→∂→ .a) | refl = refl
--   hitsAtLeastOnceUnique (s ←∂→ s₁) ↓ hitsAtLeastOnce←∂→↓ hitsAtLeastOnce←∂→↓ = refl
--   hitsAtLeastOnceUnique (s ←∂→ s₁) (ind ←∂) (hitsAtLeastOnce←∂→←∂ a) (hitsAtLeastOnce←∂→←∂ b) with (hitsAtLeastOnceUnique s ind a b)
--   hitsAtLeastOnceUnique (s ←∂→ s₁) (ind ←∂) (hitsAtLeastOnce←∂→←∂ a) (hitsAtLeastOnce←∂→←∂ .a) | refl = refl
--   hitsAtLeastOnceUnique (s ←∂→ s₁) (∂→ ind) (hitsAtLeastOnce←∂→∂→ a) (hitsAtLeastOnce←∂→∂→ b) with (hitsAtLeastOnceUnique s₁ ind a b)
--   hitsAtLeastOnceUnique (s ←∂→ s₁) (∂→ ind) (hitsAtLeastOnce←∂→∂→ a) (hitsAtLeastOnce←∂→∂→ .a) | refl = refl





--   ho-spec : ∀{i u ll rll tll ic ns} → {s : SetLL (expLLT ic tll)} → {ind : IndexLL {i} {u} rll ll} → {{eq : sl-ext {ic = ic} s ≡ ¬∅ ns}} → hitsAtLeastOnce s (expInd ic tll ind) → hitsAtLeastOnce ns ind
--   ho-spec {ic = ic←∧} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-spec {ic = ic←∧} {s = s ←∧} {{eq = refl}} (hitsAtLeastOnce←∧←∧ ho) = ho
--   ho-spec {ic = ic←∧} {s = ∧→ s} {{eq = ()}} ho
--   ho-spec {ic = ic←∧} {s = s ←∧→ s₁} {{eq = refl}} (hitsAtLeastOnce←∧→←∧ ho) = ho
--   ho-spec {ic = ic∧→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-spec {ic = ic∧→} {s = s ←∧} {{eq = ()}} ho
--   ho-spec {ic = ic∧→} {s = ∧→ s} {{eq = refl}} (hitsAtLeastOnce∧→∧→ ho) = ho
--   ho-spec {ic = ic∧→} {s = s ←∧→ s₁} {{eq = refl}} (hitsAtLeastOnce←∧→∧→ ho) = ho
--   ho-spec {ic = ic←∨} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-spec {ic = ic←∨} {s = s ←∨} {{eq = refl}} (hitsAtLeastOnce←∨←∨ ho) = ho
--   ho-spec {ic = ic←∨} {s = ∨→ s} {{eq = ()}} ho
--   ho-spec {ic = ic←∨} {s = s ←∨→ s₁} {{eq = refl}} (hitsAtLeastOnce←∨→←∨ ho) = ho
--   ho-spec {ic = ic∨→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-spec {ic = ic∨→} {s = s ←∨} {{eq = ()}} ho
--   ho-spec {ic = ic∨→} {s = ∨→ s} {{eq = refl}} (hitsAtLeastOnce∨→∨→ ho) = ho
--   ho-spec {ic = ic∨→} {s = s ←∨→ s₁} {{eq = refl}} (hitsAtLeastOnce←∨→∨→ ho) = ho
--   ho-spec {ic = ic←∂} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-spec {ic = ic←∂} {s = s ←∂} {{eq = refl}} (hitsAtLeastOnce←∂←∂ ho) = ho
--   ho-spec {ic = ic←∂} {s = ∂→ s} {{eq = ()}} ho
--   ho-spec {ic = ic←∂} {s = s ←∂→ s₁} {{eq = refl}} (hitsAtLeastOnce←∂→←∂ ho) = ho
--   ho-spec {ic = ic∂→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-spec {ic = ic∂→} {s = s ←∂} {{eq = ()}} ho
--   ho-spec {ic = ic∂→} {s = ∂→ s} {{eq = refl}} (hitsAtLeastOnce∂→∂→ ho) = ho
--   ho-spec {ic = ic∂→} {s = s ←∂→ s₁} {{eq = refl}} (hitsAtLeastOnce←∂→∂→ ho) = ho
  
  
  
--   ho-ext : ∀{i u ll rll tll ic ns} → {s : SetLL (expLLT ic tll)} → {ind : IndexLL {i} {u} rll ll} → {{eq : sl-ext {ic = ic} s ≡ ¬∅ ns}} → hitsAtLeastOnce ns ind → hitsAtLeastOnce s (expInd ic tll ind)
--   ho-ext {ic = ic←∧} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-ext {ic = ic←∧} {s = s ←∧} {{eq = refl}} ho = hitsAtLeastOnce←∧←∧ ho
--   ho-ext {ic = ic←∧} {s = ∧→ s} {{eq = ()}} ho
--   ho-ext {ic = ic←∧} {s = s ←∧→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∧→←∧ ho
--   ho-ext {ic = ic∧→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-ext {ic = ic∧→} {s = s ←∧} {{eq = ()}} ho
--   ho-ext {ic = ic∧→} {s = ∧→ s} {{eq = refl}} ho = hitsAtLeastOnce∧→∧→ ho
--   ho-ext {ic = ic∧→} {s = s ←∧→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∧→∧→ ho
--   ho-ext {ic = ic←∨} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-ext {ic = ic←∨} {s = s ←∨} {{eq = refl}} ho = hitsAtLeastOnce←∨←∨ ho
--   ho-ext {ic = ic←∨} {s = ∨→ s} {{eq = ()}} ho
--   ho-ext {ic = ic←∨} {s = s ←∨→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∨→←∨ ho
--   ho-ext {ic = ic∨→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-ext {ic = ic∨→} {s = s ←∨} {{eq = ()}} ho
--   ho-ext {ic = ic∨→} {s = ∨→ s} {{eq = refl}} ho = hitsAtLeastOnce∨→∨→ ho
--   ho-ext {ic = ic∨→} {s = s ←∨→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∨→∨→ ho
--   ho-ext {ic = ic←∂} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-ext {ic = ic←∂} {s = s ←∂} {{eq = refl}} ho = hitsAtLeastOnce←∂←∂ ho
--   ho-ext {ic = ic←∂} {s = ∂→ s} {{eq = ()}} ho
--   ho-ext {ic = ic←∂} {s = s ←∂→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∂→←∂ ho
--   ho-ext {ic = ic∂→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
--   ho-ext {ic = ic∂→} {s = s ←∂} {{eq = ()}} ho
--   ho-ext {ic = ic∂→} {s = ∂→ s} {{eq = refl}} ho = hitsAtLeastOnce∂→∂→ ho
--   ho-ext {ic = ic∂→} {s = s ←∂→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∂→∂→ ho
  
  
  
--   ¬ho-spec : ∀{i u ll rll tll ic ns} → {s : SetLL (expLLT ic tll)} → {ind : IndexLL {i} {u} rll ll} → {{eq : sl-ext {ic = ic} s ≡ ¬∅ ns}} → ¬ (hitsAtLeastOnce s (expInd ic tll ind)) → ¬ (hitsAtLeastOnce ns ind)
--   ¬ho-spec {ic = ic} {s = s} {{eq = eq}} ¬ho y = ¬ho (ho-ext y)
  
  
  

--   oi⇒ho : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → onlyInside s ind → hitsAtLeastOnce s ind
--   oi⇒ho ↓ ↓ onlyInsideCs↓ = hitsAtLeastOnce↓
--   oi⇒ho ↓ (ind ←∧) ()
--   oi⇒ho ↓ (∧→ ind) ()
--   oi⇒ho ↓ (ind ←∨) ()
--   oi⇒ho ↓ (∨→ ind) ()
--   oi⇒ho ↓ (ind ←∂) ()
--   oi⇒ho ↓ (∂→ ind) ()
--   oi⇒ho (s ←∧) ↓ onlyInsideCs↓ = hitsAtLeastOnce←∧↓
--   oi⇒ho (s ←∧) (ind ←∧) (onlyInsideC←∧←∧ oi) = hitsAtLeastOnce←∧←∧ (oi⇒ho s ind oi)
--   oi⇒ho (s ←∧) (∧→ ind) ()
--   oi⇒ho (∧→ s) ↓ oi = hitsAtLeastOnce∧→↓
--   oi⇒ho (∧→ s) (ind ←∧) ()
--   oi⇒ho (∧→ s) (∧→ ind) (onlyInsideC∧→∧→ x) = hitsAtLeastOnce∧→∧→ (oi⇒ho s ind x)
--   oi⇒ho (s ←∧→ s₁) ↓ oi = hitsAtLeastOnce←∧→↓
--   oi⇒ho (s ←∧→ s₁) (ind ←∧) ()
--   oi⇒ho (s ←∧→ s₁) (∧→ ind) ()
--   oi⇒ho (s ←∨) ↓ onlyInsideCs↓ = hitsAtLeastOnce←∨↓
--   oi⇒ho (s ←∨) (ind ←∨) (onlyInsideC←∨←∨ oi) = hitsAtLeastOnce←∨←∨ (oi⇒ho s ind oi)
--   oi⇒ho (s ←∨) (∨→ ind) ()
--   oi⇒ho (∨→ s) ↓ oi = hitsAtLeastOnce∨→↓
--   oi⇒ho (∨→ s) (ind ←∨) ()
--   oi⇒ho (∨→ s) (∨→ ind) (onlyInsideC∨→∨→ x) = hitsAtLeastOnce∨→∨→ (oi⇒ho s ind x)
--   oi⇒ho (s ←∨→ s₁) ↓ oi = hitsAtLeastOnce←∨→↓
--   oi⇒ho (s ←∨→ s₁) (ind ←∨) ()
--   oi⇒ho (s ←∨→ s₁) (∨→ ind) ()
--   oi⇒ho (s ←∂) ↓ onlyInsideCs↓ = hitsAtLeastOnce←∂↓
--   oi⇒ho (s ←∂) (ind ←∂) (onlyInsideC←∂←∂ oi) = hitsAtLeastOnce←∂←∂ (oi⇒ho s ind oi)
--   oi⇒ho (s ←∂) (∂→ ind) ()
--   oi⇒ho (∂→ s) ↓ oi = hitsAtLeastOnce∂→↓
--   oi⇒ho (∂→ s) (ind ←∂) ()
--   oi⇒ho (∂→ s) (∂→ ind) (onlyInsideC∂→∂→ x) = hitsAtLeastOnce∂→∂→ (oi⇒ho s ind x)
--   oi⇒ho (s ←∂→ s₁) ↓ oi = hitsAtLeastOnce←∂→↓
--   oi⇒ho (s ←∂→ s₁) (ind ←∂) ()
--   oi⇒ho (s ←∂→ s₁) (∂→ ind) ()




--   doesItHitAtLeastOnce : ∀{i u ll q} → (s : SetLL ll) → (ind : IndexLL {i} {u} q ll) → Dec (hitsAtLeastOnce s ind)
--   doesItHitAtLeastOnce ↓ ind = yes hitsAtLeastOnce↓
--   doesItHitAtLeastOnce (s ←∧) ↓ = yes hitsAtLeastOnce←∧↓
--   doesItHitAtLeastOnce (s ←∧) (ind ←∧) with (doesItHitAtLeastOnce s ind)
--   doesItHitAtLeastOnce (s ←∧) (ind ←∧) | yes p = yes (hitsAtLeastOnce←∧←∧ p)
--   doesItHitAtLeastOnce (s ←∧) (ind ←∧) | no ¬p = no (λ {(hitsAtLeastOnce←∧←∧ x) → ¬p x})
--   doesItHitAtLeastOnce (s ←∧) (∧→ ind) = no (λ ())
--   doesItHitAtLeastOnce (∧→ s) ↓ = yes hitsAtLeastOnce∧→↓
--   doesItHitAtLeastOnce (∧→ s) (ind ←∧) = no (λ ())
--   doesItHitAtLeastOnce (∧→ s) (∧→ ind) with (doesItHitAtLeastOnce s ind)
--   doesItHitAtLeastOnce (∧→ s) (∧→ ind) | yes p = yes (hitsAtLeastOnce∧→∧→ p)
--   doesItHitAtLeastOnce (∧→ s) (∧→ ind) | no ¬p = no (λ {(hitsAtLeastOnce∧→∧→ x) → ¬p x})
--   doesItHitAtLeastOnce (s ←∧→ s₁) ↓ = yes hitsAtLeastOnce←∧→↓
--   doesItHitAtLeastOnce (s ←∧→ s₁) (ind ←∧) with (doesItHitAtLeastOnce s ind)
--   doesItHitAtLeastOnce (s ←∧→ s₁) (ind ←∧) | yes p = yes (hitsAtLeastOnce←∧→←∧ p)
--   doesItHitAtLeastOnce (s ←∧→ s₁) (ind ←∧) | no ¬p = no (λ {(hitsAtLeastOnce←∧→←∧ x) → ¬p x})
--   doesItHitAtLeastOnce (s ←∧→ s₁) (∧→ ind) with (doesItHitAtLeastOnce s₁ ind)
--   doesItHitAtLeastOnce (s ←∧→ s₁) (∧→ ind) | yes p = yes (hitsAtLeastOnce←∧→∧→ p) 
--   doesItHitAtLeastOnce (s ←∧→ s₁) (∧→ ind) | no ¬p = no (λ {(hitsAtLeastOnce←∧→∧→ x) → ¬p x})
--   doesItHitAtLeastOnce (s ←∨) ↓ = yes hitsAtLeastOnce←∨↓
--   doesItHitAtLeastOnce (s ←∨) (ind ←∨) with (doesItHitAtLeastOnce s ind)
--   doesItHitAtLeastOnce (s ←∨) (ind ←∨) | yes p = yes (hitsAtLeastOnce←∨←∨ p) 
--   doesItHitAtLeastOnce (s ←∨) (ind ←∨) | no ¬p = no (λ {(hitsAtLeastOnce←∨←∨ x) → ¬p x})
--   doesItHitAtLeastOnce (s ←∨) (∨→ ind) = no (λ ())
--   doesItHitAtLeastOnce (∨→ s) ↓ = yes hitsAtLeastOnce∨→↓
--   doesItHitAtLeastOnce (∨→ s) (ind ←∨) = no (λ ())
--   doesItHitAtLeastOnce (∨→ s) (∨→ ind) with (doesItHitAtLeastOnce s ind)
--   doesItHitAtLeastOnce (∨→ s) (∨→ ind) | yes p = yes (hitsAtLeastOnce∨→∨→ p) 
--   doesItHitAtLeastOnce (∨→ s) (∨→ ind) | no ¬p = no (λ {(hitsAtLeastOnce∨→∨→ x) → ¬p x})
--   doesItHitAtLeastOnce (s ←∨→ s₁) ↓ = yes hitsAtLeastOnce←∨→↓
--   doesItHitAtLeastOnce (s ←∨→ s₁) (ind ←∨) with (doesItHitAtLeastOnce s ind)
--   doesItHitAtLeastOnce (s ←∨→ s₁) (ind ←∨) | yes p = yes (hitsAtLeastOnce←∨→←∨ p) 
--   doesItHitAtLeastOnce (s ←∨→ s₁) (ind ←∨) | no ¬p = no (λ {(hitsAtLeastOnce←∨→←∨ x) → ¬p x})
--   doesItHitAtLeastOnce (s ←∨→ s₁) (∨→ ind) with (doesItHitAtLeastOnce s₁ ind)
--   doesItHitAtLeastOnce (s ←∨→ s₁) (∨→ ind) | yes p = yes (hitsAtLeastOnce←∨→∨→ p)
--   doesItHitAtLeastOnce (s ←∨→ s₁) (∨→ ind) | no ¬p = no (λ {(hitsAtLeastOnce←∨→∨→ x) → ¬p x})
--   doesItHitAtLeastOnce (s ←∂) ↓ = yes hitsAtLeastOnce←∂↓
--   doesItHitAtLeastOnce (s ←∂) (ind ←∂) with (doesItHitAtLeastOnce s ind)
--   doesItHitAtLeastOnce (s ←∂) (ind ←∂) | yes p = yes (hitsAtLeastOnce←∂←∂ p) 
--   doesItHitAtLeastOnce (s ←∂) (ind ←∂) | no ¬p = no (λ {(hitsAtLeastOnce←∂←∂ x) → ¬p x})
--   doesItHitAtLeastOnce (s ←∂) (∂→ ind) = no (λ ())
--   doesItHitAtLeastOnce (∂→ s) ↓ = yes hitsAtLeastOnce∂→↓
--   doesItHitAtLeastOnce (∂→ s) (ind ←∂) = no (λ ())
--   doesItHitAtLeastOnce (∂→ s) (∂→ ind) with (doesItHitAtLeastOnce s ind)
--   doesItHitAtLeastOnce (∂→ s) (∂→ ind) | yes p = yes (hitsAtLeastOnce∂→∂→ p) 
--   doesItHitAtLeastOnce (∂→ s) (∂→ ind) | no ¬p = no (λ {(hitsAtLeastOnce∂→∂→ x) → ¬p x})
--   doesItHitAtLeastOnce (s ←∂→ s₁) ↓ = yes hitsAtLeastOnce←∂→↓
--   doesItHitAtLeastOnce (s ←∂→ s₁) (ind ←∂) with (doesItHitAtLeastOnce s ind)
--   doesItHitAtLeastOnce (s ←∂→ s₁) (ind ←∂) | yes p = yes (hitsAtLeastOnce←∂→←∂ p)
--   doesItHitAtLeastOnce (s ←∂→ s₁) (ind ←∂) | no ¬p = no (λ {(hitsAtLeastOnce←∂→←∂ x) → ¬p x})
--   doesItHitAtLeastOnce (s ←∂→ s₁) (∂→ ind) with (doesItHitAtLeastOnce s₁ ind)
--   doesItHitAtLeastOnce (s ←∂→ s₁) (∂→ ind) | yes p = yes (hitsAtLeastOnce←∂→∂→ p)
--   doesItHitAtLeastOnce (s ←∂→ s₁) (∂→ ind) | no ¬p = no (λ {(hitsAtLeastOnce←∂→∂→ x) → ¬p x})


-- compl≡∅⇒ho : ∀{i u rll ll} → (s : SetLL {i} {u} ll) → complLₛ s ≡ ∅
--                 → (ind : IndexLL rll ll) → (hitsAtLeastOnce s ind)
-- compl≡∅⇒ho ↓ ceq ind = hitsAtLeastOnce↓
-- compl≡∅⇒ho (s ←∧) ceq ind with complLₛ s
-- compl≡∅⇒ho (s ←∧) () ind | ∅
-- compl≡∅⇒ho (s ←∧) () ind | ¬∅ x
-- compl≡∅⇒ho (∧→ s) ceq ind with complLₛ s
-- compl≡∅⇒ho (∧→ s) () ind | ∅
-- compl≡∅⇒ho (∧→ s) () ind | ¬∅ x
-- compl≡∅⇒ho (s ←∧→ s₁) ceq ind with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
-- compl≡∅⇒ho (s ←∧→ s₁) ceq ↓ | ∅ | [ eq ] | ∅ | [ eq₁ ] = hitsAtLeastOnce←∧→↓
-- compl≡∅⇒ho (s ←∧→ s₁) ceq (ind ←∧) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s eq ind
-- ... | r = hitsAtLeastOnce←∧→←∧ r
-- compl≡∅⇒ho (s ←∧→ s₁) ceq (∧→ ind) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s₁ eq₁ ind
-- ... | r = hitsAtLeastOnce←∧→∧→ r
-- compl≡∅⇒ho (s ←∧→ s₁) () ind | ∅ | [ eq ] | ¬∅ x | [ eq₁ ]
-- compl≡∅⇒ho (s ←∧→ s₁) () ind | ¬∅ x | [ eq ] | ∅ | [ eq₁ ]
-- compl≡∅⇒ho (s ←∧→ s₁) () ind | ¬∅ x | [ eq ] | ¬∅ x₁ | [ eq₁ ]
-- compl≡∅⇒ho (s ←∨) ceq ind with complLₛ s
-- compl≡∅⇒ho (s ←∨) () ind | ∅
-- compl≡∅⇒ho (s ←∨) () ind | ¬∅ x
-- compl≡∅⇒ho (∨→ s) ceq ind with complLₛ s
-- compl≡∅⇒ho (∨→ s) () ind | ∅
-- compl≡∅⇒ho (∨→ s) () ind | ¬∅ x
-- compl≡∅⇒ho (s ←∨→ s₁) ceq ind with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
-- compl≡∅⇒ho (s ←∨→ s₁) ceq ↓ | ∅ | [ eq ] | ∅ | [ eq₁ ] = hitsAtLeastOnce←∨→↓
-- compl≡∅⇒ho (s ←∨→ s₁) ceq (ind ←∨) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s eq ind
-- ... | r = hitsAtLeastOnce←∨→←∨ r
-- compl≡∅⇒ho (s ←∨→ s₁) ceq (∨→ ind) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s₁ eq₁ ind
-- ... | r = hitsAtLeastOnce←∨→∨→ r
-- compl≡∅⇒ho (s ←∨→ s₁) () ind | ∅ | [ eq ] | ¬∅ x | [ eq₁ ]
-- compl≡∅⇒ho (s ←∨→ s₁) () ind | ¬∅ x | [ eq ] | ∅ | [ eq₁ ]
-- compl≡∅⇒ho (s ←∨→ s₁) () ind | ¬∅ x | [ eq ] | ¬∅ x₁ | [ eq₁ ]
-- compl≡∅⇒ho (s ←∂) ceq ind with complLₛ s
-- compl≡∅⇒ho (s ←∂) () ind | ∅
-- compl≡∅⇒ho (s ←∂) () ind | ¬∅ x
-- compl≡∅⇒ho (∂→ s) ceq ind with complLₛ s
-- compl≡∅⇒ho (∂→ s) () ind | ∅
-- compl≡∅⇒ho (∂→ s) () ind | ¬∅ x
-- compl≡∅⇒ho (s ←∂→ s₁) ceq ind with complLₛ s | inspect complLₛ s | complLₛ s₁ | inspect complLₛ s₁
-- compl≡∅⇒ho (s ←∂→ s₁) ceq ↓ | ∅ | [ eq ] | ∅ | [ eq₁ ] = hitsAtLeastOnce←∂→↓
-- compl≡∅⇒ho (s ←∂→ s₁) ceq (ind ←∂) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s eq ind
-- ... | r = hitsAtLeastOnce←∂→←∂ r
-- compl≡∅⇒ho (s ←∂→ s₁) ceq (∂→ ind) | ∅ | [ eq ] | ∅ | [ eq₁ ] with compl≡∅⇒ho s₁ eq₁ ind
-- ... | r = hitsAtLeastOnce←∂→∂→ r
-- compl≡∅⇒ho (s ←∂→ s₁) () ind | ∅ | [ eq ] | ¬∅ x | [ eq₁ ]
-- compl≡∅⇒ho (s ←∂→ s₁) () ind | ¬∅ x | [ eq ] | ∅ | [ eq₁ ]
-- compl≡∅⇒ho (s ←∂→ s₁) () ind | ¬∅ x | [ eq ] | ¬∅ x₁ | [ eq₁ ]













--   ¬ho⇒¬del≡∅ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → ¬(hitsAtLeastOnce s ind) → ¬ (del s ind fll ≡ ∅)
--   ¬ho⇒¬del≡∅ ↓ ↓ heq = λ _ → heq hitsAtLeastOnce↓
--   ¬ho⇒¬del≡∅ (x ←∧) ↓ heq = λ _ → heq hitsAtLeastOnce←∧↓
--   ¬ho⇒¬del≡∅ (∧→ x) ↓ heq = λ _ → heq hitsAtLeastOnce∧→↓
--   ¬ho⇒¬del≡∅ (x ←∧→ x₁) ↓ heq = λ _ → heq hitsAtLeastOnce←∧→↓
--   ¬ho⇒¬del≡∅ (x ←∨) ↓ heq = λ _ → heq hitsAtLeastOnce←∨↓
--   ¬ho⇒¬del≡∅ (∨→ x) ↓ heq = λ _ → heq hitsAtLeastOnce∨→↓
--   ¬ho⇒¬del≡∅ (x ←∨→ x₁) ↓ heq = λ _ → heq hitsAtLeastOnce←∨→↓
--   ¬ho⇒¬del≡∅ (x ←∂) ↓ heq = λ _ → heq hitsAtLeastOnce←∂↓
--   ¬ho⇒¬del≡∅ (∂→ x) ↓ heq = λ _ → heq hitsAtLeastOnce∂→↓
--   ¬ho⇒¬del≡∅ (x ←∂→ x₁) ↓ heq = λ _ → heq hitsAtLeastOnce←∂→↓
--   ¬ho⇒¬del≡∅ ↓ (ind ←∧) heq = λ _ → heq hitsAtLeastOnce↓
--   ¬ho⇒¬del≡∅ {fll = fll} (s ←∧) (ind ←∧) heq with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∧←∧ x) })
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()
--   ¬ho⇒¬del≡∅ (∧→ s) (ind ←∧) heq = λ ()
--   ¬ho⇒¬del≡∅ {fll = fll} (s ←∧→ s₁) (ind ←∧) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∧→←∧ x)})
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()
--   ¬ho⇒¬del≡∅ ↓ (∧→ ind) heq = λ _ → heq hitsAtLeastOnce↓
--   ¬ho⇒¬del≡∅ (s ←∧) (∧→ ind) heq = λ ()
--   ¬ho⇒¬del≡∅ {fll = fll} (∧→ s) (∧→ ind) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce∧→∧→ x) })
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()
--   ¬ho⇒¬del≡∅ {fll = fll} (s ←∧→ s₁) (∧→ ind) heq with del s₁ ind fll | ¬ho⇒¬del≡∅ {fll = fll} s₁ ind (λ {x → heq (hitsAtLeastOnce←∧→∧→ x)})
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()
--   ¬ho⇒¬del≡∅ ↓ (ind ←∨) heq = λ _ → heq hitsAtLeastOnce↓
--   ¬ho⇒¬del≡∅ {fll = fll} (s ←∨) (ind ←∨) heq with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∨←∨ x) })
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()
--   ¬ho⇒¬del≡∅ (∨→ s) (ind ←∨) heq = λ ()
--   ¬ho⇒¬del≡∅ {fll = fll} (s ←∨→ s₁) (ind ←∨) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∨→←∨ x)})
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()
--   ¬ho⇒¬del≡∅ ↓ (∨→ ind) heq = λ _ → heq hitsAtLeastOnce↓
--   ¬ho⇒¬del≡∅ (s ←∨) (∨→ ind) heq = λ ()
--   ¬ho⇒¬del≡∅ {fll = fll} (∨→ s) (∨→ ind) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce∨→∨→ x) })
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()
--   ¬ho⇒¬del≡∅ {fll = fll} (s ←∨→ s₁) (∨→ ind) heq with del s₁ ind fll | ¬ho⇒¬del≡∅ {fll = fll} s₁ ind (λ {x → heq (hitsAtLeastOnce←∨→∨→ x)})
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()
--   ¬ho⇒¬del≡∅ ↓ (ind ←∂) heq = λ _ → heq hitsAtLeastOnce↓
--   ¬ho⇒¬del≡∅ {fll = fll} (s ←∂) (ind ←∂) heq with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∂←∂ x) })
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()
--   ¬ho⇒¬del≡∅ (∂→ s) (ind ←∂) heq = λ ()
--   ¬ho⇒¬del≡∅ {fll = fll} (s ←∂→ s₁) (ind ←∂) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce←∂→←∂ x)})
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()
--   ¬ho⇒¬del≡∅ ↓ (∂→ ind) heq = λ _ → heq hitsAtLeastOnce↓
--   ¬ho⇒¬del≡∅ (s ←∂) (∂→ ind) heq = λ ()
--   ¬ho⇒¬del≡∅ {fll = fll} (∂→ s) (∂→ ind) heq  with del s ind fll | ¬ho⇒¬del≡∅ {fll = fll} s ind (λ {x → heq (hitsAtLeastOnce∂→∂→ x) })
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()
--   ¬ho⇒¬del≡∅ {fll = fll} (s ←∂→ s₁) (∂→ ind) heq with del s₁ ind fll | ¬ho⇒¬del≡∅ {fll = fll} s₁ ind (λ {x → heq (hitsAtLeastOnce←∂→∂→ x)})
--   ... | ∅ | r = λ _ → r refl
--   ... | ¬∅ x | r = λ ()



--   ¬ho⇒del≡¬∅ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → ¬(hitsAtLeastOnce s ind) → Σ (SetLL (replLL ll ind fll)) (λ z → del s ind fll ≡ ¬∅ z)
--   ¬ho⇒del≡¬∅ {fll = fll} s ind ¬ho with del s ind fll | inspect (del s ind) fll
--   ¬ho⇒del≡¬∅ {fll = fll} s ind ¬ho | ∅ | [ eq ] = ⊥-elim (¬ho⇒¬del≡∅ s ind ¬ho eq)
--   ¬ho⇒del≡¬∅ {fll = fll} s ind ¬ho | ¬∅ x | [ eq ] = x , refl



-- Already implemented the non-general case.

--   del⇒¬ho : ∀{i u pll ll tll} → (s : SetLL ll)
--       → (lind : IndexLL {i} {u} pll ll) → ∀{ds}
--       → ¬∅ ds ≡ del s lind tll
--       → ¬ (hitsAtLeastOnce ds (a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)))
--   del⇒¬ho {tll = tll} s ↓ ()
--   del⇒¬ho {tll = tll} ↓ (lind ←∧) eqd y with del ↓ lind tll | inspect (del ↓ lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (lind ←∧) refl y | ∅ | r with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {tll = tll} ↓ (lind ←∧) refl () | ∅ | r | g | e
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (lind ←∧) refl y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho ↓ lind {x} (sym eq)
--   del⇒¬ho {tll = tll} ↓ (lind ←∧) refl (hitsAtLeastOnce←∧→←∧ y) | ¬∅ x | [ eq ] | g | t | e = e y
--   del⇒¬ho {tll = tll} (s ←∧) (lind ←∧) eqd y with del s lind tll | inspect (del s lind) tll
--   del⇒¬ho {tll = tll} (s ←∧) (lind ←∧) () y | ∅ | r
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∧) (lind ←∧) refl y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s lind {x} (sym eq)
--   del⇒¬ho {tll = tll} (s ←∧) (lind ←∧) refl (hitsAtLeastOnce←∧←∧ y) | ¬∅ x | [ eq ] | g | e | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} (∧→ s) (lind ←∧) refl y with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} (∧→ s) (lind ←∧) refl () | r | g 
--   del⇒¬ho {tll = tll} (s ←∧→ s₁) (lind ←∧) eqd y with del s lind tll | inspect (del s lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∧→ s₁) (lind ←∧) eqd y | ∅ | e  with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {tll = tll} (s ←∧→ s₁) (lind ←∧) refl () | ∅ | e | g | r
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∧→ s₁) (lind ←∧) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s lind {x} (sym eq)
--   del⇒¬ho {tll = tll} (s ←∧→ s₁) (lind ←∧) refl (hitsAtLeastOnce←∧→←∧ y) | ¬∅ x | [ eq ] | g | e | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∧→ lind) eqd y with del ↓ lind tll | inspect (del ↓ lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∧→ lind) eqd y | ∅ | r with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∧→ lind) refl () | ∅ | r | e | t
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∧→ lind) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho ↓ lind {x} (sym eq)
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∧→ lind) refl (hitsAtLeastOnce←∧→∧→ y) | ¬∅ x | [ eq ] | e | g | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∧) (∧→ lind) refl y with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∧) (∧→ lind) refl () | g | e
--   del⇒¬ho {pll = pll} {tll = tll} (∧→ s) (∧→ lind) eqd y with del s lind tll | inspect (del s lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} (∧→ s) (∧→ lind) () y | ∅ | e
--   del⇒¬ho {pll = pll} {tll = tll} (∧→ s) (∧→ lind) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s lind {x} (sym eq)
--   del⇒¬ho {pll = pll} {tll = tll} (∧→ s) (∧→ lind) refl (hitsAtLeastOnce∧→∧→ y) | ¬∅ x | [ eq ] | g | e | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∧→ s₁) (∧→ lind) eqd y with del s₁ lind tll | inspect (del s₁ lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∧→ s₁) (∧→ lind) eqd y | ∅ | e with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∧→ s₁) (∧→ lind) refl () | ∅ | e | g | r
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∧→ s₁) (∧→ lind) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s₁ lind {x} (sym eq)
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∧→ s₁) (∧→ lind) refl (hitsAtLeastOnce←∧→∧→ y) | ¬∅ x | [ eq ] | g | e | t = t y
--   del⇒¬ho {tll = tll} ↓ (lind ←∨) eqd y with del ↓ lind tll | inspect (del ↓ lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (lind ←∨) refl y | ∅ | r with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {tll = tll} ↓ (lind ←∨) refl () | ∅ | r | g | e
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (lind ←∨) refl y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho ↓ lind {x} (sym eq)
--   del⇒¬ho {tll = tll} ↓ (lind ←∨) refl (hitsAtLeastOnce←∨→←∨ y) | ¬∅ x | [ eq ] | g | t | e = e y
--   del⇒¬ho {tll = tll} (s ←∨) (lind ←∨) eqd y with del s lind tll | inspect (del s lind) tll
--   del⇒¬ho {tll = tll} (s ←∨) (lind ←∨) () y | ∅ | r
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∨) (lind ←∨) refl y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s lind {x} (sym eq)
--   del⇒¬ho {tll = tll} (s ←∨) (lind ←∨) refl (hitsAtLeastOnce←∨←∨ y) | ¬∅ x | [ eq ] | g | e | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} (∨→ s) (lind ←∨) refl y with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} (∨→ s) (lind ←∨) refl () | r | g 
--   del⇒¬ho {tll = tll} (s ←∨→ s₁) (lind ←∨) eqd y with del s lind tll | inspect (del s lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∨→ s₁) (lind ←∨) eqd y | ∅ | e  with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {tll = tll} (s ←∨→ s₁) (lind ←∨) refl () | ∅ | e | g | r
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∨→ s₁) (lind ←∨) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s lind {x} (sym eq)
--   del⇒¬ho {tll = tll} (s ←∨→ s₁) (lind ←∨) refl (hitsAtLeastOnce←∨→←∨ y) | ¬∅ x | [ eq ] | g | e | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∨→ lind) eqd y with del ↓ lind tll | inspect (del ↓ lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∨→ lind) eqd y | ∅ | r with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∨→ lind) refl () | ∅ | r | e | t
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∨→ lind) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho ↓ lind {x} (sym eq)
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∨→ lind) refl (hitsAtLeastOnce←∨→∨→ y) | ¬∅ x | [ eq ] | e | g | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∨) (∨→ lind) refl y with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∨) (∨→ lind) refl () | g | e
--   del⇒¬ho {pll = pll} {tll = tll} (∨→ s) (∨→ lind) eqd y with del s lind tll | inspect (del s lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} (∨→ s) (∨→ lind) () y | ∅ | e
--   del⇒¬ho {pll = pll} {tll = tll} (∨→ s) (∨→ lind) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s lind {x} (sym eq)
--   del⇒¬ho {pll = pll} {tll = tll} (∨→ s) (∨→ lind) refl (hitsAtLeastOnce∨→∨→ y) | ¬∅ x | [ eq ] | g | e | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∨→ s₁) (∨→ lind) eqd y with del s₁ lind tll | inspect (del s₁ lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∨→ s₁) (∨→ lind) eqd y | ∅ | e with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∨→ s₁) (∨→ lind) refl () | ∅ | e | g | r
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∨→ s₁) (∨→ lind) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s₁ lind {x} (sym eq)
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∨→ s₁) (∨→ lind) refl (hitsAtLeastOnce←∨→∨→ y) | ¬∅ x | [ eq ] | g | e | t = t y
--   del⇒¬ho {tll = tll} ↓ (lind ←∂) eqd y with del ↓ lind tll | inspect (del ↓ lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (lind ←∂) refl y | ∅ | r with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {tll = tll} ↓ (lind ←∂) refl () | ∅ | r | g | e
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (lind ←∂) refl y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho ↓ lind {x} (sym eq)
--   del⇒¬ho {tll = tll} ↓ (lind ←∂) refl (hitsAtLeastOnce←∂→←∂ y) | ¬∅ x | [ eq ] | g | t | e = e y
--   del⇒¬ho {tll = tll} (s ←∂) (lind ←∂) eqd y with del s lind tll | inspect (del s lind) tll
--   del⇒¬ho {tll = tll} (s ←∂) (lind ←∂) () y | ∅ | r
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∂) (lind ←∂) refl y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s lind {x} (sym eq)
--   del⇒¬ho {tll = tll} (s ←∂) (lind ←∂) refl (hitsAtLeastOnce←∂←∂ y) | ¬∅ x | [ eq ] | g | e | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} (∂→ s) (lind ←∂) refl y with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} (∂→ s) (lind ←∂) refl () | r | g 
--   del⇒¬ho {tll = tll} (s ←∂→ s₁) (lind ←∂) eqd y with del s lind tll | inspect (del s lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∂→ s₁) (lind ←∂) eqd y | ∅ | e  with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {tll = tll} (s ←∂→ s₁) (lind ←∂) refl () | ∅ | e | g | r
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∂→ s₁) (lind ←∂) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s lind {x} (sym eq)
--   del⇒¬ho {tll = tll} (s ←∂→ s₁) (lind ←∂) refl (hitsAtLeastOnce←∂→←∂ y) | ¬∅ x | [ eq ] | g | e | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∂→ lind) eqd y with del ↓ lind tll | inspect (del ↓ lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∂→ lind) eqd y | ∅ | r with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∂→ lind) refl () | ∅ | r | e | t
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∂→ lind) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho ↓ lind {x} (sym eq)
--   del⇒¬ho {pll = pll} {tll = tll} ↓ (∂→ lind) refl (hitsAtLeastOnce←∂→∂→ y) | ¬∅ x | [ eq ] | e | g | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∂) (∂→ lind) refl y with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∂) (∂→ lind) refl () | g | e
--   del⇒¬ho {pll = pll} {tll = tll} (∂→ s) (∂→ lind) eqd y with del s lind tll | inspect (del s lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} (∂→ s) (∂→ lind) () y | ∅ | e
--   del⇒¬ho {pll = pll} {tll = tll} (∂→ s) (∂→ lind) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s lind {x} (sym eq)
--   del⇒¬ho {pll = pll} {tll = tll} (∂→ s) (∂→ lind) refl (hitsAtLeastOnce∂→∂→ y) | ¬∅ x | [ eq ] | g | e | t = t y
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∂→ s₁) (∂→ lind) eqd y with del s₁ lind tll | inspect (del s₁ lind) tll
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∂→ s₁) (∂→ lind) eqd y | ∅ | e with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind)
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∂→ s₁) (∂→ lind) refl () | ∅ | e | g | r
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∂→ s₁) (∂→ lind) eqd y | ¬∅ x | [ eq ] with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) tll | a≤ᵢb-morph lind lind tll (≤ᵢ-reflexive lind) | del⇒¬ho s₁ lind {x} (sym eq)
--   del⇒¬ho {pll = pll} {tll = tll} (s ←∂→ s₁) (∂→ lind) refl (hitsAtLeastOnce←∂→∂→ y) | ¬∅ x | [ eq ] | g | e | t = t y
  
  


--   trunc≡∅⇒¬mrpls≡∅ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → (truncSetLL s ind ≡ ∅) → ¬ (mreplacePartOf (¬∅ s) to (∅ {ll = fll}) at ind ≡ ∅)
--   trunc≡∅⇒¬mrpls≡∅ s ind treq = ¬ho⇒¬del≡∅ s ind (trunc≡∅⇒¬ho s ind treq)


--   ho⇒¬trunc≡∅ : ∀ {i u ll pll} → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
--                  → (prf : hitsAtLeastOnce s ind) → ¬ (truncSetLL s ind ≡ ∅)
--   ho⇒¬trunc≡∅ s ind prf x = trunc≡∅⇒¬ho s ind x prf




--   oi⇒¬trunc≡∅ : ∀ {i u ll pll} → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
--                  → (prf : onlyInside s ind) → ¬ (truncSetLL s ind ≡ ∅)
--   oi⇒¬trunc≡∅ s ind prf = ho⇒¬trunc≡∅ s ind (oi⇒ho s ind prf)





-- -- The ≤s relationship and hitsAtLeastOnce and onlyInside

--   oi&ss≤s⇒oiss : ∀ {i u ll pll} → (s ss : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
--                  → (oi : onlyInside s ind) → ss ≤s s → onlyInside ss ind
--   oi&ss≤s⇒oiss ↓ ss ↓ oi eq = onlyInsideCs↓
--   oi&ss≤s⇒oiss ↓ ss (x ←∧) () eq
--   oi&ss≤s⇒oiss ↓ ss (∧→ x) () eq
--   oi&ss≤s⇒oiss ↓ ss (x ←∨) () eq
--   oi&ss≤s⇒oiss ↓ ss (∨→ x) () eq
--   oi&ss≤s⇒oiss ↓ ss (x ←∂) () eq
--   oi&ss≤s⇒oiss ↓ ss (∂→ x) () eq
--   oi&ss≤s⇒oiss (s ←∧) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
--   oi&ss≤s⇒oiss (s ←∧) (sx ←∧) (ind ←∧) (onlyInsideC←∧←∧ x) (≤←∧ x₁) = onlyInsideC←∧←∧ (oi&ss≤s⇒oiss s sx ind x x₁)
--   oi&ss≤s⇒oiss (∧→ s) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
--   oi&ss≤s⇒oiss (∧→ s) (∧→ sx) (∧→ ind) (onlyInsideC∧→∧→ x) (≤∧→ x₁) = onlyInsideC∧→∧→ (oi&ss≤s⇒oiss s sx ind x x₁)
--   oi&ss≤s⇒oiss (s ←∧→ s₁) ss ↓ oi eq = onlyInsideCs↓
--   oi&ss≤s⇒oiss (s ←∧→ s₁) ss (x ←∧) () eq
--   oi&ss≤s⇒oiss (s ←∧→ s₁) ss (∧→ x) () eq
--   oi&ss≤s⇒oiss (s ←∨) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
--   oi&ss≤s⇒oiss (s ←∨) (sx ←∨) (ind ←∨) (onlyInsideC←∨←∨ x) (≤←∨ x₁) = onlyInsideC←∨←∨ (oi&ss≤s⇒oiss s sx ind x x₁)
--   oi&ss≤s⇒oiss (∨→ s) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
--   oi&ss≤s⇒oiss (∨→ s) (∨→ sx) (∨→ ind) (onlyInsideC∨→∨→ x) (≤∨→ x₁) = onlyInsideC∨→∨→ (oi&ss≤s⇒oiss s sx ind x x₁)
--   oi&ss≤s⇒oiss (s ←∨→ s₁) ss ↓ oi eq = onlyInsideCs↓
--   oi&ss≤s⇒oiss (s ←∨→ s₁) ss (x ←∨) () eq
--   oi&ss≤s⇒oiss (s ←∨→ s₁) ss (∨→ x) () eq
--   oi&ss≤s⇒oiss (s ←∂) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
--   oi&ss≤s⇒oiss (s ←∂) (sx ←∂) (ind ←∂) (onlyInsideC←∂←∂ x) (≤←∂ x₁) = onlyInsideC←∂←∂ (oi&ss≤s⇒oiss s sx ind x x₁)
--   oi&ss≤s⇒oiss (∂→ s) ss .↓ onlyInsideCs↓ eq = onlyInsideCs↓
--   oi&ss≤s⇒oiss (∂→ s) (∂→ sx) (∂→ ind) (onlyInsideC∂→∂→ x) (≤∂→ x₁) = onlyInsideC∂→∂→ (oi&ss≤s⇒oiss s sx ind x x₁)
--   oi&ss≤s⇒oiss (s ←∂→ s₁) ss ↓ oi eq = onlyInsideCs↓
--   oi&ss≤s⇒oiss (s ←∂→ s₁) ss (x ←∂) () eq
--   oi&ss≤s⇒oiss (s ←∂→ s₁) ss (∂→ x) () eq


--   ho&s≤ss⇒hoss : ∀ {i u ll pll} → (s ss : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
--                  → (ho : hitsAtLeastOnce s ind) → s ≤s ss → hitsAtLeastOnce ss ind
--   ho&s≤ss⇒hoss ↓ ↓ ind ho eq = ho
--   ho&s≤ss⇒hoss ↓ (x ←∧) ind ho ()
--   ho&s≤ss⇒hoss ↓ (∧→ x) ind ho ()
--   ho&s≤ss⇒hoss ↓ (x ←∧→ x₁) ind ho ()
--   ho&s≤ss⇒hoss ↓ (x ←∨) ind ho ()
--   ho&s≤ss⇒hoss ↓ (∨→ x) ind ho ()
--   ho&s≤ss⇒hoss ↓ (x ←∨→ x₁) ind ho ()
--   ho&s≤ss⇒hoss ↓ (x ←∂) ind ho ()
--   ho&s≤ss⇒hoss ↓ (∂→ x) ind ho ()
--   ho&s≤ss⇒hoss ↓ (x ←∂→ x₁) ind ho ()
--   ho&s≤ss⇒hoss (s ←∧) ↓ ind ho eq = hitsAtLeastOnce↓
--   ho&s≤ss⇒hoss (s ←∧) (x ←∧) .↓ hitsAtLeastOnce←∧↓ eq = hitsAtLeastOnce←∧↓
--   ho&s≤ss⇒hoss (s ←∧) (x ←∧) (ind ←∧) (hitsAtLeastOnce←∧←∧ x₁) (≤←∧ x₂) = hitsAtLeastOnce←∧←∧ (ho&s≤ss⇒hoss s x ind x₁ x₂)
--   ho&s≤ss⇒hoss (s ←∧) (∧→ ↓) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ ↓) (x ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ ↓) (∧→ x) () eq
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧)) (∧→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (∧→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (∧→ x)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (∧→ x)) (∧→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧→ x₁)) (x₂ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∧→ x₁)) (∧→ x₂) () eq
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨)) (∧→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (∨→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (∨→ x)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (∨→ x)) (∧→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨→ x₁)) (x₂ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∨→ x₁)) (∧→ x₂) () eq
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂)) (∧→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (∂→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (∂→ x)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (∂→ x)) (∧→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂→ x₁)) (x₂ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧) (∧→ (x ←∂→ x₁)) (∧→ x₂) () eq
--   ho&s≤ss⇒hoss (s ←∧) (x ←∧→ x₁) .↓ hitsAtLeastOnce←∧↓ eq = hitsAtLeastOnce←∧→↓
--   ho&s≤ss⇒hoss (s ←∧) (x ←∧→ x₁) (ind ←∧) (hitsAtLeastOnce←∧←∧ x₂) (≤d←∧ x₃) = hitsAtLeastOnce←∧→←∧ (ho&s≤ss⇒hoss s x ind x₂ x₃)
--   ho&s≤ss⇒hoss (∧→ s) ↓ ind ho eq = hitsAtLeastOnce↓
--   ho&s≤ss⇒hoss (∧→ s) (↓ ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (∧→ s) (↓ ←∧) (x ←∧) () eq
--   ho&s≤ss⇒hoss (∧→ s) (↓ ←∧) (∧→ x) ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∧) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∧) ←∧) (x₁ ←∧) () eq
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∧) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((∧→ x) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((∧→ x) ←∧) (x₁ ←∧) () eq
--   ho&s≤ss⇒hoss (∧→ s) ((∧→ x) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∧→ x₁) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∧→ x₁) ←∧) (x₂ ←∧) () eq
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∧→ x₁) ←∧) (∧→ x₂) ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∨) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∨) ←∧) (x₁ ←∧) () eq
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∨) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((∨→ x) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((∨→ x) ←∧) (x₁ ←∧) () eq
--   ho&s≤ss⇒hoss (∧→ s) ((∨→ x) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∨→ x₁) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∨→ x₁) ←∧) (x₂ ←∧) () eq
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∨→ x₁) ←∧) (∧→ x₂) ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∂) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∂) ←∧) (x₁ ←∧) () eq
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∂) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((∂→ x) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((∂→ x) ←∧) (x₁ ←∧) () eq
--   ho&s≤ss⇒hoss (∧→ s) ((∂→ x) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∂→ x₁) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∂→ x₁) ←∧) (x₂ ←∧) () eq
--   ho&s≤ss⇒hoss (∧→ s) ((x ←∂→ x₁) ←∧) (∧→ x₂) ho ()
--   ho&s≤ss⇒hoss (∧→ s) (∧→ x) .↓ hitsAtLeastOnce∧→↓ eq = hitsAtLeastOnce∧→↓
--   ho&s≤ss⇒hoss (∧→ s) (∧→ x) (∧→ ind) (hitsAtLeastOnce∧→∧→ x₁) (≤∧→ x₂) = hitsAtLeastOnce∧→∧→ (ho&s≤ss⇒hoss s x ind x₁ x₂)
--   ho&s≤ss⇒hoss (∧→ s) (x ←∧→ x₁) .↓ hitsAtLeastOnce∧→↓ eq = hitsAtLeastOnce←∧→↓
--   ho&s≤ss⇒hoss (∧→ s) (x ←∧→ x₁) (∧→ ind) (hitsAtLeastOnce∧→∧→ x₂) (≤d∧→ x₃) = hitsAtLeastOnce←∧→∧→ (ho&s≤ss⇒hoss s x₁ ind x₂ x₃)
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ↓ ind ho eq = hitsAtLeastOnce↓
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (↓ ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (↓ ←∧) (x ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (↓ ←∧) (∧→ x) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧) ←∧) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((∧→ x) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((∧→ x) ←∧) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((∧→ x) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧→ x₁) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧→ x₁) ←∧) (x₂ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∧→ x₁) ←∧) (∧→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨) ←∧) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((∨→ x) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((∨→ x) ←∧) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((∨→ x) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨→ x₁) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨→ x₁) ←∧) (x₂ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∨→ x₁) ←∧) (∧→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂) ←∧) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((∂→ x) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((∂→ x) ←∧) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((∂→ x) ←∧) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂→ x₁) ←∧) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂→ x₁) ←∧) (x₂ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) ((x ←∂→ x₁) ←∧) (∧→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ ↓) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ ↓) (x ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ ↓) (∧→ x) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧)) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∧→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∧→ x)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∧→ x)) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧→ x₁)) (x₂ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∧→ x₁)) (∧→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨)) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∨→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∨→ x)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∨→ x)) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨→ x₁)) (x₂ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∨→ x₁)) (∧→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂)) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∂→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∂→ x)) (x₁ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (∂→ x)) (∧→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂→ x₁)) (x₂ ←∧) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (∧→ (x ←∂→ x₁)) (∧→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (x ←∧→ x₁) .↓ hitsAtLeastOnce←∧→↓ eq = hitsAtLeastOnce←∧→↓
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (x ←∧→ x₁) (ind ←∧) (hitsAtLeastOnce←∧→←∧ x₂) (≤←∧→ x₃ x₄) = hitsAtLeastOnce←∧→←∧ (ho&s≤ss⇒hoss s x ind x₂ x₃)
--   ho&s≤ss⇒hoss (s ←∧→ s₁) (x ←∧→ x₁) (∧→ ind) (hitsAtLeastOnce←∧→∧→ x₂) (≤←∧→ x₃ x₄) = hitsAtLeastOnce←∧→∧→ (ho&s≤ss⇒hoss s₁ x₁ ind x₂ x₄)
--   ho&s≤ss⇒hoss (s ←∨) ↓ ind ho eq = hitsAtLeastOnce↓
--   ho&s≤ss⇒hoss (s ←∨) (x ←∨) .↓ hitsAtLeastOnce←∨↓ eq = hitsAtLeastOnce←∨↓
--   ho&s≤ss⇒hoss (s ←∨) (x ←∨) (ind ←∨) (hitsAtLeastOnce←∨←∨ x₁) (≤←∨ x₂) = hitsAtLeastOnce←∨←∨ (ho&s≤ss⇒hoss s x ind x₁ x₂)
--   ho&s≤ss⇒hoss (s ←∨) (∨→ ↓) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ ↓) (x ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ ↓) (∨→ x) () eq
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨)) (∨→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (∨→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (∨→ x)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (∨→ x)) (∨→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨→ x₁)) (x₂ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∨→ x₁)) (∨→ x₂) () eq
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧)) (∨→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (∧→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (∧→ x)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (∧→ x)) (∨→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧→ x₁)) (x₂ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∧→ x₁)) (∨→ x₂) () eq
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂)) (∨→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (∂→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (∂→ x)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (∂→ x)) (∨→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂→ x₁)) (x₂ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨) (∨→ (x ←∂→ x₁)) (∨→ x₂) () eq
--   ho&s≤ss⇒hoss (s ←∨) (x ←∨→ x₁) .↓ hitsAtLeastOnce←∨↓ eq = hitsAtLeastOnce←∨→↓
--   ho&s≤ss⇒hoss (s ←∨) (x ←∨→ x₁) (ind ←∨) (hitsAtLeastOnce←∨←∨ x₂) (≤d←∨ x₃) = hitsAtLeastOnce←∨→←∨ (ho&s≤ss⇒hoss s x ind x₂ x₃)
--   ho&s≤ss⇒hoss (∨→ s) ↓ ind ho eq = hitsAtLeastOnce↓
--   ho&s≤ss⇒hoss (∨→ s) (↓ ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (∨→ s) (↓ ←∨) (x ←∨) () eq
--   ho&s≤ss⇒hoss (∨→ s) (↓ ←∨) (∨→ x) ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∨) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∨) ←∨) (x₁ ←∨) () eq
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∨) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((∨→ x) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((∨→ x) ←∨) (x₁ ←∨) () eq
--   ho&s≤ss⇒hoss (∨→ s) ((∨→ x) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∨→ x₁) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∨→ x₁) ←∨) (x₂ ←∨) () eq
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∨→ x₁) ←∨) (∨→ x₂) ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∧) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∧) ←∨) (x₁ ←∨) () eq
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∧) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((∧→ x) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((∧→ x) ←∨) (x₁ ←∨) () eq
--   ho&s≤ss⇒hoss (∨→ s) ((∧→ x) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∧→ x₁) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∧→ x₁) ←∨) (x₂ ←∨) () eq
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∧→ x₁) ←∨) (∨→ x₂) ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∂) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∂) ←∨) (x₁ ←∨) () eq
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∂) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((∂→ x) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((∂→ x) ←∨) (x₁ ←∨) () eq
--   ho&s≤ss⇒hoss (∨→ s) ((∂→ x) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∂→ x₁) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∂→ x₁) ←∨) (x₂ ←∨) () eq
--   ho&s≤ss⇒hoss (∨→ s) ((x ←∂→ x₁) ←∨) (∨→ x₂) ho ()
--   ho&s≤ss⇒hoss (∨→ s) (∨→ x) .↓ hitsAtLeastOnce∨→↓ eq = hitsAtLeastOnce∨→↓
--   ho&s≤ss⇒hoss (∨→ s) (∨→ x) (∨→ ind) (hitsAtLeastOnce∨→∨→ x₁) (≤∨→ x₂) = hitsAtLeastOnce∨→∨→ (ho&s≤ss⇒hoss s x ind x₁ x₂)
--   ho&s≤ss⇒hoss (∨→ s) (x ←∨→ x₁) .↓ hitsAtLeastOnce∨→↓ eq = hitsAtLeastOnce←∨→↓
--   ho&s≤ss⇒hoss (∨→ s) (x ←∨→ x₁) (∨→ ind) (hitsAtLeastOnce∨→∨→ x₂) (≤d∨→ x₃) = hitsAtLeastOnce←∨→∨→ (ho&s≤ss⇒hoss s x₁ ind x₂ x₃)
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ↓ ind ho eq = hitsAtLeastOnce↓
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (↓ ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (↓ ←∨) (x ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (↓ ←∨) (∨→ x) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨) ←∨) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((∨→ x) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((∨→ x) ←∨) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((∨→ x) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨→ x₁) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨→ x₁) ←∨) (x₂ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∨→ x₁) ←∨) (∨→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧) ←∨) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((∧→ x) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((∧→ x) ←∨) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((∧→ x) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧→ x₁) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧→ x₁) ←∨) (x₂ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∧→ x₁) ←∨) (∨→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂) ←∨) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((∂→ x) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((∂→ x) ←∨) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((∂→ x) ←∨) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂→ x₁) ←∨) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂→ x₁) ←∨) (x₂ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) ((x ←∂→ x₁) ←∨) (∨→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ ↓) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ ↓) (x ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ ↓) (∨→ x) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨)) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∨→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∨→ x)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∨→ x)) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨→ x₁)) (x₂ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∨→ x₁)) (∨→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧)) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∧→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∧→ x)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∧→ x)) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧→ x₁)) (x₂ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∧→ x₁)) (∨→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂)) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∂→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∂→ x)) (x₁ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (∂→ x)) (∨→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂→ x₁)) (x₂ ←∨) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (∨→ (x ←∂→ x₁)) (∨→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (x ←∨→ x₁) .↓ hitsAtLeastOnce←∨→↓ eq = hitsAtLeastOnce←∨→↓
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (x ←∨→ x₁) (ind ←∨) (hitsAtLeastOnce←∨→←∨ x₂) (≤←∨→ x₃ x₄) = hitsAtLeastOnce←∨→←∨ (ho&s≤ss⇒hoss s x ind x₂ x₃)
--   ho&s≤ss⇒hoss (s ←∨→ s₁) (x ←∨→ x₁) (∨→ ind) (hitsAtLeastOnce←∨→∨→ x₂) (≤←∨→ x₃ x₄) = hitsAtLeastOnce←∨→∨→ (ho&s≤ss⇒hoss s₁ x₁ ind x₂ x₄)
--   ho&s≤ss⇒hoss (s ←∂) ↓ ind ho eq = hitsAtLeastOnce↓
--   ho&s≤ss⇒hoss (s ←∂) (x ←∂) .↓ hitsAtLeastOnce←∂↓ eq = hitsAtLeastOnce←∂↓
--   ho&s≤ss⇒hoss (s ←∂) (x ←∂) (ind ←∂) (hitsAtLeastOnce←∂←∂ x₁) (≤←∂ x₂) = hitsAtLeastOnce←∂←∂ (ho&s≤ss⇒hoss s x ind x₁ x₂)
--   ho&s≤ss⇒hoss (s ←∂) (∂→ ↓) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ ↓) (x ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ ↓) (∂→ x) () eq
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂)) (∂→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (∂→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (∂→ x)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (∂→ x)) (∂→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂→ x₁)) (x₂ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∂→ x₁)) (∂→ x₂) () eq
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨)) (∂→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (∨→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (∨→ x)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (∨→ x)) (∂→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨→ x₁)) (x₂ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∨→ x₁)) (∂→ x₂) () eq
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧)) (∂→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (∧→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (∧→ x)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (∧→ x)) (∂→ x₁) () eq
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧→ x₁)) (x₂ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂) (∂→ (x ←∧→ x₁)) (∂→ x₂) () eq
--   ho&s≤ss⇒hoss (s ←∂) (x ←∂→ x₁) .↓ hitsAtLeastOnce←∂↓ eq = hitsAtLeastOnce←∂→↓
--   ho&s≤ss⇒hoss (s ←∂) (x ←∂→ x₁) (ind ←∂) (hitsAtLeastOnce←∂←∂ x₂) (≤d←∂ x₃) = hitsAtLeastOnce←∂→←∂ (ho&s≤ss⇒hoss s x ind x₂ x₃)
--   ho&s≤ss⇒hoss (∂→ s) ↓ ind ho eq = hitsAtLeastOnce↓
--   ho&s≤ss⇒hoss (∂→ s) (↓ ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (∂→ s) (↓ ←∂) (x ←∂) () eq
--   ho&s≤ss⇒hoss (∂→ s) (↓ ←∂) (∂→ x) ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∂) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∂) ←∂) (x₁ ←∂) () eq
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∂) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((∂→ x) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((∂→ x) ←∂) (x₁ ←∂) () eq
--   ho&s≤ss⇒hoss (∂→ s) ((∂→ x) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∂→ x₁) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∂→ x₁) ←∂) (x₂ ←∂) () eq
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∂→ x₁) ←∂) (∂→ x₂) ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∨) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∨) ←∂) (x₁ ←∂) () eq
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∨) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((∨→ x) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((∨→ x) ←∂) (x₁ ←∂) () eq
--   ho&s≤ss⇒hoss (∂→ s) ((∨→ x) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∨→ x₁) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∨→ x₁) ←∂) (x₂ ←∂) () eq
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∨→ x₁) ←∂) (∂→ x₂) ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∧) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∧) ←∂) (x₁ ←∂) () eq
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∧) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((∧→ x) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((∧→ x) ←∂) (x₁ ←∂) () eq
--   ho&s≤ss⇒hoss (∂→ s) ((∧→ x) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∧→ x₁) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∧→ x₁) ←∂) (x₂ ←∂) () eq
--   ho&s≤ss⇒hoss (∂→ s) ((x ←∧→ x₁) ←∂) (∂→ x₂) ho ()
--   ho&s≤ss⇒hoss (∂→ s) (∂→ x) .↓ hitsAtLeastOnce∂→↓ eq = hitsAtLeastOnce∂→↓
--   ho&s≤ss⇒hoss (∂→ s) (∂→ x) (∂→ ind) (hitsAtLeastOnce∂→∂→ x₁) (≤∂→ x₂) = hitsAtLeastOnce∂→∂→ (ho&s≤ss⇒hoss s x ind x₁ x₂)
--   ho&s≤ss⇒hoss (∂→ s) (x ←∂→ x₁) .↓ hitsAtLeastOnce∂→↓ eq = hitsAtLeastOnce←∂→↓
--   ho&s≤ss⇒hoss (∂→ s) (x ←∂→ x₁) (∂→ ind) (hitsAtLeastOnce∂→∂→ x₂) (≤d∂→ x₃) = hitsAtLeastOnce←∂→∂→ (ho&s≤ss⇒hoss s x₁ ind x₂ x₃)
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ↓ ind ho eq = hitsAtLeastOnce↓
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (↓ ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (↓ ←∂) (x ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (↓ ←∂) (∂→ x) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂) ←∂) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((∂→ x) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((∂→ x) ←∂) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((∂→ x) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂→ x₁) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂→ x₁) ←∂) (x₂ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∂→ x₁) ←∂) (∂→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨) ←∂) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((∨→ x) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((∨→ x) ←∂) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((∨→ x) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨→ x₁) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨→ x₁) ←∂) (x₂ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∨→ x₁) ←∂) (∂→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧) ←∂) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((∧→ x) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((∧→ x) ←∂) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((∧→ x) ←∂) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧→ x₁) ←∂) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧→ x₁) ←∂) (x₂ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) ((x ←∧→ x₁) ←∂) (∂→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ ↓) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ ↓) (x ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ ↓) (∂→ x) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂)) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∂→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∂→ x)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∂→ x)) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂→ x₁)) (x₂ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∂→ x₁)) (∂→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨)) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∨→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∨→ x)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∨→ x)) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨→ x₁)) (x₂ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∨→ x₁)) (∂→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧)) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∧→ x)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∧→ x)) (x₁ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (∧→ x)) (∂→ x₁) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧→ x₁)) ↓ ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧→ x₁)) (x₂ ←∂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (∂→ (x ←∧→ x₁)) (∂→ x₂) ho ()
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (x ←∂→ x₁) .↓ hitsAtLeastOnce←∂→↓ eq = hitsAtLeastOnce←∂→↓
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (x ←∂→ x₁) (ind ←∂) (hitsAtLeastOnce←∂→←∂ x₂) (≤←∂→ x₃ x₄) = hitsAtLeastOnce←∂→←∂ (ho&s≤ss⇒hoss s x ind x₂ x₃)
--   ho&s≤ss⇒hoss (s ←∂→ s₁) (x ←∂→ x₁) (∂→ ind) (hitsAtLeastOnce←∂→∂→ x₂) (≤←∂→ x₃ x₄) = hitsAtLeastOnce←∂→∂→ (ho&s≤ss⇒hoss s₁ x₁ ind x₂ x₄)



--   ¬ho&s≤ss⇒¬hos : ∀ {i u ll pll} → (s ss : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
--                  → ¬ (hitsAtLeastOnce ss ind) → s ≤s ss → ¬ (hitsAtLeastOnce s ind)
--   ¬ho&s≤ss⇒¬hos s ss ind ¬ho rl x = ¬ho (ho&s≤ss⇒hoss s ss ind x rl)


  
--   ¬trho : ∀{i u ll pll rll} →  ∀ ltr → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
--           → ¬ (hitsAtLeastOnce s ind) → (ut : UpTran {rll = rll} ind ltr)
--           → ¬ (hitsAtLeastOnce (SetLL.tran s ltr) (IndexLLProp.tran ind ltr ut))
--   ¬trho I s ind ¬ho indI = ¬ho
--   ¬trho (∂c ltr) ↓ .(_ ←∂) ¬ho (←∂∂c ut) = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (∂c ltr) ↓ .(∂→ _) ¬ho (∂→∂c ut) = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (∂c ltr) (s ←∂) (ind ←∂) ¬ho (←∂∂c ut) = ¬trho ltr (∂→ s) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ s) (∂→ ind))
--     ¬nho (hitsAtLeastOnce∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂←∂ x)
--   ¬trho (∂c ltr) (s ←∂) (∂→ ind) ¬ho (∂→∂c ut) = ¬trho ltr (∂→ s) (ind ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ s) (ind ←∂))
--     ¬nho ()
--   ¬trho (∂c ltr) (∂→ s) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce∂→↓
--   ¬trho (∂c ltr) (∂→ s) (ind ←∂) ¬ho (←∂∂c ut) = ¬trho ltr (s ←∂) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (∂→ ind))
--     ¬nho ()
--   ¬trho (∂c ltr) (∂→ s) (∂→ ind) ¬ho (∂→∂c ut) = ¬trho ltr (s ←∂) (ind ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (ind ←∂))
--     ¬nho (hitsAtLeastOnce←∂←∂ x) = ¬ho (hitsAtLeastOnce∂→∂→ x)
--   ¬trho (∂c ltr) (s ←∂→ s₁) (ind ←∂) ¬ho (←∂∂c ut) = ¬trho ltr (s₁ ←∂→ s) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∂→ s) (∂→ ind))
--     ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
--   ¬trho (∂c ltr) (s ←∂→ s₁) (∂→ ind) ¬ho (∂→∂c ut)  = ¬trho ltr (s₁ ←∂→ s) (ind ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∂→ s) (ind ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
--   ¬trho (∧c ltr) ↓ .(_ ←∧) ¬ho (←∧∧c ut) = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (∧c ltr) ↓ .(∧→ _) ¬ho (∧→∧c ut) = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (∧c ltr) (s ←∧) (ind ←∧) ¬ho (←∧∧c ut) = ¬trho ltr (∧→ s) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ s) (∧→ ind))
--     ¬nho (hitsAtLeastOnce∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧←∧ x)
--   ¬trho (∧c ltr) (s ←∧) (∧→ ind) ¬ho (∧→∧c ut) = ¬trho ltr (∧→ s) (ind ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ s) (ind ←∧))
--     ¬nho ()
--   ¬trho (∧c ltr) (∧→ s) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce∧→↓
--   ¬trho (∧c ltr) (∧→ s) (ind ←∧) ¬ho (←∧∧c ut) = ¬trho ltr (s ←∧) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (∧→ ind))
--     ¬nho ()
--   ¬trho (∧c ltr) (∧→ s) (∧→ ind) ¬ho (∧→∧c ut) = ¬trho ltr (s ←∧) (ind ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (ind ←∧))
--     ¬nho (hitsAtLeastOnce←∧←∧ x) = ¬ho (hitsAtLeastOnce∧→∧→ x)
--   ¬trho (∧c ltr) (s ←∧→ s₁) (ind ←∧) ¬ho (←∧∧c ut) = ¬trho ltr (s₁ ←∧→ s) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∧→ s) (∧→ ind))
--     ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
--   ¬trho (∧c ltr) (s ←∧→ s₁) (∧→ ind) ¬ho (∧→∧c ut)  = ¬trho ltr (s₁ ←∧→ s) (ind ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∧→ s) (ind ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
--   ¬trho (∨c ltr) ↓ .(_ ←∨) ¬ho (←∨∨c ut) = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (∨c ltr) ↓ .(∨→ _) ¬ho (∨→∨c ut) = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (∨c ltr) (s ←∨) (ind ←∨) ¬ho (←∨∨c ut) = ¬trho ltr (∨→ s) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ s) (∨→ ind))
--     ¬nho (hitsAtLeastOnce∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨←∨ x)
--   ¬trho (∨c ltr) (s ←∨) (∨→ ind) ¬ho (∨→∨c ut) = ¬trho ltr (∨→ s) (ind ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ s) (ind ←∨))
--     ¬nho ()
--   ¬trho (∨c ltr) (∨→ s) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce∨→↓
--   ¬trho (∨c ltr) (∨→ s) (ind ←∨) ¬ho (←∨∨c ut) = ¬trho ltr (s ←∨) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (∨→ ind))
--     ¬nho ()
--   ¬trho (∨c ltr) (∨→ s) (∨→ ind) ¬ho (∨→∨c ut) = ¬trho ltr (s ←∨) (ind ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (ind ←∨))
--     ¬nho (hitsAtLeastOnce←∨←∨ x) = ¬ho (hitsAtLeastOnce∨→∨→ x)
--   ¬trho (∨c ltr) (s ←∨→ s₁) (ind ←∨) ¬ho (←∨∨c ut) = ¬trho ltr (s₁ ←∨→ s) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∨→ s) (∨→ ind))
--     ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
--   ¬trho (∨c ltr) (s ←∨→ s₁) (∨→ ind) ¬ho (∨→∨c ut)  = ¬trho ltr (s₁ ←∨→ s) (ind ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∨→ s) (ind ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
--   ¬trho (∧∧d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (∧∧d ltr) (↓ ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut)
--                                       = λ _ → ¬ho (hitsAtLeastOnce←∧←∧ hitsAtLeastOnce↓)
--   ¬trho (∧∧d ltr) ((s ←∧) ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (s ←∧) (ind ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (ind ←∧))
--     ¬nho (hitsAtLeastOnce←∧←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧←∧ x))
  
--   ¬trho (∧∧d ltr) ((∧→ s) ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut)  = ¬trho ltr (∧→ (s ←∧)) (ind ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧)) (ind ←∧))
--     ¬nho ()
  
--   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧)) (ind ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧)) (ind ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→←∧ x))
  
--   ¬trho (∧∧d ltr) (↓ ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = λ _ → ¬ho (hitsAtLeastOnce←∧←∧ hitsAtLeastOnce↓)
--   ¬trho (∧∧d ltr) ((s ←∧) ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧) (∧→ (ind ←∧)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (∧→ (ind ←∧)))
--     ¬nho ()
  
--   ¬trho (∧∧d ltr) ((∧→ s) ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (∧→ (s ←∧)) (∧→ (ind ←∧)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧)) (∧→ (ind ←∧)))
--     ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce∧→∧→ x))
  
--   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧)) (∧→ (ind ←∧)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧)) (∧→ (ind ←∧)))
--     ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→∧→ x))
  
--   ¬trho (∧∧d ltr) (↓ ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧)) (∧→ (∧→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧)) (∧→ (∧→ ind)))
--     ¬nho (hitsAtLeastOnce←∧→∧→ ())
  
--   ¬trho (∧∧d ltr) ((s ←∧) ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧) (∧→ (∧→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (∧→ (∧→ ind)))
--     ¬nho ()
  
--   ¬trho (∧∧d ltr) ((∧→ s) ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (∧→ (s ←∧)) (∧→ (∧→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧)) (∧→ (∧→ ind)))
--     ¬nho (hitsAtLeastOnce∧→∧→ ())
  
--   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧)) (∧→ (∧→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧)) (∧→ (∧→ ind)))
--     ¬nho (hitsAtLeastOnce←∧→∧→ ())
  
--   ¬trho (∧∧d ltr) (∧→ s) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (∧→ (∧→ s)) (ind ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ (∧→ s)) (ind ←∧))
--     ¬nho ()
  
--   ¬trho (∧∧d ltr) (∧→ s) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (∧→ (∧→ s)) (∧→ (ind ←∧)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ (∧→ s)) (∧→ (ind ←∧)))
--     ¬nho (hitsAtLeastOnce∧→∧→ ())
  
--   ¬trho (∧∧d ltr) (∧→ s) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (∧→ (∧→ s)) (∧→ (∧→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ (∧→ s)) (∧→ (∧→ ind)))
--     ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce∧→∧→ x)
  
  
  
--   ¬trho (∧∧d ltr) (↓ ←∧→ s₁) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧→ s₁)) (ind ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧→ s₁)) (ind ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓)
   
--   ¬trho (∧∧d ltr) ((s ←∧) ←∧→ s₁) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (∧→ s₁)) (ind ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (∧→ s₁)) (ind ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧←∧ x))
  
--   ¬trho (∧∧d ltr) ((∧→ s) ←∧→ s₁) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (∧→ (s ←∧→ s₁)) (ind ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧→ s₁)) (ind ←∧))
--     ¬nho ()
  
--   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧→ s₂) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut)  = ¬trho ltr (s ←∧→ (s₁ ←∧→ s₂)) (ind ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧→ s₂)) (ind ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ x))
  
  
--   ¬trho (∧∧d ltr) (↓ ←∧→ s₁) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (ind ←∧)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (ind ←∧)))
--     ¬nho x = ¬ho (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓)
   
--   ¬trho (∧∧d ltr) ((s ←∧) ←∧→ s₁) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (∧→ s₁)) (∧→ (ind ←∧)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (∧→ s₁)) (∧→ (ind ←∧)))
--     ¬nho (hitsAtLeastOnce←∧→∧→ ())
  
--   ¬trho (∧∧d ltr) ((∧→ s) ←∧→ s₁) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (∧→ (s ←∧→ s₁)) (∧→ (ind ←∧)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧→ s₁)) (∧→ (ind ←∧)))
--     ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce∧→∧→ x))
  
--   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧→ s₂) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (ind ←∧)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (ind ←∧)))
--     ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ x))
  
--   ¬trho (∧∧d ltr) (↓ ←∧→ s₁) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (∧→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (∧→ ind)))
--     ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
   
--   ¬trho (∧∧d ltr) ((s ←∧) ←∧→ s₁) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧→ (∧→ s₁)) (∧→ (∧→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (∧→ s₁)) (∧→ (∧→ ind)))
--     ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
--   ¬trho (∧∧d ltr) ((∧→ s) ←∧→ s₁) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (∧→ (s ←∧→ s₁)) (∧→ (∧→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧→ s₁)) (∧→ (∧→ ind)))
--     ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
--   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧→ s₂) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (∧→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (∧→ ind)))
--     ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
--   ¬trho (¬∧∧d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (¬∧∧d ltr) (s ←∧) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce←∧↓
--   ¬trho (¬∧∧d ltr) (s ←∧) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s ←∧) ←∧) ((ind ←∧) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s ←∧) ←∧) ((ind ←∧) ←∧))
--     ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧←∧ x)
  
--   ¬trho (¬∧∧d ltr) (s ←∧) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s ←∧) ←∧) ((∧→ ind) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s ←∧) ←∧) ((∧→ ind) ←∧))
--     ¬nho (hitsAtLeastOnce←∧←∧ ())
  
--   ¬trho (¬∧∧d ltr) (s ←∧) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s ←∧) ←∧) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s ←∧) ←∧) (∧→ ind))
--     ¬nho ()
  
--   ¬trho (¬∧∧d ltr) (∧→ ↓) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ ())
  
--   ¬trho (¬∧∧d ltr) (∧→ (s ←∧)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((∧→ s) ←∧) ((ind ←∧) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧) ((ind ←∧) ←∧))
--     ¬nho (hitsAtLeastOnce←∧←∧ ())
  
--   ¬trho (¬∧∧d ltr) (∧→ (∧→ s)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr (∧→ s) ((ind ←∧) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ s) ((ind ←∧) ←∧))
--     ¬nho ()
  
--   ¬trho (¬∧∧d ltr) (∧→ (s ←∧→ s₁)) (ind ←∧) ¬ho (←∧¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧→ s₁) ((ind ←∧) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧→ s₁) ((ind ←∧) ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ ())
  
  
--   ¬trho (¬∧∧d ltr) (∧→ ↓) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr ((∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧))
--     ¬nho x = ¬ho (hitsAtLeastOnce∧→∧→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∧∧d ltr) (∧→ (s ←∧)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧) ((∧→ ind) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧) ((∧→ ind) ←∧))
--     ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧←∧ x))
  
--   ¬trho (¬∧∧d ltr) (∧→ (∧→ s)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr (∧→ s) ((∧→ ind) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ s) ((∧→ ind) ←∧))
--     ¬nho ()
  
--   ¬trho (¬∧∧d ltr) (∧→ (s ←∧→ s₁)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧→ s₁) ((∧→ ind) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧→ s₁) ((∧→ ind) ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→←∧ x))
  
  
--   ¬trho (¬∧∧d ltr) (∧→ ↓) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut)   = ¬trho ltr ((∧→ ↓) ←∧→ ↓) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∧→ ↓) ←∧→ ↓) (∧→ ind))
--     ¬nho x = ¬ho (hitsAtLeastOnce∧→∧→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∧∧d ltr) (∧→ (s ←∧)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧) (∧→ ind))
--     ¬nho ()
  
--   ¬trho (¬∧∧d ltr) (∧→ (∧→ s)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr (∧→ s) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∧→ s) (∧→ ind))
--     ¬nho (hitsAtLeastOnce∧→∧→ x) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce∧→∧→ x))
  
--   ¬trho (¬∧∧d ltr) (∧→ (s ←∧→ s₁)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧→ s₁) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧→ s₁) (∧→ ind))
--     ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→∧→ x))
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ ↓) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧) ((ind ←∧) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧) ((ind ←∧) ←∧))
--     ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (∧→ s)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧) ←∧→ s) ((ind ←∧) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧) ←∧→ s) ((ind ←∧) ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧→ s₂)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧→ s₂) ((ind ←∧) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧→ s₂) ((ind ←∧) ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ ↓) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧))
--     ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧) ((∧→ ind) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧) ((∧→ ind) ←∧))
--     ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧←∧ x))
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (∧→ s)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧) ←∧→ s) ((∧→ ind) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧) ←∧→ s) ((∧→ ind) ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ ())
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧→ s₂)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧→ s₂) ((∧→ ind) ←∧) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧→ s₂) ((∧→ ind) ←∧))
--     ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ x))
  
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ ↓) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ ↓) ←∧→ ↓) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ ↓) ←∧→ ↓) (∧→ ind))
--     ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧) (∧→ ind))
--     ¬nho ()
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (∧→ s)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧) ←∧→ s) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧) ←∧→ s) (∧→ ind))
--     ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce∧→∧→ x))
  
--   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧→ s₂)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧→ s₂) (∧→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧→ s₂) (∧→ ind))
--     ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ x))
  
  
--   ¬trho (∨∨d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (∨∨d ltr) (↓ ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut)
--                                       = λ _ → ¬ho (hitsAtLeastOnce←∨←∨ hitsAtLeastOnce↓)
--   ¬trho (∨∨d ltr) ((s ←∨) ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (s ←∨) (ind ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (ind ←∨))
--     ¬nho (hitsAtLeastOnce←∨←∨ x) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨←∨ x))
  
--   ¬trho (∨∨d ltr) ((∨→ s) ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut)  = ¬trho ltr (∨→ (s ←∨)) (ind ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨)) (ind ←∨))
--     ¬nho ()
  
--   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨)) (ind ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨)) (ind ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→←∨ x))
  
--   ¬trho (∨∨d ltr) (↓ ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = λ _ → ¬ho (hitsAtLeastOnce←∨←∨ hitsAtLeastOnce↓)
--   ¬trho (∨∨d ltr) ((s ←∨) ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨) (∨→ (ind ←∨)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (∨→ (ind ←∨)))
--     ¬nho ()
  
--   ¬trho (∨∨d ltr) ((∨→ s) ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (∨→ (s ←∨)) (∨→ (ind ←∨)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨)) (∨→ (ind ←∨)))
--     ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce∨→∨→ x))
  
--   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨)) (∨→ (ind ←∨)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨)) (∨→ (ind ←∨)))
--     ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→∨→ x))
  
--   ¬trho (∨∨d ltr) (↓ ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨)) (∨→ (∨→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨)) (∨→ (∨→ ind)))
--     ¬nho (hitsAtLeastOnce←∨→∨→ ())
  
--   ¬trho (∨∨d ltr) ((s ←∨) ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨) (∨→ (∨→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (∨→ (∨→ ind)))
--     ¬nho ()
  
--   ¬trho (∨∨d ltr) ((∨→ s) ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (∨→ (s ←∨)) (∨→ (∨→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨)) (∨→ (∨→ ind)))
--     ¬nho (hitsAtLeastOnce∨→∨→ ())
  
--   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨)) (∨→ (∨→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨)) (∨→ (∨→ ind)))
--     ¬nho (hitsAtLeastOnce←∨→∨→ ())
  
--   ¬trho (∨∨d ltr) (∨→ s) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (∨→ (∨→ s)) (ind ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ (∨→ s)) (ind ←∨))
--     ¬nho ()
  
--   ¬trho (∨∨d ltr) (∨→ s) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (∨→ (∨→ s)) (∨→ (ind ←∨)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ (∨→ s)) (∨→ (ind ←∨)))
--     ¬nho (hitsAtLeastOnce∨→∨→ ())
  
--   ¬trho (∨∨d ltr) (∨→ s) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (∨→ (∨→ s)) (∨→ (∨→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ (∨→ s)) (∨→ (∨→ ind)))
--     ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce∨→∨→ x)
  
  
  
--   ¬trho (∨∨d ltr) (↓ ←∨→ s₁) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨→ s₁)) (ind ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨→ s₁)) (ind ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓)
   
--   ¬trho (∨∨d ltr) ((s ←∨) ←∨→ s₁) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (∨→ s₁)) (ind ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (∨→ s₁)) (ind ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨←∨ x))
  
--   ¬trho (∨∨d ltr) ((∨→ s) ←∨→ s₁) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (∨→ (s ←∨→ s₁)) (ind ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨→ s₁)) (ind ←∨))
--     ¬nho ()
  
--   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨→ s₂) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut)  = ¬trho ltr (s ←∨→ (s₁ ←∨→ s₂)) (ind ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨→ s₂)) (ind ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ x))
  
  
--   ¬trho (∨∨d ltr) (↓ ←∨→ s₁) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (ind ←∨)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (ind ←∨)))
--     ¬nho x = ¬ho (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓)
   
--   ¬trho (∨∨d ltr) ((s ←∨) ←∨→ s₁) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (∨→ s₁)) (∨→ (ind ←∨)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (∨→ s₁)) (∨→ (ind ←∨)))
--     ¬nho (hitsAtLeastOnce←∨→∨→ ())
  
--   ¬trho (∨∨d ltr) ((∨→ s) ←∨→ s₁) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (∨→ (s ←∨→ s₁)) (∨→ (ind ←∨)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨→ s₁)) (∨→ (ind ←∨)))
--     ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce∨→∨→ x))
  
--   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨→ s₂) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (ind ←∨)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (ind ←∨)))
--     ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ x))
  
--   ¬trho (∨∨d ltr) (↓ ←∨→ s₁) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (∨→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (∨→ ind)))
--     ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
   
--   ¬trho (∨∨d ltr) ((s ←∨) ←∨→ s₁) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨→ (∨→ s₁)) (∨→ (∨→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (∨→ s₁)) (∨→ (∨→ ind)))
--     ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
--   ¬trho (∨∨d ltr) ((∨→ s) ←∨→ s₁) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (∨→ (s ←∨→ s₁)) (∨→ (∨→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨→ s₁)) (∨→ (∨→ ind)))
--     ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
--   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨→ s₂) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (∨→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (∨→ ind)))
--     ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
--   ¬trho (¬∨∨d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (¬∨∨d ltr) (s ←∨) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce←∨↓
--   ¬trho (¬∨∨d ltr) (s ←∨) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s ←∨) ←∨) ((ind ←∨) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s ←∨) ←∨) ((ind ←∨) ←∨))
--     ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨←∨ x)
  
--   ¬trho (¬∨∨d ltr) (s ←∨) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s ←∨) ←∨) ((∨→ ind) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s ←∨) ←∨) ((∨→ ind) ←∨))
--     ¬nho (hitsAtLeastOnce←∨←∨ ())
  
--   ¬trho (¬∨∨d ltr) (s ←∨) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s ←∨) ←∨) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s ←∨) ←∨) (∨→ ind))
--     ¬nho ()
  
--   ¬trho (¬∨∨d ltr) (∨→ ↓) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ ())
  
--   ¬trho (¬∨∨d ltr) (∨→ (s ←∨)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((∨→ s) ←∨) ((ind ←∨) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨) ((ind ←∨) ←∨))
--     ¬nho (hitsAtLeastOnce←∨←∨ ())
  
--   ¬trho (¬∨∨d ltr) (∨→ (∨→ s)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr (∨→ s) ((ind ←∨) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ s) ((ind ←∨) ←∨))
--     ¬nho ()
  
--   ¬trho (¬∨∨d ltr) (∨→ (s ←∨→ s₁)) (ind ←∨) ¬ho (←∨¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨→ s₁) ((ind ←∨) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨→ s₁) ((ind ←∨) ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ ())
  
  
--   ¬trho (¬∨∨d ltr) (∨→ ↓) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr ((∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨))
--     ¬nho x = ¬ho (hitsAtLeastOnce∨→∨→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∨∨d ltr) (∨→ (s ←∨)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨) ((∨→ ind) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨) ((∨→ ind) ←∨))
--     ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨←∨ x))
  
--   ¬trho (¬∨∨d ltr) (∨→ (∨→ s)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr (∨→ s) ((∨→ ind) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ s) ((∨→ ind) ←∨))
--     ¬nho ()
  
--   ¬trho (¬∨∨d ltr) (∨→ (s ←∨→ s₁)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨→ s₁) ((∨→ ind) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨→ s₁) ((∨→ ind) ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→←∨ x))
  
  
--   ¬trho (¬∨∨d ltr) (∨→ ↓) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut)   = ¬trho ltr ((∨→ ↓) ←∨→ ↓) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∨→ ↓) ←∨→ ↓) (∨→ ind))
--     ¬nho x = ¬ho (hitsAtLeastOnce∨→∨→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∨∨d ltr) (∨→ (s ←∨)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨) (∨→ ind))
--     ¬nho ()
  
--   ¬trho (¬∨∨d ltr) (∨→ (∨→ s)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr (∨→ s) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∨→ s) (∨→ ind))
--     ¬nho (hitsAtLeastOnce∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce∨→∨→ x))
  
--   ¬trho (¬∨∨d ltr) (∨→ (s ←∨→ s₁)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨→ s₁) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨→ s₁) (∨→ ind))
--     ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→∨→ x))
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ ↓) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨) ((ind ←∨) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨) ((ind ←∨) ←∨))
--     ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (∨→ s)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨) ←∨→ s) ((ind ←∨) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨) ←∨→ s) ((ind ←∨) ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨→ s₂)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨→ s₂) ((ind ←∨) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨→ s₂) ((ind ←∨) ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ ↓) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨))
--     ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨) ((∨→ ind) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨) ((∨→ ind) ←∨))
--     ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨←∨ x))
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (∨→ s)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨) ←∨→ s) ((∨→ ind) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨) ←∨→ s) ((∨→ ind) ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ ())
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨→ s₂)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨→ s₂) ((∨→ ind) ←∨) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨→ s₂) ((∨→ ind) ←∨))
--     ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ x))
  
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ ↓) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ ↓) ←∨→ ↓) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ ↓) ←∨→ ↓) (∨→ ind))
--     ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨) (∨→ ind))
--     ¬nho ()
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (∨→ s)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨) ←∨→ s) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨) ←∨→ s) (∨→ ind))
--     ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce∨→∨→ x))
  
--   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨→ s₂)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨→ s₂) (∨→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨→ s₂) (∨→ ind))
--     ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ x))
  
  
--   ¬trho (∂∂d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (∂∂d ltr) (↓ ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut)
--                                       = λ _ → ¬ho (hitsAtLeastOnce←∂←∂ hitsAtLeastOnce↓)
--   ¬trho (∂∂d ltr) ((s ←∂) ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (s ←∂) (ind ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (ind ←∂))
--     ¬nho (hitsAtLeastOnce←∂←∂ x) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂←∂ x))
  
--   ¬trho (∂∂d ltr) ((∂→ s) ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut)  = ¬trho ltr (∂→ (s ←∂)) (ind ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂)) (ind ←∂))
--     ¬nho ()
  
--   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂)) (ind ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂)) (ind ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→←∂ x))
  
--   ¬trho (∂∂d ltr) (↓ ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = λ _ → ¬ho (hitsAtLeastOnce←∂←∂ hitsAtLeastOnce↓)
--   ¬trho (∂∂d ltr) ((s ←∂) ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂) (∂→ (ind ←∂)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (∂→ (ind ←∂)))
--     ¬nho ()
  
--   ¬trho (∂∂d ltr) ((∂→ s) ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (∂→ (s ←∂)) (∂→ (ind ←∂)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂)) (∂→ (ind ←∂)))
--     ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce∂→∂→ x))
  
--   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂)) (∂→ (ind ←∂)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂)) (∂→ (ind ←∂)))
--     ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→∂→ x))
  
--   ¬trho (∂∂d ltr) (↓ ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂)) (∂→ (∂→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂)) (∂→ (∂→ ind)))
--     ¬nho (hitsAtLeastOnce←∂→∂→ ())
  
--   ¬trho (∂∂d ltr) ((s ←∂) ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂) (∂→ (∂→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (∂→ (∂→ ind)))
--     ¬nho ()
  
--   ¬trho (∂∂d ltr) ((∂→ s) ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (∂→ (s ←∂)) (∂→ (∂→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂)) (∂→ (∂→ ind)))
--     ¬nho (hitsAtLeastOnce∂→∂→ ())
  
--   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂)) (∂→ (∂→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂)) (∂→ (∂→ ind)))
--     ¬nho (hitsAtLeastOnce←∂→∂→ ())
  
--   ¬trho (∂∂d ltr) (∂→ s) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (∂→ (∂→ s)) (ind ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ (∂→ s)) (ind ←∂))
--     ¬nho ()
  
--   ¬trho (∂∂d ltr) (∂→ s) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (∂→ (∂→ s)) (∂→ (ind ←∂)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ (∂→ s)) (∂→ (ind ←∂)))
--     ¬nho (hitsAtLeastOnce∂→∂→ ())
  
--   ¬trho (∂∂d ltr) (∂→ s) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (∂→ (∂→ s)) (∂→ (∂→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ (∂→ s)) (∂→ (∂→ ind)))
--     ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce∂→∂→ x)
  
  
  
--   ¬trho (∂∂d ltr) (↓ ←∂→ s₁) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂→ s₁)) (ind ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂→ s₁)) (ind ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓)
   
--   ¬trho (∂∂d ltr) ((s ←∂) ←∂→ s₁) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (∂→ s₁)) (ind ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (∂→ s₁)) (ind ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂←∂ x))
  
--   ¬trho (∂∂d ltr) ((∂→ s) ←∂→ s₁) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (∂→ (s ←∂→ s₁)) (ind ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂→ s₁)) (ind ←∂))
--     ¬nho ()
  
--   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂→ s₂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut)  = ¬trho ltr (s ←∂→ (s₁ ←∂→ s₂)) (ind ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂→ s₂)) (ind ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ x))
  
  
--   ¬trho (∂∂d ltr) (↓ ←∂→ s₁) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (ind ←∂)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (ind ←∂)))
--     ¬nho x = ¬ho (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓)
   
--   ¬trho (∂∂d ltr) ((s ←∂) ←∂→ s₁) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (∂→ s₁)) (∂→ (ind ←∂)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (∂→ s₁)) (∂→ (ind ←∂)))
--     ¬nho (hitsAtLeastOnce←∂→∂→ ())
  
--   ¬trho (∂∂d ltr) ((∂→ s) ←∂→ s₁) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (∂→ (s ←∂→ s₁)) (∂→ (ind ←∂)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂→ s₁)) (∂→ (ind ←∂)))
--     ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce∂→∂→ x))
  
--   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂→ s₂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (ind ←∂)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (ind ←∂)))
--     ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ x))
  
--   ¬trho (∂∂d ltr) (↓ ←∂→ s₁) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (∂→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (∂→ ind)))
--     ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
   
--   ¬trho (∂∂d ltr) ((s ←∂) ←∂→ s₁) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂→ (∂→ s₁)) (∂→ (∂→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (∂→ s₁)) (∂→ (∂→ ind)))
--     ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
--   ¬trho (∂∂d ltr) ((∂→ s) ←∂→ s₁) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (∂→ (s ←∂→ s₁)) (∂→ (∂→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂→ s₁)) (∂→ (∂→ ind)))
--     ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
--   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂→ s₂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (∂→ ind)) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (∂→ ind)))
--     ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
--   ¬trho (¬∂∂d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬trho (¬∂∂d ltr) (s ←∂) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce←∂↓
--   ¬trho (¬∂∂d ltr) (s ←∂) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s ←∂) ←∂) ((ind ←∂) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s ←∂) ←∂) ((ind ←∂) ←∂))
--     ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂←∂ x)
  
--   ¬trho (¬∂∂d ltr) (s ←∂) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s ←∂) ←∂) ((∂→ ind) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s ←∂) ←∂) ((∂→ ind) ←∂))
--     ¬nho (hitsAtLeastOnce←∂←∂ ())
  
--   ¬trho (¬∂∂d ltr) (s ←∂) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s ←∂) ←∂) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s ←∂) ←∂) (∂→ ind))
--     ¬nho ()
  
--   ¬trho (¬∂∂d ltr) (∂→ ↓) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ ())
  
--   ¬trho (¬∂∂d ltr) (∂→ (s ←∂)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((∂→ s) ←∂) ((ind ←∂) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂) ((ind ←∂) ←∂))
--     ¬nho (hitsAtLeastOnce←∂←∂ ())
  
--   ¬trho (¬∂∂d ltr) (∂→ (∂→ s)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr (∂→ s) ((ind ←∂) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ s) ((ind ←∂) ←∂))
--     ¬nho ()
  
--   ¬trho (¬∂∂d ltr) (∂→ (s ←∂→ s₁)) (ind ←∂) ¬ho (←∂¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂→ s₁) ((ind ←∂) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂→ s₁) ((ind ←∂) ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ ())
  
  
--   ¬trho (¬∂∂d ltr) (∂→ ↓) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr ((∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂))
--     ¬nho x = ¬ho (hitsAtLeastOnce∂→∂→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∂∂d ltr) (∂→ (s ←∂)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂) ((∂→ ind) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂) ((∂→ ind) ←∂))
--     ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂←∂ x))
  
--   ¬trho (¬∂∂d ltr) (∂→ (∂→ s)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr (∂→ s) ((∂→ ind) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ s) ((∂→ ind) ←∂))
--     ¬nho ()
  
--   ¬trho (¬∂∂d ltr) (∂→ (s ←∂→ s₁)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂→ s₁) ((∂→ ind) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂→ s₁) ((∂→ ind) ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→←∂ x))
  
  
--   ¬trho (¬∂∂d ltr) (∂→ ↓) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut)   = ¬trho ltr ((∂→ ↓) ←∂→ ↓) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∂→ ↓) ←∂→ ↓) (∂→ ind))
--     ¬nho x = ¬ho (hitsAtLeastOnce∂→∂→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∂∂d ltr) (∂→ (s ←∂)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂) (∂→ ind))
--     ¬nho ()
  
--   ¬trho (¬∂∂d ltr) (∂→ (∂→ s)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr (∂→ s) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce (∂→ s) (∂→ ind))
--     ¬nho (hitsAtLeastOnce∂→∂→ x) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce∂→∂→ x))
  
--   ¬trho (¬∂∂d ltr) (∂→ (s ←∂→ s₁)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂→ s₁) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂→ s₁) (∂→ ind))
--     ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→∂→ x))
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ ↓) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂) ((ind ←∂) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂) ((ind ←∂) ←∂))
--     ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (∂→ s)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂) ←∂→ s) ((ind ←∂) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂) ←∂→ s) ((ind ←∂) ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂→ s₂)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂→ s₂) ((ind ←∂) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂→ s₂) ((ind ←∂) ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ ↓) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂))
--     ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂) ((∂→ ind) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂) ((∂→ ind) ←∂))
--     ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂←∂ x))
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (∂→ s)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂) ←∂→ s) ((∂→ ind) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂) ←∂→ s) ((∂→ ind) ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ ())
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂→ s₂)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂→ s₂) ((∂→ ind) ←∂) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂→ s₂) ((∂→ ind) ←∂))
--     ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ x))
  
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ ↓) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ ↓) ←∂→ ↓) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ ↓) ←∂→ ↓) (∂→ ind))
--     ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓)
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂) (∂→ ind))
--     ¬nho ()
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (∂→ s)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂) ←∂→ s) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂) ←∂→ s) (∂→ ind))
--     ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce∂→∂→ x))
  
--   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂→ s₂)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂→ s₂) (∂→ ind) ¬nho ut where
--     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂→ s₂) (∂→ ind))
--     ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ x))
  
  
  







-- -- Extending a set gives us onlyInside and hitsAtLeastOnce immediately because the rest is empty.

--   ext⇒oi : ∀{i u pll ll} → ∀ s → (ind : IndexLL {i} {u} pll ll)
--          → onlyInside (extend ind s) ind
--   ext⇒oi {pll = pll} {(li ∧ _)} s (ind ←∧)
--     with replLL li ind pll | replLL-id li ind pll refl | extendg ind s | ext⇒oi s ind 
--   ... | .li | refl | e | q = onlyInsideC←∧←∧ q
--   ext⇒oi {pll = pll} {(_ ∧ ri)} s (∧→ ind)
--     with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind s | ext⇒oi s ind 
--   ... | .ri | refl | e | q = onlyInsideC∧→∧→ q
--   ext⇒oi {pll = pll} {(li ∨ _)} s (ind ←∨)
--     with replLL li ind pll | replLL-id li ind pll refl | extendg ind s | ext⇒oi s ind 
--   ... | .li | refl | e | q = onlyInsideC←∨←∨ q
--   ext⇒oi {pll = pll} {(_ ∨ ri)} s (∨→ ind)
--     with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind s | ext⇒oi s ind 
--   ... | .ri | refl | e | q = onlyInsideC∨→∨→ q
--   ext⇒oi {pll = pll} {(li ∂ _)} s (ind ←∂)
--     with replLL li ind pll | replLL-id li ind pll refl | extendg ind s | ext⇒oi s ind 
--   ... | .li | refl | e | q = onlyInsideC←∂←∂ q
--   ext⇒oi {pll = pll} {(_ ∂ ri)} s (∂→ ind)
--     with replLL ri ind pll | replLL-id ri ind pll refl | extendg ind s | ext⇒oi s ind 
--   ... | .ri | refl | e | q = onlyInsideC∂→∂→ q
--   ext⇒oi s ↓ = onlyInsideCs↓

--   ext⇒ho : ∀{i u pll ll} → ∀ s → (ind : IndexLL {i} {u} pll ll)
--          → hitsAtLeastOnce (extend ind s) ind
--   ext⇒ho s ind = oi⇒ho (extend ind s) ind (ext⇒oi s ind)



--   ¬ho⇒ind+¬ho : ∀{i u pll rll ll} → (s : SetLL {i} {u} ll) → (ind : IndexLL pll ll)
--               → ¬ (hitsAtLeastOnce s ind) → (lind : IndexLL rll pll)
--               → ¬ (hitsAtLeastOnce s (ind +ᵢ lind))
--   ¬ho⇒ind+¬ho ↓ (ind ←∧) ¬ho lind x = ¬ho hitsAtLeastOnce↓
--   ¬ho⇒ind+¬ho (s ←∧) (ind ←∧) ¬ho lind (hitsAtLeastOnce←∧←∧ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∧←∧ z)) lind x
--   ¬ho⇒ind+¬ho (∧→ s) (ind ←∧) ¬ho lind ()
--   ¬ho⇒ind+¬ho (s ←∧→ s₁) (ind ←∧) ¬ho lind (hitsAtLeastOnce←∧→←∧ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∧→←∧ z)) lind x
--   ¬ho⇒ind+¬ho ↓ (∧→ ind) ¬ho lind x = ¬ho hitsAtLeastOnce↓
--   ¬ho⇒ind+¬ho (s ←∧) (∧→ ind) ¬ho lind ()
--   ¬ho⇒ind+¬ho (∧→ s) (∧→ ind) ¬ho lind (hitsAtLeastOnce∧→∧→ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∧→∧→ z)) lind x
--   ¬ho⇒ind+¬ho (s ←∧→ s₁) (∧→ ind) ¬ho lind (hitsAtLeastOnce←∧→∧→ x) = ¬ho⇒ind+¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∧→∧→ z)) lind x
--   ¬ho⇒ind+¬ho ↓ (ind ←∨) ¬ho lind x = ¬ho hitsAtLeastOnce↓
--   ¬ho⇒ind+¬ho (s ←∨) (ind ←∨) ¬ho lind (hitsAtLeastOnce←∨←∨ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∨←∨ z)) lind x
--   ¬ho⇒ind+¬ho (∨→ s) (ind ←∨) ¬ho lind ()
--   ¬ho⇒ind+¬ho (s ←∨→ s₁) (ind ←∨) ¬ho lind (hitsAtLeastOnce←∨→←∨ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∨→←∨ z)) lind x
--   ¬ho⇒ind+¬ho ↓ (∨→ ind) ¬ho lind x = ¬ho hitsAtLeastOnce↓
--   ¬ho⇒ind+¬ho (s ←∨) (∨→ ind) ¬ho lind ()
--   ¬ho⇒ind+¬ho (∨→ s) (∨→ ind) ¬ho lind (hitsAtLeastOnce∨→∨→ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∨→∨→ z)) lind x
--   ¬ho⇒ind+¬ho (s ←∨→ s₁) (∨→ ind) ¬ho lind (hitsAtLeastOnce←∨→∨→ x) = ¬ho⇒ind+¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∨→∨→ z)) lind x
--   ¬ho⇒ind+¬ho ↓ (ind ←∂) ¬ho lind x = ¬ho hitsAtLeastOnce↓
--   ¬ho⇒ind+¬ho (s ←∂) (ind ←∂) ¬ho lind (hitsAtLeastOnce←∂←∂ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∂←∂ z)) lind x
--   ¬ho⇒ind+¬ho (∂→ s) (ind ←∂) ¬ho lind ()
--   ¬ho⇒ind+¬ho (s ←∂→ s₁) (ind ←∂) ¬ho lind (hitsAtLeastOnce←∂→←∂ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∂→←∂ z)) lind x
--   ¬ho⇒ind+¬ho ↓ (∂→ ind) ¬ho lind x = ¬ho hitsAtLeastOnce↓
--   ¬ho⇒ind+¬ho (s ←∂) (∂→ ind) ¬ho lind ()
--   ¬ho⇒ind+¬ho (∂→ s) (∂→ ind) ¬ho lind (hitsAtLeastOnce∂→∂→ x) = ¬ho⇒ind+¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∂→∂→ z)) lind x
--   ¬ho⇒ind+¬ho (s ←∂→ s₁) (∂→ ind) ¬ho lind (hitsAtLeastOnce←∂→∂→ x) = ¬ho⇒ind+¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∂→∂→ z)) lind x
--   ¬ho⇒ind+¬ho ↓ ↓ ¬ho lind x = ¬ho hitsAtLeastOnce↓
--   ¬ho⇒ind+¬ho (x ←∧) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce←∧↓
--   ¬ho⇒ind+¬ho (∧→ x) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce∧→↓
--   ¬ho⇒ind+¬ho (x ←∧→ x₁) ↓ ¬ho lind x₂ = ¬ho hitsAtLeastOnce←∧→↓
--   ¬ho⇒ind+¬ho (x ←∨) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce←∨↓
--   ¬ho⇒ind+¬ho (∨→ x) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce∨→↓
--   ¬ho⇒ind+¬ho (x ←∨→ x₁) ↓ ¬ho lind x₂ = ¬ho hitsAtLeastOnce←∨→↓
--   ¬ho⇒ind+¬ho (x ←∂) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce←∂↓
--   ¬ho⇒ind+¬ho (∂→ x) ↓ ¬ho lind x₁ = ¬ho hitsAtLeastOnce∂→↓
--   ¬ho⇒ind+¬ho (x ←∂→ x₁) ↓ ¬ho lind x₂ = ¬ho hitsAtLeastOnce←∂→↓
  

























-- module _ where

--   ¬ord&ext⇒¬ho' : ∀{i u pll rll ll tll} → ∀ (s : SetLL tll) → (ind : IndexLL {i} {u} pll ll)
--         → (lind : IndexLL rll ll) → (nord : ¬ Orderedᵢ lind ind) → (fnord : ¬ Orderedᵢ ind lind)
--         → ¬ hitsAtLeastOnce (extendg ind s) (¬ord-morph lind ind tll fnord)
--   ¬ord&ext⇒¬ho' s ↓ lind nord _ = λ _ → nord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&ext⇒¬ho' s (ind ←∧) ↓ nord fnord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
--   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∧ ri} {tll} s (ind ←∧) (lind ←∧) nord fnord = hf where
  
--     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (SetLL (_ ∧ ri) ∋ (extendg ind s ←∧)) ((¬ord-morph lind ind tll (¬ord-spec fnord)) ←∧)
--     hf (hitsAtLeastOnce←∧←∧ x) = is x
  
--   ¬ord&ext⇒¬ho' s (ind ←∧) (∧→ lind) nord _ = λ ()
--   ¬ord&ext⇒¬ho' s (∧→ ind) ↓ nord _ = λ _ → nord (a≤ᵢb ≤ᵢ↓)
--   ¬ord&ext⇒¬ho' s (∧→ ind) (lind ←∧) nord _ = λ ()
--   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∧ ri} {tll} s (∧→ ind) (∧→ lind) nord fnord = hf where
  
--     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (SetLL (li ∧ _) ∋ (∧→ extendg ind s)) (∧→ (¬ord-morph lind ind tll (¬ord-spec fnord)))
--     hf (hitsAtLeastOnce∧→∧→ x) = is x
--   ¬ord&ext⇒¬ho' s (ind ←∨) ↓ nord _ = λ _ → nord (a≤ᵢb ≤ᵢ↓)
--   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∨ ri} {tll} s (ind ←∨) (lind ←∨) nord fnord = hf where
  
--     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (SetLL (_ ∨ ri) ∋ (extendg ind s ←∨)) ((¬ord-morph lind ind tll (¬ord-spec fnord)) ←∨)
--     hf (hitsAtLeastOnce←∨←∨ x) = is x
  
--   ¬ord&ext⇒¬ho' s (ind ←∨) (∨→ lind) nord _ = λ ()
--   ¬ord&ext⇒¬ho' s (∨→ ind) ↓ nord _ = λ _ → nord (a≤ᵢb ≤ᵢ↓)
--   ¬ord&ext⇒¬ho' s (∨→ ind) (lind ←∨) nord _ = λ ()
--   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∨ ri} {tll} s (∨→ ind) (∨→ lind) nord fnord = hf where
  
--     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (SetLL (li ∨ _) ∋ (∨→ extendg ind s)) (∨→ (¬ord-morph lind ind tll (¬ord-spec fnord)))
--     hf (hitsAtLeastOnce∨→∨→ x) = is x
  
--   ¬ord&ext⇒¬ho' s (ind ←∂) ↓ nord _ = λ _ → nord (a≤ᵢb ≤ᵢ↓)
--   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∂ ri} {tll} s (ind ←∂) (lind ←∂) nord fnord = hf where
  
--     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (SetLL (_ ∂ ri) ∋ (extendg ind s ←∂)) ((¬ord-morph lind ind tll (¬ord-spec fnord)) ←∂)
--     hf (hitsAtLeastOnce←∂←∂ x) = is x
  
--   ¬ord&ext⇒¬ho' s (ind ←∂) (∂→ lind) nord _ = λ ()
--   ¬ord&ext⇒¬ho' s (∂→ ind) ↓ nord _ = λ _ → nord (a≤ᵢb ≤ᵢ↓)
--   ¬ord&ext⇒¬ho' s (∂→ ind) (lind ←∂) nord _ = λ ()
--   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∂ ri} {tll} s (∂→ ind) (∂→ lind) nord fnord = hf where
  
--     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (SetLL (li ∂ _) ∋ (∂→ extendg ind s)) (∂→ (¬ord-morph lind ind tll (¬ord-spec fnord)))
--     hf (hitsAtLeastOnce∂→∂→ x) = is x
    
--   ¬ord&ext⇒¬ho : ∀{i u pll rll ll tll} → ∀ (s : SetLL tll) → (ind : IndexLL {i} {u} pll ll)
--           → (lind : IndexLL rll ll) → (nord : ¬ Orderedᵢ lind ind)
--           → ¬ hitsAtLeastOnce (extendg ind s) (¬ord-morph lind ind tll (flipNotOrdᵢ nord))
--   ¬ord&ext⇒¬ho s ind lind nord = ¬ord&ext⇒¬ho' s ind lind nord (flipNotOrdᵢ nord)



-- module _ where


--   ¬ord&¬ho-repl⇒¬ho' : ∀{i u rll pll ll tll} → (lind : IndexLL {i} {u} rll ll) → (s : SetLL ll) → ∀{rs : SetLL tll}
--         → ¬ (hitsAtLeastOnce s lind) → (ind : IndexLL pll ll)
--         → (nord : ¬ Orderedᵢ lind ind) → (fnord : ¬ Orderedᵢ ind lind)
--         → ¬ (hitsAtLeastOnce (replacePartOf s to rs at ind) (¬ord-morph lind ind tll fnord))
--   ¬ord&¬ho-repl⇒¬ho' ↓ s ¬ho ind ¬ord fnord = λ _ → ¬ord (a≤ᵢb ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧) {rs} ¬ho (ind ←∧) ¬ord fnord x
--                                    with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce←∧←∧ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧) {rs} ¬ho (ind ←∧) ¬ord fnord (hitsAtLeastOnce←∧←∧ x) | r = ⊥-elim (r x)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧) ¬ho (∧→ ind) ¬ord fnord (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ x)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (∧→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (lind ←∧) (∧→ s) {rs} ¬ho (ind ←∧) ¬ord fnord = hf where
    
--     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (extendg ind rs ←∧→ s) (¬ord-morph (lind ←∧) (ind ←∧) tll fnord)
--     hf (hitsAtLeastOnce←∧→←∧ x) = h1 x

--   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (∧→ s) ¬ho (∧→ ind) ¬ord fnord = λ ()
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧→ s₁) {rs} ¬ho (ind ←∧) ¬ord fnord (hitsAtLeastOnce←∧→←∧ x) = is x where
--     hf : ¬ hitsAtLeastOnce s lind
--     hf x = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
--     is = ¬ord&¬ho-repl⇒¬ho' lind s {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧→ s₁) {rs} ¬ho (∧→ ind) ¬ord fnord (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
--   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (s ←∧) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (s ←∧) ¬ho (ind ←∧) ¬ord fnord = λ ()
--   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (∧→ lind) (s ←∧) {rs} ¬ho (∧→ ind) ¬ord fnord = hf where
    
--     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (s ←∧→ extendg ind rs) (¬ord-morph (∧→ lind) (∧→ ind) tll (fnord))
--     hf (hitsAtLeastOnce←∧→∧→ x) = h1 x
  
--   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (∧→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (∧→ s) ¬ho (ind ←∧) ¬ord fnord (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce∧→∧→ x)
--   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (∧→ s) {rs} ¬ho (∧→ ind) ¬ord fnord x
--                              with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce∧→∧→ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
--   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (∧→ s) ¬ho (∧→ ind) ¬ord fnord (hitsAtLeastOnce∧→∧→ x) | r = r x
--   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (s ←∧→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) ¬ord fnord (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
--   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (s ←∧→ s₁) {rs} ¬ho (∧→ ind) ¬ord fnord (hitsAtLeastOnce←∧→∧→ x) = is x where
--     hf : ¬ hitsAtLeastOnce s₁ lind
--     hf x = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
--     is = ¬ord&¬ho-repl⇒¬ho' lind s₁ {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨) {rs} ¬ho (ind ←∨) ¬ord fnord x
--                                    with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce←∨←∨ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨) {rs} ¬ho (ind ←∨) ¬ord fnord (hitsAtLeastOnce←∨←∨ x) | r = ⊥-elim (r x)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨) ¬ho (∨→ ind) ¬ord fnord (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨←∨ x)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (∨→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (lind ←∨) (∨→ s) {rs} ¬ho (ind ←∨) ¬ord fnord = hf where
--     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (extendg ind rs ←∨→ s) (¬ord-morph (lind ←∨) (ind ←∨) tll (fnord))
--     hf (hitsAtLeastOnce←∨→←∨ x) = h1 x
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (∨→ s) ¬ho (∨→ ind) ¬ord fnord = λ ()
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨→ s₁) {rs} ¬ho (ind ←∨) ¬ord fnord (hitsAtLeastOnce←∨→←∨ x) = is x where
--     hf : ¬ hitsAtLeastOnce s lind
--     hf x = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
--     is = ¬ord&¬ho-repl⇒¬ho' lind s {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨→ s₁) {rs} ¬ho (∨→ ind) ¬ord fnord (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
--   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (s ←∨) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (s ←∨) ¬ho (ind ←∨) ¬ord fnord = λ ()
--   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (∨→ lind) (s ←∨) {rs} ¬ho (∨→ ind) ¬ord fnord = hf where
--     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (s ←∨→ extendg ind rs) (¬ord-morph (∨→ lind) (∨→ ind) tll (fnord))
--     hf (hitsAtLeastOnce←∨→∨→ x) = h1 x
  
--   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (∨→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (∨→ s) ¬ho (ind ←∨) ¬ord fnord (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ x)
--   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (∨→ s) {rs} ¬ho (∨→ ind) ¬ord fnord x
--                              with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce∨→∨→ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
--   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (∨→ s) ¬ho (∨→ ind) ¬ord fnord (hitsAtLeastOnce∨→∨→ x) | r = r x
--   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (s ←∨→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) ¬ord fnord (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
--   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (s ←∨→ s₁) {rs} ¬ho (∨→ ind) ¬ord fnord (hitsAtLeastOnce←∨→∨→ x) = is x where
--     hf : ¬ hitsAtLeastOnce s₁ lind
--     hf x = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
--     is = ¬ord&¬ho-repl⇒¬ho' lind s₁ {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂) {rs} ¬ho (ind ←∂) ¬ord fnord x
--                                    with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce←∂←∂ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂) {rs} ¬ho (ind ←∂) ¬ord fnord (hitsAtLeastOnce←∂←∂ x) | r = ⊥-elim (r x)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂) ¬ho (∂→ ind) ¬ord fnord (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂←∂ x)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (∂→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (lind ←∂) (∂→ s) {rs} ¬ho (ind ←∂) ¬ord fnord = hf where
--     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (extendg ind rs ←∂→ s) (¬ord-morph (lind ←∂) (ind ←∂) tll (fnord))
--     hf (hitsAtLeastOnce←∂→←∂ x) = h1 x
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (∂→ s) ¬ho (∂→ ind) ¬ord fnord = λ ()
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂→ s₁) {rs} ¬ho (ind ←∂) ¬ord fnord (hitsAtLeastOnce←∂→←∂ x) = is x where
--     hf : ¬ hitsAtLeastOnce s lind
--     hf x = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
--     is = ¬ord&¬ho-repl⇒¬ho' lind s {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
--   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂→ s₁) {rs} ¬ho (∂→ ind) ¬ord fnord (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
--   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (s ←∂) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (s ←∂) ¬ho (ind ←∂) ¬ord fnord = λ ()
--   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (∂→ lind) (s ←∂) {rs} ¬ho (∂→ ind) ¬ord fnord = hf where
    
--     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
--     hf : ¬ hitsAtLeastOnce (s ←∂→ extendg ind rs) (¬ord-morph (∂→ lind) (∂→ ind) tll (fnord))
--     hf (hitsAtLeastOnce←∂→∂→ x) = h1 x
  
--   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (∂→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (∂→ s) ¬ho (ind ←∂) ¬ord fnord (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce∂→∂→ x)
--   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (∂→ s) {rs} ¬ho (∂→ ind) ¬ord fnord x
--                              with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce∂→∂→ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
--   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (∂→ s) ¬ho (∂→ ind) ¬ord fnord (hitsAtLeastOnce∂→∂→ x) | r = r x
--   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (s ←∂→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) ¬ord fnord (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
--   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (s ←∂→ s₁) {rs} ¬ho (∂→ ind) ¬ord fnord (hitsAtLeastOnce←∂→∂→ x) = is x where
--     hf : ¬ hitsAtLeastOnce s₁ lind
--     hf x = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
--     is = ¬ord&¬ho-repl⇒¬ho' lind s₁ {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
  

--   ¬ord&¬ho-repl⇒¬ho : ∀{i u rll pll ll tll} → (lind : IndexLL {i} {u} rll ll) → (s : SetLL ll) → ∀{rs : SetLL tll}
--           → ¬ (hitsAtLeastOnce s lind) → (ind : IndexLL pll ll)
--           → (nord : ¬ Orderedᵢ lind ind)
--           → ¬ (hitsAtLeastOnce (replacePartOf s to rs at ind) (¬ord-morph lind ind tll (flipNotOrdᵢ nord)))
--   ¬ord&¬ho-repl⇒¬ho lind s ¬ho ind nord = ¬ord&¬ho-repl⇒¬ho' lind s ¬ho ind nord (flipNotOrdᵢ nord)


-- module _ where

--     -- Not being Ordered is only necessary to morph the type of the index. but this statement is true in general.
--   ¬ord&¬ho-del⇒¬ho' : ∀{i u rll pll ll tll} → (lind : IndexLL {i} {u} rll ll) → (s : SetLL ll)
--         → ¬ (hitsAtLeastOnce s lind) → (ind : IndexLL pll ll) → ∀{ds}
--         → (nord : ¬ Orderedᵢ lind ind) → (fnord : ¬ Orderedᵢ ind lind)
--         → ¬∅ ds ≡ del s ind tll
--         → ¬ (hitsAtLeastOnce ds (¬ord-morph lind ind tll fnord))
--   ¬ord&¬ho-del⇒¬ho' ↓ s ¬ho ind nord fnord eqd = λ _ → nord (a≤ᵢb ≤ᵢ↓)
--   ¬ord&¬ho-del⇒¬ho' (lind ←∧) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-del⇒¬ho' (lind ←∧) ↓ ¬ho (ind ←∧) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧) ¬ho (ind ←∧) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧) ¬ho (ind ←∧) nord fnord () y | ∅ | r
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧) ¬ho (ind ←∧) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
  
--     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
--   ¬ord&¬ho-del⇒¬ho' (lind ←∧) (∧→ s) ¬ho (ind ←∧) nord fnord refl = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord eqd with del s ind tll | inspect (del s ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord refl | ∅ | r = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
  
--     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
--   ¬ord&¬ho-del⇒¬ho' (lind ←∧) ↓ ¬ho (∧→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' (lind ←∧) (s ←∧) ¬ho (∧→ ind) nord fnord refl (hitsAtLeastOnce←∧←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ x)
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (∧→ s) ¬ho (∧→ ind) nord fnord eqd with del s ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (∧→ s) ¬ho (∧→ ind) nord fnord () | ∅
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (∧→ s) ¬ho (∧→ ind) nord fnord refl | ¬∅ x = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord eqd y with del s₁ ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∧→←∧ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∧→←∧ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' (∧→ lind) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-del⇒¬ho' (∧→ lind) ↓ ¬ho (ind ←∧) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧) ¬ho (ind ←∧) nord fnord eqd with del s ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧) ¬ho (ind ←∧) nord fnord () | ∅
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧) ¬ho (ind ←∧) nord fnord refl | ¬∅ x = λ ()
--   ¬ord&¬ho-del⇒¬ho' (∧→ lind) (∧→ s) ¬ho (ind ←∧) nord fnord refl y = ¬ho (hitsAtLeastOnce∧→∧→ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord eqd y with del s ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∧→∧→ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∧→∧→ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' (∧→ lind) ↓ ¬ho (∧→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' (∧→ lind) (s ←∧) ¬ho (∧→ ind) nord fnord refl = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (∧→ s) ¬ho (∧→ ind) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (∧→ s) ¬ho (∧→ ind) nord fnord () y | ∅ | r
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (∧→ s) ¬ho (∧→ ind) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
--     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord eqd with del s₁ ind tll | inspect (del s₁ ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord refl | ∅ | r =  λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
--     is =  ¬ord&¬ho-del⇒¬ho' lind s₁ (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
--   ¬ord&¬ho-del⇒¬ho' (lind ←∨) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-del⇒¬ho' (lind ←∨) ↓ ¬ho (ind ←∨) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨) ¬ho (ind ←∨) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨) ¬ho (ind ←∨) nord fnord () y | ∅ | r
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨) ¬ho (ind ←∨) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
--     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
--   ¬ord&¬ho-del⇒¬ho' (lind ←∨) (∨→ s) ¬ho (ind ←∨) nord fnord refl = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord eqd with del s ind tll | inspect (del s ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord refl | ∅ | r = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
--     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
--   ¬ord&¬ho-del⇒¬ho' (lind ←∨) ↓ ¬ho (∨→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' (lind ←∨) (s ←∨) ¬ho (∨→ ind) nord fnord refl x = ¬ho (hitsAtLeastOnce←∨←∨ (ho-spec x))
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (∨→ s) ¬ho (∨→ ind) nord fnord eqd with del s ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (∨→ s) ¬ho (∨→ ind) nord fnord () | ∅
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (∨→ s) ¬ho (∨→ ind) nord fnord refl | ¬∅ x = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord eqd y with del s₁ ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∨→←∨ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∨→←∨ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' (∨→ lind) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-del⇒¬ho' (∨→ lind) ↓ ¬ho (ind ←∨) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨) ¬ho (ind ←∨) nord fnord eqd with del s ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨) ¬ho (ind ←∨) nord fnord () | ∅
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨) ¬ho (ind ←∨) nord fnord refl | ¬∅ x = λ ()
--   ¬ord&¬ho-del⇒¬ho' (∨→ lind) (∨→ s) ¬ho (ind ←∨) nord fnord refl (hitsAtLeastOnce∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ x)
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord eqd y with del s ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∨→∨→ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∨→∨→ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' (∨→ lind) ↓ ¬ho (∨→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' (∨→ lind) (s ←∨) ¬ho (∨→ ind) nord fnord refl = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (∨→ s) ¬ho (∨→ ind) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (∨→ s) ¬ho (∨→ ind) nord fnord () y | ∅ | r
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (∨→ s) ¬ho (∨→ ind) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
--     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord eqd with del s₁ ind tll | inspect (del s₁ ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord refl | ∅ | r = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
--     is =  ¬ord&¬ho-del⇒¬ho' lind s₁ (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
--   ¬ord&¬ho-del⇒¬ho' (lind ←∂) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-del⇒¬ho' (lind ←∂) ↓ ¬ho (ind ←∂) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂) ¬ho (ind ←∂) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂) ¬ho (ind ←∂) nord fnord () y | ∅ | r
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂) ¬ho (ind ←∂) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
--     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
--   ¬ord&¬ho-del⇒¬ho' (lind ←∂) (∂→ s) ¬ho (ind ←∂) nord fnord refl = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord eqd with del s ind tll | inspect (del s ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord refl | ∅ | r = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
--     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
--   ¬ord&¬ho-del⇒¬ho' (lind ←∂) ↓ ¬ho (∂→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' (lind ←∂) (s ←∂) ¬ho (∂→ ind) nord fnord refl y = ¬ho (hitsAtLeastOnce←∂←∂ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (∂→ s) ¬ho (∂→ ind) nord fnord eqd with del s ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (∂→ s) ¬ho (∂→ ind) nord fnord () | ∅
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (∂→ s) ¬ho (∂→ ind) nord fnord refl | ¬∅ x = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord eqd y with del s₁ ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∂→←∂ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∂→←∂ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' (∂→ lind) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
--   ¬ord&¬ho-del⇒¬ho' (∂→ lind) ↓ ¬ho (ind ←∂) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂) ¬ho (ind ←∂) nord fnord eqd with del s ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂) ¬ho (ind ←∂) nord fnord () | ∅
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂) ¬ho (ind ←∂) nord fnord refl | ¬∅ x = λ ()
--   ¬ord&¬ho-del⇒¬ho' (∂→ lind) (∂→ s) ¬ho (ind ←∂) nord fnord refl y = ¬ho (hitsAtLeastOnce∂→∂→ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord eqd y with del s ind tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∂→∂→ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∂→∂→ (ho-spec y))
--   ¬ord&¬ho-del⇒¬ho' (∂→ lind) ↓ ¬ho (∂→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
--   ¬ord&¬ho-del⇒¬ho' (∂→ lind) (s ←∂) ¬ho (∂→ ind) nord fnord refl = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (∂→ s) ¬ho (∂→ ind) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (∂→ s) ¬ho (∂→ ind) nord fnord () y | ∅ | r
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (∂→ s) ¬ho (∂→ ind) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
--     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord eqd with del s₁ ind tll | inspect (del s₁ ind) tll
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord refl | ∅ | r = λ ()
--   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
--     is =  ¬ord&¬ho-del⇒¬ho' lind s₁ (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
--   ¬ord&¬ho-del⇒¬ho : ∀{i u rll pll ll tll} → (lind : IndexLL {i} {u} rll ll) → (s : SetLL ll)
--         → ¬ (hitsAtLeastOnce s lind) → (ind : IndexLL pll ll) → ∀{ds}
--         → (nord : ¬ Orderedᵢ lind ind)
--         → ¬∅ ds ≡ del s ind tll
--         → ¬ (hitsAtLeastOnce ds (¬ord-morph lind ind tll (flipNotOrdᵢ nord)))
--   ¬ord&¬ho-del⇒¬ho lind s ¬ho ind nord deq =  ¬ord&¬ho-del⇒¬ho' lind s ¬ho ind nord (flipNotOrdᵢ nord) deq



-- rl&¬ho-trunc⇒¬ho : ∀{i u pll rll ll x} → ∀ (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
--       → ¬ hitsAtLeastOnce s ind
--       → (lind : IndexLL rll ll) → (rl : lind ≤ᵢ ind)
--       → ¬∅ x ≡ truncSetLL s lind
--       → ¬ hitsAtLeastOnce x ((ind -ᵢ lind) rl)
-- rl&¬ho-trunc⇒¬ho s ind ¬ho ↓ ≤ᵢ↓ refl = ¬ho
-- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (lind ←∧) rl tc = ⊥-elim (¬ho hitsAtLeastOnce↓)
-- rl&¬ho-trunc⇒¬ho (s ←∧) ↓ ¬ho (lind ←∧) rl tc = λ _ → ¬ho hitsAtLeastOnce←∧↓
-- rl&¬ho-trunc⇒¬ho (s ←∧) (ind ←∧) ¬ho (lind ←∧) (≤ᵢ←∧ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∧←∧ z)) lind rl tc
-- rl&¬ho-trunc⇒¬ho (s ←∧) (∧→ ind) ¬ho (lind ←∧) () tc
-- rl&¬ho-trunc⇒¬ho (∧→ s) ind ¬ho (lind ←∧) rl ()
-- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) ↓ ¬ho (lind ←∧) rl tc = λ _ → ¬ho hitsAtLeastOnce←∧→↓
-- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) (ind ←∧) ¬ho (lind ←∧) (≤ᵢ←∧ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∧→←∧ z)) lind rl tc
-- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) (∧→ ind) ¬ho (lind ←∧) () tc
-- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (∧→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce↓
-- rl&¬ho-trunc⇒¬ho (s ←∧) ind ¬ho (∧→ lind) rl ()
-- rl&¬ho-trunc⇒¬ho (∧→ s) ↓ ¬ho (∧→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce∧→↓
-- rl&¬ho-trunc⇒¬ho (∧→ s) (ind ←∧) ¬ho (∧→ lind) () tc
-- rl&¬ho-trunc⇒¬ho (∧→ s) (∧→ ind) ¬ho (∧→ lind) (≤ᵢ∧→ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∧→∧→ z)) lind rl tc
-- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) ↓ ¬ho (∧→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce←∧→↓
-- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) (ind ←∧) ¬ho (∧→ lind) () tc
-- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) (∧→ ind) ¬ho (∧→ lind) (≤ᵢ∧→ rl) tc = rl&¬ho-trunc⇒¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∧→∧→ z)) lind rl tc
-- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (lind ←∨) rl tc = ⊥-elim (¬ho hitsAtLeastOnce↓)
-- rl&¬ho-trunc⇒¬ho (s ←∨) ↓ ¬ho (lind ←∨) rl tc = λ _ → ¬ho hitsAtLeastOnce←∨↓
-- rl&¬ho-trunc⇒¬ho (s ←∨) (ind ←∨) ¬ho (lind ←∨) (≤ᵢ←∨ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∨←∨ z)) lind rl tc
-- rl&¬ho-trunc⇒¬ho (s ←∨) (∨→ ind) ¬ho (lind ←∨) () tc
-- rl&¬ho-trunc⇒¬ho (∨→ s) ind ¬ho (lind ←∨) rl ()
-- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) ↓ ¬ho (lind ←∨) rl tc = λ _ → ¬ho hitsAtLeastOnce←∨→↓
-- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) (ind ←∨) ¬ho (lind ←∨) (≤ᵢ←∨ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∨→←∨ z)) lind rl tc
-- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) (∨→ ind) ¬ho (lind ←∨) () tc
-- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (∨→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce↓
-- rl&¬ho-trunc⇒¬ho (s ←∨) ind ¬ho (∨→ lind) rl ()
-- rl&¬ho-trunc⇒¬ho (∨→ s) ↓ ¬ho (∨→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce∨→↓
-- rl&¬ho-trunc⇒¬ho (∨→ s) (ind ←∨) ¬ho (∨→ lind) () tc
-- rl&¬ho-trunc⇒¬ho (∨→ s) (∨→ ind) ¬ho (∨→ lind) (≤ᵢ∨→ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∨→∨→ z)) lind rl tc
-- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) ↓ ¬ho (∨→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce←∨→↓
-- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) (ind ←∨) ¬ho (∨→ lind) () tc
-- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) (∨→ ind) ¬ho (∨→ lind) (≤ᵢ∨→ rl) tc = rl&¬ho-trunc⇒¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∨→∨→ z)) lind rl tc
-- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (lind ←∂) rl tc = ⊥-elim (¬ho hitsAtLeastOnce↓)
-- rl&¬ho-trunc⇒¬ho (s ←∂) ↓ ¬ho (lind ←∂) rl tc = λ _ → ¬ho hitsAtLeastOnce←∂↓
-- rl&¬ho-trunc⇒¬ho (s ←∂) (ind ←∂) ¬ho (lind ←∂) (≤ᵢ←∂ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∂←∂ z)) lind rl tc
-- rl&¬ho-trunc⇒¬ho (s ←∂) (∂→ ind) ¬ho (lind ←∂) () tc
-- rl&¬ho-trunc⇒¬ho (∂→ s) ind ¬ho (lind ←∂) rl ()
-- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) ↓ ¬ho (lind ←∂) rl tc = λ _ → ¬ho hitsAtLeastOnce←∂→↓
-- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) (ind ←∂) ¬ho (lind ←∂) (≤ᵢ←∂ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∂→←∂ z)) lind rl tc
-- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) (∂→ ind) ¬ho (lind ←∂) () tc
-- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (∂→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce↓
-- rl&¬ho-trunc⇒¬ho (s ←∂) ind ¬ho (∂→ lind) rl ()
-- rl&¬ho-trunc⇒¬ho (∂→ s) ↓ ¬ho (∂→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce∂→↓
-- rl&¬ho-trunc⇒¬ho (∂→ s) (ind ←∂) ¬ho (∂→ lind) () tc
-- rl&¬ho-trunc⇒¬ho (∂→ s) (∂→ ind) ¬ho (∂→ lind) (≤ᵢ∂→ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∂→∂→ z)) lind rl tc
-- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) ↓ ¬ho (∂→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce←∂→↓
-- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) (ind ←∂) ¬ho (∂→ lind) () tc
-- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) (∂→ ind) ¬ho (∂→ lind) (≤ᵢ∂→ rl) tc = rl&¬ho-trunc⇒¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∂→∂→ z)) lind rl tc





-- ¬ho⇒+ind¬ho : ∀{i u pll ll ell rll} → (s : SetLL ell) → (t : IndexLL {i} {u} rll ell)
--       → (lind : IndexLL pll ll)
--       → ¬ (hitsAtLeastOnce s t)
--       → ¬ (hitsAtLeastOnce (extendg lind s) (subst (λ x → IndexLL x (replLL ll lind ell)) (replLL-↓ {ell = ell} lind) (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) +ᵢ t))
-- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t ↓ ¬ho = ¬ho
-- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (lind ←∧) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (lind ←∧) ¬ho (hitsAtLeastOnce←∧←∧ x) | g | refl | e | q = q x
-- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (∧→ lind) ¬ho  x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (∧→ lind) ¬ho (hitsAtLeastOnce∧→∧→ x) | g | refl | e | q = q x
-- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (lind ←∨) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (lind ←∨) ¬ho (hitsAtLeastOnce←∨←∨ x) | g | refl | e | q = q x
-- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (∨→ lind) ¬ho  x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (∨→ lind) ¬ho (hitsAtLeastOnce∨→∨→ x) | g | refl | e | q = q x
-- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (lind ←∂) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (lind ←∂) ¬ho (hitsAtLeastOnce←∂←∂ x) | g | refl | e | q = q x
-- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (∂→ lind) ¬ho  x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (∂→ lind) ¬ho (hitsAtLeastOnce∂→∂→ x) | g | refl | e | q = q x



-- a≤b&¬ho-repl⇒¬ho : ∀{i u pll ll ell rll} → ∀ (s : SetLL ll) → (y : SetLL ell) → (t : IndexLL {i} {u} rll ell)
--       → (lind : IndexLL pll ll)
--       → ¬ (hitsAtLeastOnce y t)
--       → ¬ (hitsAtLeastOnce (replacePartOf s to y at lind) (subst (λ x → IndexLL x (replLL ll lind ell)) (replLL-↓ {ell = ell} lind) (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) +ᵢ t))
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} s y t ↓ ¬ho = ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (lind ←∧) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (lind ←∧) ¬ho (hitsAtLeastOnce←∧→←∧ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∧) y t (lind ←∧) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∧) y t (lind ←∧) ¬ho (hitsAtLeastOnce←∧←∧ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∧→ s) y t (lind ←∧) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∧→ s) y t (lind ←∧) ¬ho (hitsAtLeastOnce←∧→←∧ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∧→ s₁) y t (lind ←∧) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∧→ s₁) y t (lind ←∧) ¬ho (hitsAtLeastOnce←∧→←∧ x) | g | refl | e | q = q x

-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (∧→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (∧→ lind) ¬ho (hitsAtLeastOnce←∧→∧→ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∧) y t (∧→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∧) y t (∧→ lind) ¬ho (hitsAtLeastOnce←∧→∧→ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∧→ s) y t (∧→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∧→ s) y t (∧→ lind) ¬ho (hitsAtLeastOnce∧→∧→ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∧→ s₁) y t (∧→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s₁ y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∧→ s₁) y t (∧→ lind) ¬ho (hitsAtLeastOnce←∧→∧→ x) | g | refl | e | q = q x

-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (lind ←∨) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (lind ←∨) ¬ho (hitsAtLeastOnce←∨→←∨ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∨) y t (lind ←∨) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∨) y t (lind ←∨) ¬ho (hitsAtLeastOnce←∨←∨ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∨→ s) y t (lind ←∨) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∨→ s) y t (lind ←∨) ¬ho (hitsAtLeastOnce←∨→←∨ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∨→ s₁) y t (lind ←∨) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∨→ s₁) y t (lind ←∨) ¬ho (hitsAtLeastOnce←∨→←∨ x) | g | refl | e | q = q x

-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (∨→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (∨→ lind) ¬ho (hitsAtLeastOnce←∨→∨→ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∨) y t (∨→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∨) y t (∨→ lind) ¬ho (hitsAtLeastOnce←∨→∨→ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∨→ s) y t (∨→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∨→ s) y t (∨→ lind) ¬ho (hitsAtLeastOnce∨→∨→ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∨→ s₁) y t (∨→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s₁ y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∨→ s₁) y t (∨→ lind) ¬ho (hitsAtLeastOnce←∨→∨→ x) | g | refl | e | q = q x

-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (lind ←∂) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (lind ←∂) ¬ho (hitsAtLeastOnce←∂→←∂ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∂) y t (lind ←∂) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∂) y t (lind ←∂) ¬ho (hitsAtLeastOnce←∂←∂ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∂→ s) y t (lind ←∂) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∂→ s) y t (lind ←∂) ¬ho (hitsAtLeastOnce←∂→←∂ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∂→ s₁) y t (lind ←∂) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∂→ s₁) y t (lind ←∂) ¬ho (hitsAtLeastOnce←∂→←∂ x) | g | refl | e | q = q x

-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (∂→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (∂→ lind) ¬ho (hitsAtLeastOnce←∂→∂→ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∂) y t (∂→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∂) y t (∂→ lind) ¬ho (hitsAtLeastOnce←∂→∂→ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∂→ s) y t (∂→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∂→ s) y t (∂→ lind) ¬ho (hitsAtLeastOnce∂→∂→ x) | g | refl | e | q = q x
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∂→ s₁) y t (∂→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s₁ y t lind ¬ho
-- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∂→ s₁) y t (∂→ lind) ¬ho (hitsAtLeastOnce←∂→∂→ x) | g | refl | e | q = q x






  
  
-- module _ where

--   open import IndexLLProp
  
--   ho-trans : ∀{i u pll rll ll} → ∀ s → (ind1 : IndexLL {i} {u} pll ll) → (ind2 : IndexLL rll pll)
--          → (ho1 : hitsAtLeastOnce s ind1) → hitsAtLeastOnce (truncHOSetLL s ind1 ho1) ind2
--          → hitsAtLeastOnce s (ind1 +ᵢ ind2)
--   ho-trans ↓ ind ind2 ho1 ho2 = hitsAtLeastOnce↓
--   ho-trans (s ←∧) ↓ ind2 ho1 ho2 = ho2
--   ho-trans (s ←∧) (ind ←∧) ind2 (hitsAtLeastOnce←∧←∧ ho1) ho2 = hitsAtLeastOnce←∧←∧ r where
--     r = ho-trans s ind ind2 ho1 ho2
--   ho-trans (s ←∧) (∧→ ind) ind2 () ho2
--   ho-trans (∧→ s) ↓ ind2 ho1 ho2 = ho2
--   ho-trans (∧→ s) (ind ←∧) ind2 () ho2
--   ho-trans (∧→ s) (∧→ ind) ind2 (hitsAtLeastOnce∧→∧→ ho1) ho2 = hitsAtLeastOnce∧→∧→ r where
--     r = ho-trans s ind ind2 ho1 ho2
--   ho-trans (s ←∧→ s₁) ↓ ind2 ho1 ho2 = ho2
--   ho-trans (s ←∧→ s₁) (ind ←∧) ind2 (hitsAtLeastOnce←∧→←∧ ho1) ho2 = hitsAtLeastOnce←∧→←∧ r where
--     r = ho-trans s ind ind2 ho1 ho2
--   ho-trans (s ←∧→ s₁) (∧→ ind) ind2 (hitsAtLeastOnce←∧→∧→ ho1) ho2 = hitsAtLeastOnce←∧→∧→ r where
--     r = ho-trans s₁ ind ind2 ho1 ho2
--   ho-trans (s ←∨) ↓ ind2 ho1 ho2 = ho2
--   ho-trans (s ←∨) (ind ←∨) ind2 (hitsAtLeastOnce←∨←∨ ho1) ho2 = hitsAtLeastOnce←∨←∨ r where
--     r = ho-trans s ind ind2 ho1 ho2
--   ho-trans (s ←∨) (∨→ ind) ind2 () ho2
--   ho-trans (∨→ s) ↓ ind2 ho1 ho2 = ho2
--   ho-trans (∨→ s) (ind ←∨) ind2 () ho2
--   ho-trans (∨→ s) (∨→ ind) ind2 (hitsAtLeastOnce∨→∨→ ho1) ho2 = hitsAtLeastOnce∨→∨→ r where
--     r = ho-trans s ind ind2 ho1 ho2
--   ho-trans (s ←∨→ s₁) ↓ ind2 ho1 ho2 = ho2
--   ho-trans (s ←∨→ s₁) (ind ←∨) ind2 (hitsAtLeastOnce←∨→←∨ ho1) ho2 = hitsAtLeastOnce←∨→←∨ r where
--     r = ho-trans s ind ind2 ho1 ho2
--   ho-trans (s ←∨→ s₁) (∨→ ind) ind2 (hitsAtLeastOnce←∨→∨→ ho1) ho2 = hitsAtLeastOnce←∨→∨→ r where
--     r = ho-trans s₁ ind ind2 ho1 ho2
--   ho-trans (s ←∂) ↓ ind2 ho1 ho2 = ho2
--   ho-trans (s ←∂) (ind ←∂) ind2 (hitsAtLeastOnce←∂←∂ ho1) ho2 = hitsAtLeastOnce←∂←∂ r where
--     r = ho-trans s ind ind2 ho1 ho2
--   ho-trans (s ←∂) (∂→ ind) ind2 () ho2
--   ho-trans (∂→ s) ↓ ind2 ho1 ho2 = ho2
--   ho-trans (∂→ s) (ind ←∂) ind2 () ho2
--   ho-trans (∂→ s) (∂→ ind) ind2 (hitsAtLeastOnce∂→∂→ ho1) ho2 = hitsAtLeastOnce∂→∂→ r where
--     r = ho-trans s ind ind2 ho1 ho2
--   ho-trans (s ←∂→ s₁) ↓ ind2 ho1 ho2 = ho2
--   ho-trans (s ←∂→ s₁) (ind ←∂) ind2 (hitsAtLeastOnce←∂→←∂ ho1) ho2 = hitsAtLeastOnce←∂→←∂ r where
--     r = ho-trans s ind ind2 ho1 ho2
--   ho-trans (s ←∂→ s₁) (∂→ ind) ind2 (hitsAtLeastOnce←∂→∂→ ho1) ho2 = hitsAtLeastOnce←∂→∂→ r where
--     r = ho-trans s₁ ind ind2 ho1 ho2


--   oi-trans : ∀{i u pll rll ll} → ∀ s → (ind1 : IndexLL {i} {u} pll ll) → (ind2 : IndexLL rll pll)
--          → (oi1 : onlyInside s ind1) → onlyInside (truncHOSetLL s ind1 (oi⇒ho s ind1 oi1)) ind2
--          → onlyInside s (ind1 +ᵢ ind2)
--   oi-trans ↓ ↓ ind2 oi1 oi2 = oi2
--   oi-trans ↓ (x ←∧) ind2 () oi2
--   oi-trans ↓ (∧→ x) ind2 () oi2
--   oi-trans ↓ (x ←∨) ind2 () oi2
--   oi-trans ↓ (∨→ x) ind2 () oi2
--   oi-trans ↓ (x ←∂) ind2 () oi2
--   oi-trans ↓ (∂→ x) ind2 () oi2
--   oi-trans (s ←∧) ↓ ind2 oi1 oi2 = oi2
--   oi-trans (s ←∧) (ind1 ←∧) ind2 (onlyInsideC←∧←∧ oi1) oi2 = onlyInsideC←∧←∧ r where
--     r = oi-trans s ind1 ind2 oi1 oi2
--   oi-trans (s ←∧) (∧→ ind1) ind2 () oi2
--   oi-trans (∧→ s) ↓ ind2 oi1 oi2 = oi2
--   oi-trans (∧→ s) (ind1 ←∧) ind2 () oi2
--   oi-trans (∧→ s) (∧→ ind1) ind2 (onlyInsideC∧→∧→ oi1) oi2 = onlyInsideC∧→∧→ r where
--     r = oi-trans s ind1 ind2 oi1 oi2
--   oi-trans (s ←∧→ s₁) ↓ ind2 oi1 oi2 = oi2
--   oi-trans (s ←∧→ s₁) (ind1 ←∧) ind2 () oi2
--   oi-trans (s ←∧→ s₁) (∧→ ind1) ind2 () oi2
--   oi-trans (s ←∨) ↓ ind2 oi1 oi2 = oi2
--   oi-trans (s ←∨) (ind1 ←∨) ind2 (onlyInsideC←∨←∨ oi1) oi2 = onlyInsideC←∨←∨ r where
--     r = oi-trans s ind1 ind2 oi1 oi2
--   oi-trans (s ←∨) (∨→ ind1) ind2 () oi2
--   oi-trans (∨→ s) ↓ ind2 oi1 oi2 = oi2
--   oi-trans (∨→ s) (ind1 ←∨) ind2 () oi2
--   oi-trans (∨→ s) (∨→ ind1) ind2 (onlyInsideC∨→∨→ oi1) oi2 = onlyInsideC∨→∨→ r where
--     r = oi-trans s ind1 ind2 oi1 oi2
--   oi-trans (s ←∨→ s₁) ↓ ind2 oi1 oi2 = oi2
--   oi-trans (s ←∨→ s₁) (ind1 ←∨) ind2 () oi2
--   oi-trans (s ←∨→ s₁) (∨→ ind1) ind2 () oi2
--   oi-trans (s ←∂) ↓ ind2 oi1 oi2 = oi2
--   oi-trans (s ←∂) (ind1 ←∂) ind2 (onlyInsideC←∂←∂ oi1) oi2 = onlyInsideC←∂←∂ r where
--     r = oi-trans s ind1 ind2 oi1 oi2
--   oi-trans (s ←∂) (∂→ ind1) ind2 () oi2
--   oi-trans (∂→ s) ↓ ind2 oi1 oi2 = oi2
--   oi-trans (∂→ s) (ind1 ←∂) ind2 () oi2
--   oi-trans (∂→ s) (∂→ ind1) ind2 (onlyInsideC∂→∂→ oi1) oi2 = onlyInsideC∂→∂→ r where
--     r = oi-trans s ind1 ind2 oi1 oi2
--   oi-trans (s ←∂→ s₁) ↓ ind2 oi1 oi2 = oi2
--   oi-trans (s ←∂→ s₁) (ind1 ←∂) ind2 () oi2
--   oi-trans (s ←∂→ s₁) (∂→ ind1) ind2 () oi2



--   contr-pres≤ : ∀{i u ll} → (s ss : SetLL {i} {u} ll) → s ≤s ss → contruct s ≤s contruct ss 
--   contr-pres≤ ↓ ↓ eq = eq
--   contr-pres≤ ↓ (x ←∧) ()
--   contr-pres≤ ↓ (∧→ x) ()
--   contr-pres≤ ↓ (x ←∧→ x₁) ()
--   contr-pres≤ ↓ (x ←∨) ()
--   contr-pres≤ ↓ (∨→ x) ()
--   contr-pres≤ ↓ (x ←∨→ x₁) ()
--   contr-pres≤ ↓ (x ←∂) ()
--   contr-pres≤ ↓ (∂→ x) ()
--   contr-pres≤ ↓ (x ←∂→ x₁) ()
--   contr-pres≤ (s ←∧) ↓ eq = ≤↓
--   contr-pres≤ (s ←∧) (ss ←∧) (≤←∧ x) = ≤←∧ (contr-pres≤ s ss x)
--   contr-pres≤ (s ←∧) (∧→ ss) ()
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss eq
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | ↓ | e = ≤↓
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∧ | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | ∧→ g | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∧→ g₁ | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∨ | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | ∨→ g | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∨→ g₁ | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∂ | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | ∂→ g | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ↓ | g ←∂→ g₁ | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∧ | g | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ∧→ r | g | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∧→ r₁ | g | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∨ | g | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ∨→ r | g | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∨→ r₁ | g | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∂ | g | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | ∂→ r | g | e = ≤d←∧ e
--   contr-pres≤ (s ←∧) (ss ←∧→ ss₁) (≤d←∧ eq) | r ←∂→ r₁ | g | e = ≤d←∧ e
--   contr-pres≤ (∧→ s) ↓ eq = ≤↓
--   contr-pres≤ (∧→ s) (ss ←∧) ()
--   contr-pres≤ (∧→ s) (∧→ ss) (≤∧→ x) = ≤∧→ (contr-pres≤ s ss x)
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss₁ eq
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | ↓ | e = ≤↓
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∧ | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | ∧→ g | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∧→ g₁ | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∨ | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | ∨→ g | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∨→ g₁ | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∂ | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | ∂→ g | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ↓ | g ←∂→ g₁ | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∧ | g | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ∧→ r | g | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∧→ r₁ | g | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∨ | g | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ∨→ r | g | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∨→ r₁ | g | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∂ | g | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | ∂→ r | g | e = ≤d∧→ e
--   contr-pres≤ (∧→ s) (ss ←∧→ ss₁) (≤d∧→ eq) | r ←∂→ r₁ | g | e = ≤d∧→ e
--   contr-pres≤ (s ←∧→ s₁) ↓ eq = ≤↓
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧) ()
--   contr-pres≤ (s ←∧→ s₁) (∧→ ss) ()
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) with contruct s | contruct s₁ | contruct ss | contruct ss₁ | contr-pres≤ s ss eq | contr-pres≤ s₁ ss₁ eq₁
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ↓ | .↓ | .↓ | ≤↓ | ≤↓ = ≤↓
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧ | .↓ | ∧→ h | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∧→ g | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∧→ g | .↓ | ∧→ h | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ∧→ h | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨ | .↓ | ∨→ h | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∨→ g | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∨→ g | .↓ | ∨→ h | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ∨→ h | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂ | .↓ | ∂→ h | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∂→ g | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∂→ g | .↓ | ∂→ h | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂ | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ∂→ h | ≤↓ | q = ≤←∧→ ≤↓ q
--   contr-pres≤ (s ←∧→ s₁) (ss ←∧→ ss₁) (≤←∧→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∧→ ≤↓ q
--   ... | r ←∧ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∧ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
--   ... | r ←∧ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
--   ... | r ←∧ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∧ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
--   ... | r ←∧ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
--   ... | r ←∧ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∧ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
--   ... | r ←∧ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
--   ... | r ←∧ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∧ | g | t ←∧ | h | e | q = ≤←∧→ e q
--   ... | r ←∧ | g | ∧→ t | h | e | q = ≤←∧→ e q
--   ... | r ←∧ | g | t ←∧→ t₁ | h | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | ↓ | ↓ | e | q = ≤↓
--   ... | ∧→ r | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | t ←∧ | h | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | ∧→ t | h | e | q = ≤←∧→ e q
--   ... | ∧→ r | g | t ←∧→ t₁ | h | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∧→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | t ←∧ | h | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | ∧→ t | h | e | q = ≤←∧→ e q
--   ... | r ←∧→ r₁ | g | t ←∧→ t₁ | h | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∨ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | t ←∨ | h | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | ∨→ t | h | e | q = ≤←∧→ e q
--   ... | r ←∨ | g | t ←∨→ t₁ | h | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | ↓ | ↓ | e | q = ≤↓
--   ... | ∨→ r | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | t ←∨ | h | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | ∨→ t | h | e | q = ≤←∧→ e q
--   ... | ∨→ r | g | t ←∨→ t₁ | h | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∨→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | t ←∨ | h | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | ∨→ t | h | e | q = ≤←∧→ e q
--   ... | r ←∨→ r₁ | g | t ←∨→ t₁ | h | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∂ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | t ←∂ | h | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | ∂→ t | h | e | q = ≤←∧→ e q
--   ... | r ←∂ | g | t ←∂→ t₁ | h | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | ↓ | ↓ | e | q = ≤↓
--   ... | ∂→ r | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | t ←∂ | h | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | ∂→ t | h | e | q = ≤←∧→ e q
--   ... | ∂→ r | g | t ←∂→ t₁ | h | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∂→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | t ←∂ | h | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | ∂→ t | h | e | q = ≤←∧→ e q
--   ... | r ←∂→ r₁ | g | t ←∂→ t₁ | h | e | q = ≤←∧→ e q
--   contr-pres≤ (s ←∨) ↓ eq = ≤↓
--   contr-pres≤ (s ←∨) (ss ←∨) (≤←∨ x) = ≤←∨ (contr-pres≤ s ss x)
--   contr-pres≤ (s ←∨) (∨→ ss) ()
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss eq
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | ↓ | e = ≤↓
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∧ | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | ∧→ g | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∧→ g₁ | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∨ | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | ∨→ g | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∨→ g₁ | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∂ | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | ∂→ g | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ↓ | g ←∂→ g₁ | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∧ | g | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ∧→ r | g | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∧→ r₁ | g | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∨ | g | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ∨→ r | g | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∨→ r₁ | g | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∂ | g | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | ∂→ r | g | e = ≤d←∨ e
--   contr-pres≤ (s ←∨) (ss ←∨→ ss₁) (≤d←∨ eq) | r ←∂→ r₁ | g | e = ≤d←∨ e
--   contr-pres≤ (∨→ s) ↓ eq = ≤↓
--   contr-pres≤ (∨→ s) (ss ←∨) ()
--   contr-pres≤ (∨→ s) (∨→ ss) (≤∨→ x) = ≤∨→ (contr-pres≤ s ss x)
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss₁ eq
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | ↓ | e = ≤↓
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∧ | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | ∧→ g | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∧→ g₁ | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∨ | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | ∨→ g | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∨→ g₁ | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∂ | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | ∂→ g | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ↓ | g ←∂→ g₁ | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∧ | g | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ∧→ r | g | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∧→ r₁ | g | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∨ | g | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ∨→ r | g | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∨→ r₁ | g | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∂ | g | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | ∂→ r | g | e = ≤d∨→ e
--   contr-pres≤ (∨→ s) (ss ←∨→ ss₁) (≤d∨→ eq) | r ←∂→ r₁ | g | e = ≤d∨→ e
--   contr-pres≤ (s ←∨→ s₁) ↓ eq = ≤↓
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨) ()
--   contr-pres≤ (s ←∨→ s₁) (∨→ ss) ()
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) with contruct s | contruct s₁ | contruct ss | contruct ss₁ | contr-pres≤ s ss eq | contr-pres≤ s₁ ss₁ eq₁
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ↓ | .↓ | .↓ | ≤↓ | ≤↓ = ≤↓
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧ | .↓ | ∧→ h | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∧→ g | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∧→ g | .↓ | ∧→ h | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ∧→ h | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨ | .↓ | ∨→ h | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∨→ g | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∨→ g | .↓ | ∨→ h | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ∨→ h | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂ | .↓ | ∂→ h | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∂→ g | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∂→ g | .↓ | ∂→ h | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂ | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ∂→ h | ≤↓ | q = ≤←∨→ ≤↓ q
--   contr-pres≤ (s ←∨→ s₁) (ss ←∨→ ss₁) (≤←∨→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∨→ ≤↓ q
--   ... | r ←∧ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∧ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
--   ... | r ←∧ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
--   ... | r ←∧ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∧ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
--   ... | r ←∧ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
--   ... | r ←∧ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∧ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
--   ... | r ←∧ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
--   ... | r ←∧ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∧ | g | t ←∧ | h | e | q = ≤←∨→ e q
--   ... | r ←∧ | g | ∧→ t | h | e | q = ≤←∨→ e q
--   ... | r ←∧ | g | t ←∧→ t₁ | h | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | ↓ | ↓ | e | q = ≤↓
--   ... | ∧→ r | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | t ←∧ | h | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | ∧→ t | h | e | q = ≤←∨→ e q
--   ... | ∧→ r | g | t ←∧→ t₁ | h | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∧→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | t ←∧ | h | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | ∧→ t | h | e | q = ≤←∨→ e q
--   ... | r ←∧→ r₁ | g | t ←∧→ t₁ | h | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∨ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | t ←∨ | h | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | ∨→ t | h | e | q = ≤←∨→ e q
--   ... | r ←∨ | g | t ←∨→ t₁ | h | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | ↓ | ↓ | e | q = ≤↓
--   ... | ∨→ r | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | t ←∨ | h | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | ∨→ t | h | e | q = ≤←∨→ e q
--   ... | ∨→ r | g | t ←∨→ t₁ | h | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∨→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | t ←∨ | h | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | ∨→ t | h | e | q = ≤←∨→ e q
--   ... | r ←∨→ r₁ | g | t ←∨→ t₁ | h | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∂ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | t ←∂ | h | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | ∂→ t | h | e | q = ≤←∨→ e q
--   ... | r ←∂ | g | t ←∂→ t₁ | h | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | ↓ | ↓ | e | q = ≤↓
--   ... | ∂→ r | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | t ←∂ | h | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | ∂→ t | h | e | q = ≤←∨→ e q
--   ... | ∂→ r | g | t ←∂→ t₁ | h | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∂→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | t ←∂ | h | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | ∂→ t | h | e | q = ≤←∨→ e q
--   ... | r ←∂→ r₁ | g | t ←∂→ t₁ | h | e | q = ≤←∨→ e q
--   contr-pres≤ (s ←∂) ↓ eq = ≤↓
--   contr-pres≤ (s ←∂) (ss ←∂) (≤←∂ x) = ≤←∂ (contr-pres≤ s ss x)
--   contr-pres≤ (s ←∂) (∂→ ss) ()
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss eq
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | ↓ | e = ≤↓
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∧ | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | ∧→ g | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∧→ g₁ | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∨ | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | ∨→ g | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∨→ g₁ | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∂ | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | ∂→ g | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ↓ | g ←∂→ g₁ | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∧ | g | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ∧→ r | g | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∧→ r₁ | g | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∨ | g | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ∨→ r | g | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∨→ r₁ | g | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∂ | g | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | ∂→ r | g | e = ≤d←∂ e
--   contr-pres≤ (s ←∂) (ss ←∂→ ss₁) (≤d←∂ eq) | r ←∂→ r₁ | g | e = ≤d←∂ e
--   contr-pres≤ (∂→ s) ↓ eq = ≤↓
--   contr-pres≤ (∂→ s) (ss ←∂) ()
--   contr-pres≤ (∂→ s) (∂→ ss) (≤∂→ x) = ≤∂→ (contr-pres≤ s ss x)
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) with contruct ss | contruct ss₁ | contr-pres≤ s ss₁ eq
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | ↓ | e = ≤↓
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∧ | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | ∧→ g | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∧→ g₁ | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∨ | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | ∨→ g | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∨→ g₁ | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∂ | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | ∂→ g | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ↓ | g ←∂→ g₁ | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∧ | g | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ∧→ r | g | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∧→ r₁ | g | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∨ | g | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ∨→ r | g | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∨→ r₁ | g | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∂ | g | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | ∂→ r | g | e = ≤d∂→ e
--   contr-pres≤ (∂→ s) (ss ←∂→ ss₁) (≤d∂→ eq) | r ←∂→ r₁ | g | e = ≤d∂→ e
--   contr-pres≤ (s ←∂→ s₁) ↓ eq = ≤↓
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂) ()
--   contr-pres≤ (s ←∂→ s₁) (∂→ ss) ()
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) with contruct s | contruct s₁ | contruct ss | contruct ss₁ | contr-pres≤ s ss eq | contr-pres≤ s₁ ss₁ eq₁
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ↓ | .↓ | .↓ | ≤↓ | ≤↓ = ≤↓
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧ | .↓ | ∧→ h | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∧→ g | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∧→ g | .↓ | ∧→ h | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∧→ g | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | ∧→ h | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∧→ g₁ | .↓ | h ←∧→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨ | .↓ | ∨→ h | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∨→ g | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∨→ g | .↓ | ∨→ h | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∨→ g | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | ∨→ h | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∨→ g₁ | .↓ | h ←∨→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂ | .↓ | ∂→ h | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∂→ g | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∂→ g | .↓ | ∂→ h | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | ∂→ g | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ↓ | ≤↓ | q = ≤↓
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂ | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | ∂→ h | ≤↓ | q = ≤←∂→ ≤↓ q
--   contr-pres≤ (s ←∂→ s₁) (ss ←∂→ ss₁) (≤←∂→ eq eq₁) | ↓ | g ←∂→ g₁ | .↓ | h ←∂→ h₁ | ≤↓ | q = ≤←∂→ ≤↓ q
--   ... | r ←∧ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∧ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
--   ... | r ←∧ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
--   ... | r ←∧ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∧ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
--   ... | r ←∧ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
--   ... | r ←∧ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∧ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
--   ... | r ←∧ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
--   ... | r ←∧ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∧ | g | t ←∧ | h | e | q = ≤←∂→ e q
--   ... | r ←∧ | g | ∧→ t | h | e | q = ≤←∂→ e q
--   ... | r ←∧ | g | t ←∧→ t₁ | h | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | ↓ | ↓ | e | q = ≤↓
--   ... | ∧→ r | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | t ←∧ | h | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | ∧→ t | h | e | q = ≤←∂→ e q
--   ... | ∧→ r | g | t ←∧→ t₁ | h | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∧→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | t ←∧ | h | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | ∧→ t | h | e | q = ≤←∂→ e q
--   ... | r ←∧→ r₁ | g | t ←∧→ t₁ | h | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∨ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | t ←∨ | h | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | ∨→ t | h | e | q = ≤←∂→ e q
--   ... | r ←∨ | g | t ←∨→ t₁ | h | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | ↓ | ↓ | e | q = ≤↓
--   ... | ∨→ r | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | t ←∨ | h | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | ∨→ t | h | e | q = ≤←∂→ e q
--   ... | ∨→ r | g | t ←∨→ t₁ | h | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∨→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | t ←∨ | h | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | ∨→ t | h | e | q = ≤←∂→ e q
--   ... | r ←∨→ r₁ | g | t ←∨→ t₁ | h | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∂ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | t ←∂ | h | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | ∂→ t | h | e | q = ≤←∂→ e q
--   ... | r ←∂ | g | t ←∂→ t₁ | h | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | ↓ | ↓ | e | q = ≤↓
--   ... | ∂→ r | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | t ←∂ | h | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | ∂→ t | h | e | q = ≤←∂→ e q
--   ... | ∂→ r | g | t ←∂→ t₁ | h | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ↓ | e | q = ≤↓
--   ... | r ←∂→ r₁ | g | ↓ | h ←∧ | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ∧→ h | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∧→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∨ | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ∨→ h | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∨→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∂ | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | ↓ | ∂→ h | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | ↓ | h ←∂→ h₁ | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | t ←∂ | h | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | ∂→ t | h | e | q = ≤←∂→ e q
--   ... | r ←∂→ r₁ | g | t ←∂→ t₁ | h | e | q = ≤←∂→ e q



--   ¬contr≡↓⇒¬contrdel≡↓ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → (ind : IndexLL rll ll) → ∀{x} → del s ind fll ≡ ¬∅ x → ¬ (contruct x ≡ ↓)
--   ¬contr≡↓⇒¬contrdel≡↓ s eq ↓ ()
--   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∧) deq = ⊥-elim (eq refl)
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) deq with del s ind fll 
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) () | ∅
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) refl | ¬∅ di = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ (∧→ s) eq (ind ←∧) refl = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) deq with del s ind fll | inspect (λ x → del s x fll) ind
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ∅ | [ eq1 ] = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
--   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∧ rs} {fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
--     hf : ¬ (contruct s₁ ≡ ↓)
--     hf x with contruct s₁
--     hf refl | .↓ = ⊥-elim (eq refl)

--     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∧→ t)) ≡ ↓)
--     hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
--     hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
--     hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
--     hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
--     hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
--     hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
--     hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
--     hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
--     hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
--     hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
--     hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
--     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
--     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∧→ s₁)) ≡ ↓)
--     hf t eq x with contruct t | isEq (contruct t) ↓
--     hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
--     hf t eq₁ x | ↓ | no ¬p = eq₁ refl
--     hf t eq₁ () | g ←∧ | no ¬p
--     hf t eq₁ () | ∧→ g | no ¬p
--     hf t eq₁ () | g ←∧→ g₁ | no ¬p 
--     hf t eq₁ () | g ←∨ | no ¬p 
--     hf t eq₁ () | ∨→ g | no ¬p 
--     hf t eq₁ () | g ←∨→ g₁ | no ¬p 
--     hf t eq₁ () | g ←∂ | no ¬p 
--     hf t eq₁ () | ∂→ g | no ¬p 
--     hf t eq₁ () | g ←∂→ g₁ | no ¬p 
--   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∧→ ind) deq = ⊥-elim (eq refl)
--   ¬contr≡↓⇒¬contrdel≡↓ (s ←∧) eq (∧→ ind) refl = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) deq with del s ind fll
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) () | ∅
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) refl | ¬∅ x = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ∅ | r = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
--   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
--     hf : ¬ (contruct s ≡ ↓)
--     hf x with contruct s
--     hf refl | .↓ = ⊥-elim (eq refl)

--     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∧→ t)) ≡ ↓)
--     hf2 t e eq x with contruct e | isEq (contruct e) ↓
--     hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
--     hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
--     hf2 t e eq₂ () | ce ←∧ | no ¬p
--     hf2 t e eq₂ () | ∧→ ce | no ¬p 
--     hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
--     hf2 t e eq₂ () | ce ←∨ | no ¬p 
--     hf2 t e eq₂ () | ∨→ ce | no ¬p 
--     hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
--     hf2 t e eq₂ () | ce ←∂ | no ¬p 
--     hf2 t e eq₂ () | ∂→ ce | no ¬p 
--     hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
--     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
--     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∧→ t)) ≡ ↓)
--     hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
--     hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
--     hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
--     hf t eq₁ () | ↓ | g ←∧ | no ¬p
--     hf t eq₁ () | ↓ | ∧→ g | no ¬p 
--     hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
--     hf t eq₁ () | ↓ | g ←∨ | no ¬p 
--     hf t eq₁ () | ↓ | ∨→ g | no ¬p 
--     hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
--     hf t eq₁ () | ↓ | g ←∂ | no ¬p 
--     hf t eq₁ () | ↓ | ∂→ g | no ¬p 
--     hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
--     hf t eq₁ () | r ←∧ | g | no ¬p 
--     hf t eq₁ () | ∧→ r | g | no ¬p 
--     hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
--     hf t eq₁ () | r ←∨ | g | no ¬p 
--     hf t eq₁ () | ∨→ r | g | no ¬p 
--     hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
--     hf t eq₁ () | r ←∂ | g | no ¬p 
--     hf t eq₁ () | ∂→ r | g | no ¬p 
--     hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 

--   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∨) deq = ⊥-elim (eq refl)
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) deq with del s ind fll 
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) () | ∅
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) refl | ¬∅ di = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ (∨→ s) eq (ind ←∨) refl = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) deq with del s ind fll | inspect (λ x → del s x fll) ind
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ∅ | [ eq1 ] = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
--   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∨ rs} {fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
--     hf : ¬ (contruct s₁ ≡ ↓)
--     hf x with contruct s₁
--     hf refl | .↓ = ⊥-elim (eq refl)

--     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∨→ t)) ≡ ↓)
--     hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
--     hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
--     hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
--     hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
--     hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
--     hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
--     hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
--     hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
--     hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
--     hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
--     hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
--     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
--     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∨→ s₁)) ≡ ↓)
--     hf t eq x with contruct t | isEq (contruct t) ↓
--     hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
--     hf t eq₁ x | ↓ | no ¬p = eq₁ refl
--     hf t eq₁ () | g ←∧ | no ¬p
--     hf t eq₁ () | ∧→ g | no ¬p
--     hf t eq₁ () | g ←∧→ g₁ | no ¬p 
--     hf t eq₁ () | g ←∨ | no ¬p 
--     hf t eq₁ () | ∨→ g | no ¬p 
--     hf t eq₁ () | g ←∨→ g₁ | no ¬p 
--     hf t eq₁ () | g ←∂ | no ¬p 
--     hf t eq₁ () | ∂→ g | no ¬p 
--     hf t eq₁ () | g ←∂→ g₁ | no ¬p 
--   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∨→ ind) deq = ⊥-elim (eq refl)
--   ¬contr≡↓⇒¬contrdel≡↓ (s ←∨) eq (∨→ ind) refl = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) deq with del s ind fll
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) () | ∅
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) refl | ¬∅ x = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ∅ | r = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
--   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
--     hf : ¬ (contruct s ≡ ↓)
--     hf x with contruct s
--     hf refl | .↓ = ⊥-elim (eq refl)

--     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∨→ t)) ≡ ↓)
--     hf2 t e eq x with contruct e | isEq (contruct e) ↓
--     hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
--     hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
--     hf2 t e eq₂ () | ce ←∧ | no ¬p
--     hf2 t e eq₂ () | ∧→ ce | no ¬p 
--     hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
--     hf2 t e eq₂ () | ce ←∨ | no ¬p 
--     hf2 t e eq₂ () | ∨→ ce | no ¬p 
--     hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
--     hf2 t e eq₂ () | ce ←∂ | no ¬p 
--     hf2 t e eq₂ () | ∂→ ce | no ¬p 
--     hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
--     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
--     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∨→ t)) ≡ ↓)
--     hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
--     hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
--     hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
--     hf t eq₁ () | ↓ | g ←∧ | no ¬p
--     hf t eq₁ () | ↓ | ∧→ g | no ¬p 
--     hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
--     hf t eq₁ () | ↓ | g ←∨ | no ¬p 
--     hf t eq₁ () | ↓ | ∨→ g | no ¬p 
--     hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
--     hf t eq₁ () | ↓ | g ←∂ | no ¬p 
--     hf t eq₁ () | ↓ | ∂→ g | no ¬p 
--     hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
--     hf t eq₁ () | r ←∧ | g | no ¬p 
--     hf t eq₁ () | ∧→ r | g | no ¬p 
--     hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
--     hf t eq₁ () | r ←∨ | g | no ¬p 
--     hf t eq₁ () | ∨→ r | g | no ¬p 
--     hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
--     hf t eq₁ () | r ←∂ | g | no ¬p 
--     hf t eq₁ () | ∂→ r | g | no ¬p 
--     hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 

--   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∂) deq = ⊥-elim (eq refl)
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) deq with del s ind fll 
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) () | ∅
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) refl | ¬∅ di = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ (∂→ s) eq (ind ←∂) refl = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) deq with del s ind fll | inspect (λ x → del s x fll) ind
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ∅ | [ eq1 ] = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
--   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∂ rs} {fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
--     hf : ¬ (contruct s₁ ≡ ↓)
--     hf x with contruct s₁
--     hf refl | .↓ = ⊥-elim (eq refl)

--     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∂→ t)) ≡ ↓)
--     hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
--     hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
--     hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
--     hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
--     hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
--     hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
--     hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
--     hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
--     hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
--     hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
--     hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
--     hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
--     hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

--   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
--     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
--     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∂→ s₁)) ≡ ↓)
--     hf t eq x with contruct t | isEq (contruct t) ↓
--     hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
--     hf t eq₁ x | ↓ | no ¬p = eq₁ refl
--     hf t eq₁ () | g ←∧ | no ¬p
--     hf t eq₁ () | ∧→ g | no ¬p
--     hf t eq₁ () | g ←∧→ g₁ | no ¬p 
--     hf t eq₁ () | g ←∨ | no ¬p 
--     hf t eq₁ () | ∨→ g | no ¬p 
--     hf t eq₁ () | g ←∨→ g₁ | no ¬p 
--     hf t eq₁ () | g ←∂ | no ¬p 
--     hf t eq₁ () | ∂→ g | no ¬p 
--     hf t eq₁ () | g ←∂→ g₁ | no ¬p 
--   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∂→ ind) deq = ⊥-elim (eq refl)
--   ¬contr≡↓⇒¬contrdel≡↓ (s ←∂) eq (∂→ ind) refl = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) deq with del s ind fll
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) () | ∅
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) refl | ¬∅ x = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ∅ | r = λ ()
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
--   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
--     hf : ¬ (contruct s ≡ ↓)
--     hf x with contruct s
--     hf refl | .↓ = ⊥-elim (eq refl)

--     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∂→ t)) ≡ ↓)
--     hf2 t e eq x with contruct e | isEq (contruct e) ↓
--     hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
--     hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
--     hf2 t e eq₂ () | ce ←∧ | no ¬p
--     hf2 t e eq₂ () | ∧→ ce | no ¬p 
--     hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
--     hf2 t e eq₂ () | ce ←∨ | no ¬p 
--     hf2 t e eq₂ () | ∨→ ce | no ¬p 
--     hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
--     hf2 t e eq₂ () | ce ←∂ | no ¬p 
--     hf2 t e eq₂ () | ∂→ ce | no ¬p 
--     hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

--   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
--     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
--     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∂→ t)) ≡ ↓)
--     hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
--     hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
--     hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
--     hf t eq₁ () | ↓ | g ←∧ | no ¬p
--     hf t eq₁ () | ↓ | ∧→ g | no ¬p 
--     hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
--     hf t eq₁ () | ↓ | g ←∨ | no ¬p 
--     hf t eq₁ () | ↓ | ∨→ g | no ¬p 
--     hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
--     hf t eq₁ () | ↓ | g ←∂ | no ¬p 
--     hf t eq₁ () | ↓ | ∂→ g | no ¬p 
--     hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
--     hf t eq₁ () | r ←∧ | g | no ¬p 
--     hf t eq₁ () | ∧→ r | g | no ¬p 
--     hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
--     hf t eq₁ () | r ←∨ | g | no ¬p 
--     hf t eq₁ () | ∨→ r | g | no ¬p 
--     hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
--     hf t eq₁ () | r ←∂ | g | no ¬p 
--     hf t eq₁ () | ∂→ r | g | no ¬p 
--     hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 


-- module _ where

--   open Data.Product
  
--   ¬contr≡↓&trunc≡∅⇒¬contrdel≡↓ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → (ind : IndexLL rll ll) → (truncSetLL s ind ≡ ∅)
--                                  → Σ (SetLL (replLL ll ind fll)) (λ x → (del s ind fll ≡ ¬∅ x) × (¬ (contruct x ≡ ↓)))
--   ¬contr≡↓&trunc≡∅⇒¬contrdel≡↓ {fll = fll} s ceq ind treq with del s ind fll | inspect (λ x → del s x fll) ind
--   ... | ∅ | [ eq ] = ⊥-elim (d eq) where
--     d = trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind treq
--   ... | ¬∅ x | [ eq ] = (x , refl , c) where
--     c = ¬contr≡↓⇒¬contrdel≡↓ s ceq ind eq



