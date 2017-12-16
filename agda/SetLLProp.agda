module SetLLProp where

open import Common
open import LinLogic
open import SetLL
open import IndexLLProp

open import Relation.Binary.PropositionalEquality
import Data.Product
open import Data.Sum

-------------

mutual

  compl∅⇒contruct↓-abs : ∀ {i u} {l r : LinLogic i {u}} {il}
                         (s : SetLL l) (s₁ : SetLL r) (w : MSetLL l) (weq : w ≡ complLₛ s) (w₁ : MSetLL r) (weq₁ : w₁ ≡ complLₛ s₁) →
                       sbcm {il = il} w w₁ ≡ ∅ → contruct-abs {il = il} (contruct s) (contruct s₁) ≡ ↓
  compl∅⇒contruct↓-abs s s₁ ∅ weq ∅ weq1 eq = cong₂ contruct-abs (compl∅⇒contruct↓ s (sym weq)) (compl∅⇒contruct↓ s₁ (sym weq1))
  compl∅⇒contruct↓-abs s s₁ ∅ weq (¬∅ x) weq1 eq = ⊥-elim (∅-neq-¬∅ (trans (sym eq) (proj₂ (sbcm¬∅ {ms = ∅} (inj₂ (x , refl))))))
  compl∅⇒contruct↓-abs s s₁ (¬∅ x) weq w₁ weq1 eq = ⊥-elim (∅-neq-¬∅ (trans (sym eq) (proj₂ (sbcm¬∅ {ms₁ = w₁} (inj₁ (x , refl))))))


  compl∅⇒contruct↓ : ∀{i u ll} → (s : SetLL {i} {u} ll) → (eq : complLₛ s ≡ ∅) → contruct s ≡ ↓
  compl∅⇒contruct↓ ↓ eq = refl
  compl∅⇒contruct↓ (sic ds s) eq = ⊥-elim (∅-neq-¬∅ (trans (sym eq) (proj₂ (pickLLₛ-sbcm¬∅ ds (inj₂ (_ , refl))))))
  compl∅⇒contruct↓ (sbc s s₁) eq = compl∅⇒contruct↓-abs s s₁ (complLₛ s) refl (complLₛ s₁) refl eq

mutual

  contruct↓⇒compl∅-abs : ∀ {i u} {l r : LinLogic i {u}} {il}
                         (s : SetLL l) (s₁ : SetLL r) →
                       (w : SetLL l) (weq : contruct s ≡ w) → (w₁ : SetLL r) (weq₁ : contruct s₁ ≡ w₁) → (eq : contruct-abs {il = il} w w₁ ≡ ↓) → sbcm {il = il} (complLₛ s) (complLₛ s₁) ≡ ∅
  contruct↓⇒compl∅-abs s s₁ ↓ weq ↓ weq1 eq = cong₂ sbcm (contruct↓⇒compl∅ s weq) (contruct↓⇒compl∅ s₁ weq1)
  contruct↓⇒compl∅-abs s s₁ ↓ weq (sic ds w1) weq1 ()
  contruct↓⇒compl∅-abs s s₁ ↓ weq (sbc w1 w2) weq1 ()
  contruct↓⇒compl∅-abs s s₁ (sic ds w) weq w1 weq1 ()
  contruct↓⇒compl∅-abs s s₁ (sbc w w₁) weq w1 weq1 ()

  contruct↓⇒compl∅ : ∀{i u ll} → (s : SetLL {i} {u} ll) → (contruct s ≡ ↓) → (complLₛ s ≡ ∅)
  contruct↓⇒compl∅ ↓ eq = refl
  contruct↓⇒compl∅ (sic ds s) ()
  contruct↓⇒compl∅ (sbc s s₁) eq = contruct↓⇒compl∅-abs s s₁ (contruct s) refl (contruct s₁) refl eq



--------------------------------




compl-tr-com-abs2 : ∀ {ds d i u} {l : LinLogic i {u}} {il}
                      {r rll : LinLogic i} {s : SetLL (pickLL ds l r)}
                      (ind : IndexLL rll (pickLL d l r)) →
                    ~ict ds ≡ d →
                    ¬∅ fillAllLower ≡
                    (pickLLₛ-sbcm {il = il} ds (complLₛ s) (¬∅ fillAllLower)
                     >>=ₛ (λ z → truncₛ z (ic d ind)))
compl-tr-com-abs2 {ds = ds}  ind refl = trans (sym (tr-fAL ind)) (sym (truncₛ-psbcm→ ds ind))



mutual

  compl-tr-com-abs3 : ∀ {i u} {l : LinLogic i {u}} {il} {r rll : LinLogic i}
                 {s : SetLL l} {s₁ : SetLL r} → ∀ d →
                 (ind : IndexLL rll (pickLL d l r)) →
               (sbcm {il = il} (complLₛ s) (complLₛ s₁) >>=ₛ (λ z → truncₛ z (ic d ind))) ≡
               (pickLLₘₛ d (complLₛ s) (complLₛ s₁) >>=ₛ (λ z → truncₛ z ind)) →
               mcomplLₛ (truncₛ (pickLLₛ d s s₁) ind) ≡
               (sbcm {il = il} (complLₛ s) (complLₛ s₁) >>=ₛ (λ z → truncₛ z (ic d ind)))
  compl-tr-com-abs3 {s = s} ic← ind eq = trans (compl-tr-com s ind) (sym eq)
  compl-tr-com-abs3 {s₁ = s₁} ic→ ind eq = trans (compl-tr-com s₁ ind) (sym eq)


  compl-tr-com-abs1 : ∀ {ds d} (w : DecICT ds d) {i u}
                      {l : LinLogic i {u}} {il} {r rll : LinLogic i}
                      {s : SetLL (pickLL ds l r)} {ind : IndexLL rll (pickLL d l r)} →
                    mcomplLₛ (truncₛ-abs s ind w) ≡
                    (pickLLₛ-sbcm {il = il} ds (complLₛ s) (¬∅ fillAllLower)
                     >>=ₛ (λ z → truncₛ z (ic d ind)))
  compl-tr-com-abs1 {ds} (yes refl) {s = s} {ind} = trans (compl-tr-com s ind) (sym (truncₛ-psbcm← ds ind))
  compl-tr-com-abs1 {ds} (no x) {s = s} {ind} = compl-tr-com-abs2 {s = s} ind (~ict-sym x)
      

  compl-tr-com : ∀{i u rll ll} → (s : SetLL {i} {u} ll) 
                      → (ind : IndexLL rll ll)
                      → mcomplLₛ (truncₛ s ind) ≡ (complLₛ s >>=ₛ (λ z → truncₛ z ind))
  compl-tr-com s ↓ = >>=ₛ-id (complLₛ s)
  compl-tr-com ↓ (ic d ind) = refl
  compl-tr-com (sic ds s) (ic d ind) = compl-tr-com-abs1 (isEqICT ds d)
  compl-tr-com (sbc s s₁) (ic d ind) = compl-tr-com-abs3 d ind (truncₛ-sbcm d (complLₛ s) (complLₛ s₁) ind) 





mutual
--
--  compl-repl⇒id-abs1 : ∀ {i u} {l : LinLogic i {u}} {il}
--                       {r rll : LinLogic i} {s : SetLL (l < il > r)} {vs : SetLL rll} {d}
--                       {w1 : MSetLL rll} {ds} {x : SetLL (pickLL ds l r)}
--                       (ind : IndexLL rll (pickLL d l r)) →
--                     ∅ ≡ complLₛ s →
--                     w1 ≡ complLₛ vs →
--                     ¬∅ (sic ds x) ≡ del s (ic d ind) →
--                     (w : DecICT ds d) →
--                     mapₛ (λ s₁ → sic {il = il} d (s-extend ind s₁)) w1 ≡
--                     complLₛ (`replacePartOf-abs x vs ind w)
--  compl-repl⇒id-abs1 {s = ↓} {d = d} ind eq eq1 eq2 (yes refl) = ⊥-elim (pickLLₛ-sbcm⇒¬sic d (del ↓ ind) eq2)
--  compl-repl⇒id-abs1 {s = sic ds s} ind eq eq1 eq2 (yes refl) = ⊥-elim (∅-neq-¬∅ (trans eq (proj₂ (pickLLₛ-sbcm¬∅ ds (inj₂ (_ , refl)))))) 
--  compl-repl⇒id-abs1 {s = sbc s s₁} {d = d} ind eq eq1 eq2 (yes refl) = ⊥-elim (pickLLₛ-sbcm⇒¬sic d (del (pickLLₛ d s s₁) ind) eq2)
--  compl-repl⇒id-abs1 {s = ↓} {d = ic←} ↓ eq refl refl (no refl) = {!!}
--  compl-repl⇒id-abs1 {s = sic ic← s} {d = ic←} {w1} ↓ eq eq1 () (no refl)
--  compl-repl⇒id-abs1 {s = sic ic→ s} {d = ic←} {w1} ↓ eq eq1 refl (no refl) = ⊥-elim (∅-neq-¬∅ (trans eq (proj₂ (sbcm¬∅ {ms₁ = complLₛ s} (inj₁ (_ , refl))))))
--  compl-repl⇒id-abs1 {s = sbc s s₁} {d = ic←} {w1} ↓ eq eq1 refl (no refl) = {!!}
--  compl-repl⇒id-abs1 {s = s} {d = ic←} {w1} (ic d ind) eq eq1 eq2 (no refl) = {!!}
--  compl-repl⇒id-abs1 {s = s} {d = ic→} {w1} ind eq eq1 eq2 (no refl) = {!!} -- trans (mapₛ-fg {g = s-extend ind} {f = sic d} w1) {!!}
--
--  compl-repl⇒id-abs : ∀ {i u} {ll rll : LinLogic i {u}} {s : SetLL ll}
--                  {vs : SetLL rll} (ind : IndexLL rll ll) (w : MSetLL ll) (eq : w ≡ complLₛ s)
--                  (w₁ : MSetLL rll) (eq₁ : w₁ ≡ complLₛ vs) → (w₂ : MSetLL ll) → (eq₂ : w₂ ≡ del s ind) →
--                (mreplacePartOf w to w₁ at ind) ≡
--                complLₛ (replacePartOf-abs {b = vs} ind w₂)
--  compl-repl⇒id-abs ↓ ∅ eq w1 refl .∅ refl = mapₛ-id w1
--  compl-repl⇒id-abs ↓ (¬∅ x) eq ∅ eq1 .∅ refl = eq1
--  compl-repl⇒id-abs ↓ (¬∅ x) eq (¬∅ x₁) eq1 .∅ refl = eq1
--  compl-repl⇒id-abs {s = s} (ic d ind) ∅ eq w1 eq1 ∅ eq2 = ⊥-elim (compl≡∅⇒¬oi {s = s} (sym eq) (del⇒oi (sym eq2)))
--  compl-repl⇒id-abs {s = s} (ic d ind) ∅ eq w1 eq1 (¬∅ ↓) eq2 = ⊥-elim (del⇒¬ho {s = s} (ic d ind) eq2 hLO↓ic)
--  compl-repl⇒id-abs {s = s} (ic d ind) ∅ eq w1 eq1 (¬∅ (sic ds x)) eq2 = compl-repl⇒id-abs1 {s = s} ind eq eq1 eq2 (isEqICT ds d)
--  compl-repl⇒id-abs (ic d ind) ∅ eq w1 eq1 (¬∅ (sbc x x₁)) eq2 = {!!}
--  compl-repl⇒id-abs (ic d ind) (¬∅ x) eq w1 eq1 w2 eq2 = {!!}
--

-- TODO These are general proofs.
  compl-repl⇒id-abs1 : ∀ {i u} {r l : LinLogic i {u}} {il}
                       (w : MSetLL l) →
                     mapₛ (sic {r = r} {il = il} ic←) w ≡ sbcm w ∅
  compl-repl⇒id-abs1 ∅ = refl
  compl-repl⇒id-abs1 (¬∅ x) = refl

  compl-repl⇒id-abs2 : ∀ {i u} {l : LinLogic i {u}} {il} {r : LinLogic i}
                       (w : MSetLL r) →
                     mapₛ (sic {l = l} {il = il} ic→) w ≡ sbcm ∅ w
  compl-repl⇒id-abs2 ∅ = refl
  compl-repl⇒id-abs2 (¬∅ x) = refl

  compl-repl⇒id-abs : ∀ {i u} {l : LinLogic i {u}} {r : LinLogic i}
                      {il} {rll : LinLogic i} {vs : SetLL rll} d
                      (ind : IndexLL rll (pickLL d l r)) →
                    (dw : MSetLL (pickLL d l r)) → (deq : dw ≡ del ↓ ind)
                    (w : MSetLL (l < il > r)) (eq : w ≡ (pickLLₛ-sbcm {il = il} d dw (¬∅ (pickLLₛ (~ict d) ↓ ↓)))) (w₁ : SetLL (l < il > r)) →
                    w ≡ ¬∅ w₁ →
                    mapₛ (λ s → sic d (s-extend ind s)) (complLₛ vs) ≡ complLₛ (replacePartOf-abs {b = vs} (ic d ind) w)
  compl-repl⇒id-abs ic← ind ∅ deq .(¬∅ ↓) () ↓ refl
  compl-repl⇒id-abs ic→ ind ∅ deq .(¬∅ ↓) () ↓ refl
  compl-repl⇒id-abs {vs = vs} ic← ↓ ∅ deq .(¬∅ (sic ic→ ↓)) refl (sic .ic→ .↓) refl = compl-repl⇒id-abs1 (complLₛ vs)
  compl-repl⇒id-abs ic← (ic d ind) ∅ deq .(¬∅ (sic ds w1)) eq (sic ds w1) refl = ⊥-elim (∅-neq-¬∅ (trans deq (proj₂ (pickLLₛ-sbcm¬∅ d (inj₂ (_ , refl)))))) 
  compl-repl⇒id-abs {vs = vs} ic→ ↓ ∅ deq .(¬∅ (sic ic← ↓)) refl (sic .ic← .↓) refl = compl-repl⇒id-abs2 (complLₛ vs)
  compl-repl⇒id-abs {vs = vs} ic→ (ic d ind) ∅ deq .(¬∅ (sic ic← ↓)) refl (sic .ic← .↓) refl = ⊥-elim (∅-neq-¬∅ (trans deq (proj₂ (pickLLₛ-sbcm¬∅ d (inj₂ (_ , refl))))))
  compl-repl⇒id-abs ic← ind ∅ deq .(¬∅ (sbc w1 w2)) eq (sbc w1 w2) refl = {!!}
  compl-repl⇒id-abs ic→ ind ∅ deq .(¬∅ (sbc w1 w2)) eq (sbc w1 w2) refl = {!!}
  compl-repl⇒id-abs d ind (¬∅ x) deq .(¬∅ w1) eq w1 refl = {!!}


  compl-repl⇒id : ∀{i u ll rll} → {s : SetLL ll} → {vs : SetLL {i} rll} → (ind : IndexLL {i} {u} rll ll)
                       → mreplacePartOf (complLₛ s) to (complLₛ vs) at ind ≡ complLₛ (replacePartOf s to vs at ind) 
  -- compl-repl⇒id {s = s} {vs} ind = compl-repl⇒id-abs ind (complLₛ s) refl (complLₛ vs) refl (del s ind) refl
  compl-repl⇒id {s = ↓} {vs} ↓ = mapₛ-id (complLₛ vs)
  compl-repl⇒id {s = ↓} {vs} (ic {il = il} d ind) =  compl-repl⇒id-abs d ind (del ↓ ind) refl (pickLLₛ-sbcm {il = il} d (del ↓ ind) (¬∅ (pickLLₛ (~ict d) ↓ ↓))) refl (proj₁ r) (proj₂ r)  where
    r = pickLLₛ-sbcm¬∅ {il = il} d {ms = del ↓ ind} (inj₂ (pickLLₛ (~ict d) ↓ ↓ , refl))
  compl-repl⇒id {s = sic ds s} {vs} ind = {!!}
  compl-repl⇒id {s = sbc s s₁} {vs} ind = {!!} 






-- contr-pres⊂ₛ-abs← : ∀ {i u} {l : LinLogic i {u}} {il}
--                    {r : LinLogic i} (w : SetLL l) (z : SetLL r)
--                    (w₁ : SetLL l) →
--                  {{eq : w ⊂ₛ w₁}} →
--                  contruct-abs {il = il} w z ⊂ₛ contruct-abs w₁ z
-- contr-pres⊂ₛ-abs← ↓ ↓ .↓ {{⊂↓}} = ⊂↓
-- contr-pres⊂ₛ-abs← ↓ (sic ds z) .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs← ↓ (sbc z z₁) .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs← (sic ds w) ↓ .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs← (sic ds w) (sic ds₁ z) .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs← (sic ds w) (sbc z z₁) .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs← (sbc w w₁) ↓ .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs← (sbc w w₁) (sic ds z) .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs← (sbc w w₁) (sbc z z₁) .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs← .(sic _ _) z .(sic _ _) {{⊂sic}} = it
-- contr-pres⊂ₛ-abs← .(sbc _ _) z .(sbc _ _) {{⊂sbc}} = it
-- contr-pres⊂ₛ-abs← .(sic _ _) z .(sbc _ _) {{⊂dsbc}} = it

-- contr-pres⊂ₛ-abs→ : ∀ {i u} {l : LinLogic i {u}} {il}
--                    {r : LinLogic i} (w : SetLL l) (z : SetLL r)
--                    (w₁ : SetLL l) →
--                  {{eq : w ⊂ₛ w₁}} →
--                  contruct-abs {il = il} z w ⊂ₛ contruct-abs z w₁
-- contr-pres⊂ₛ-abs→ w ↓ .↓ {{⊂↓}} = ⊂↓
-- contr-pres⊂ₛ-abs→ w (sic ds z) .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs→ w (sbc z z₁) .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs→ .(sic _ _) ↓ .(sic _ _) {{⊂sic}} = it
-- contr-pres⊂ₛ-abs→ .(sic _ _) (sic ds z) .(sic _ _) {{⊂sic}} = it
-- contr-pres⊂ₛ-abs→ .(sic _ _) (sbc z z₁) .(sic _ _) {{⊂sic}} = it
-- contr-pres⊂ₛ-abs→ .(sbc _ _) ↓ .(sbc _ _) {{⊂sbc}} = it
-- contr-pres⊂ₛ-abs→ .(sbc _ _) (sic ds z) .(sbc _ _) {{⊂sbc}} = it
-- contr-pres⊂ₛ-abs→ .(sbc _ _) (sbc z z₁) .(sbc _ _) {{⊂sbc}} = it
-- contr-pres⊂ₛ-abs→ .(sic _ _) ↓ .(sbc _ _) {{⊂dsbc}} = it
-- contr-pres⊂ₛ-abs→ .(sic _ _) (sic ds z) .(sbc _ _) {{⊂dsbc}} = it
-- contr-pres⊂ₛ-abs→ .(sic _ _) (sbc z z₁) .(sbc _ _) {{⊂dsbc}} = it


-- contr-pres⊂ₛ-abs1 : ∀ {i u} {l r : LinLogic i {u}} {il}
--                       {sx sly : SetLL l} {sry : SetLL r} (w w₁ : SetLL l) (w₂ : SetLL r)
--                       {{eq : w ⊂ₛ w₁}} →
--                     sic {il = il} ic← w ⊂ₛ contruct-abs w₁ w₂
-- contr-pres⊂ₛ-abs1 w .↓ ↓ {{⊂↓}} = ⊂↓
-- contr-pres⊂ₛ-abs1 w .↓ (sic ds w2) {{⊂↓}} = it
-- contr-pres⊂ₛ-abs1 w .↓ (sbc w2 w3) {{⊂↓}} = it
-- contr-pres⊂ₛ-abs1 .(sic _ _) .(sic _ _) w2 {{⊂sic}} = it
-- contr-pres⊂ₛ-abs1 .(sbc _ _) .(sbc _ _) w2 {{⊂sbc}} = it
-- contr-pres⊂ₛ-abs1 .(sic _ _) .(sbc _ _) w2 {{⊂dsbc}} = it

-- contr-pres⊂ₛ-abs2 : ∀ {i u} {l r : LinLogic i {u}} {il} {sx : SetLL r}
--                       {sly : SetLL l} {sry : SetLL r} (w : SetLL r) (w₁ : SetLL l)
--                       (w₂ : SetLL r) {{eq : w ⊂ₛ w₂}} →
--                     sic {il = il} ic→ w ⊂ₛ contruct-abs w₁ w₂
-- contr-pres⊂ₛ-abs2 w ↓ .↓ {{⊂↓}} = ⊂↓
-- contr-pres⊂ₛ-abs2 w (sic ds w1) .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs2 w (sbc w1 w2) .↓ {{⊂↓}} = it
-- contr-pres⊂ₛ-abs2 .(sic _ _) ↓ .(sic _ _) {{⊂sic}} = it
-- contr-pres⊂ₛ-abs2 .(sic _ _) (sic ds w1) .(sic _ _) {{⊂sic}} = it
-- contr-pres⊂ₛ-abs2 .(sic _ _) (sbc w1 w2) .(sic _ _) {{⊂sic}} = it
-- contr-pres⊂ₛ-abs2 .(sbc _ _) ↓ .(sbc _ _) {{⊂sbc}} = it
-- contr-pres⊂ₛ-abs2 .(sbc _ _) (sic ds w1) .(sbc _ _) {{⊂sbc}} = it
-- contr-pres⊂ₛ-abs2 .(sbc _ _) (sbc w1 w2) .(sbc _ _) {{⊂sbc}} = it
-- contr-pres⊂ₛ-abs2 .(sic _ _) ↓ .(sbc _ _) {{⊂dsbc}} = it
-- contr-pres⊂ₛ-abs2 .(sic _ _) (sic ds w1) .(sbc _ _) {{⊂dsbc}} = it
-- contr-pres⊂ₛ-abs2 .(sic _ _) (sbc w1 w2) .(sbc _ _) {{⊂dsbc}} = it

-- mutual


--   contr-pres⊂ₛ-abs : ∀ {i u} {l : LinLogic i {u}} {s ss : SetLL l} {il}
--                      {r : LinLogic i} {s1 ss1 : SetLL r} (w : SetLL l) (w₁ : SetLL r)
--                      (w₂ : SetLL l) (w₃ : SetLL r) →
--                    {{eq : w ⊂ₛ w₂}} →
--                    {{eq1 : w₁ ⊂ₛ w₃}} →
--                    contruct-abs {il = il} w w₁ ⊂ₛ contruct-abs w₂ w₃
--   contr-pres⊂ₛ-abs w w1 w2 w3 {{eq}} {{eq1}} = ⊂ₛ-trans (contr-pres⊂ₛ-abs← w w1 w2) (contr-pres⊂ₛ-abs→ w1 w2 w3)


--   contr-pres⊂ₛ : ∀{i u ll} → (s ss : SetLL {i} {u} ll) → {{eq : s ⊂ₛ ss}} → contruct s ⊂ₛ contruct ss 
--   contr-pres⊂ₛ s .↓ {{⊂↓}} = ⊂↓
--   contr-pres⊂ₛ (sic _ s) (sic _ ss) {{⊂sic}} = ⊂sic {{ieq = contr-pres⊂ₛ s ss}}
--   contr-pres⊂ₛ (sbc s s1) (sbc ss ss1) {{⊂sbc {{ieql = ieql}} {{ieqr}}}} =  contr-pres⊂ₛ-abs {s = s} {ss} {s1 = s1} {ss1} (contruct s) (contruct s1) (contruct ss) (contruct ss1) {{contr-pres⊂ₛ s ss}} {{contr-pres⊂ₛ s1 ss1}} 
--   contr-pres⊂ₛ (sic ic← sx) (sbc sly sry) {{⊂dsbc}} = contr-pres⊂ₛ-abs1 {sx = sx} {sly} {sry} (contruct sx) (contruct sly) (contruct sry) {{contr-pres⊂ₛ sx sly}}
--   contr-pres⊂ₛ (sic ic→ sx) (sbc sly sry) {{⊂dsbc}} = contr-pres⊂ₛ-abs2 {sx = sx} {sly} {sry} (contruct sx) (contruct sly) (contruct sry) {{contr-pres⊂ₛ sx sry}} 




-- -- module _ where

-- --   open import Data.Product

-- --   compl≡¬∅⇒replace-compl≡¬∅ : ∀{i u ll ell pll x trs} → (s : SetLL ll) → (lind : IndexLL {i} {u} pll ll)
-- --           → (eq : complLₛ s ≡ ¬∅ x)
-- --           → (teq : truncSetLL s lind ≡ ¬∅ trs)
-- --           → complLₛ trs ≡ ∅
-- --           → (vs : SetLL ell) 
-- --           → let mx = replacePartOf s to vs at lind in
-- --           Σ (SetLL (replLL ll lind ell)) (λ cs → complLₛ mx ≡ ¬∅ cs)
-- --   compl≡¬∅⇒replace-compl≡¬∅ s ↓ eq refl ceq vs with complLₛ s
-- --   compl≡¬∅⇒replace-compl≡¬∅ s ↓ () refl refl vs | .∅
-- --   compl≡¬∅⇒replace-compl≡¬∅ ↓ (lind ←∧) () teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) eq teq ceq vs with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind 
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) eq teq ceq vs | ∅ = (∧→ fillAllLower rll) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) eq teq ceq vs | ¬∅ x = (x ←∧→ fillAllLower rll) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (∧→ s) (lind ←∧) eq () ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs with complLₛ s₁
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ∅ with complLₛ s | inspect complLₛ s 
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) () teq ceq vs | ∅ | ∅ | [ e ]
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
-- --     is = compl≡¬∅⇒replace-compl≡¬∅ s lind e teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (x ←∧) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ¬∅ x with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ¬∅ x | ∅ = (∧→ x) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (lind ←∧) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x ←∧→ x₁) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ ↓ (∧→ lind) () teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧) (∧→ lind) eq () ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rrl} (∧→ s) (∧→ lind) eq teq ceq vs with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rrl} (∧→ s) (∧→ lind) eq teq ceq vs | ∅ = (fillAllLower lll ←∧) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∧ rrl} (∧→ s) (∧→ lind) eq teq ceq vs | ¬∅ x = (fillAllLower lll ←∧→ x) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs with complLₛ s
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ∅ with complLₛ s₁ | inspect complLₛ s₁
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) () teq ceq vs | ∅ | ∅ | e
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
-- --     is = compl≡¬∅⇒replace-compl≡¬∅ s₁ lind e teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
-- --     mx = replacePartOf s₁ to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (∧→ x) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ¬∅ x with complLₛ mx where
-- --     mx = replacePartOf s₁ to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ¬∅ x | ∅ = (x ←∧) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∧→ s₁) (∧→ lind) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x₁ ←∧→ x) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ ↓ (lind ←∨) () teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) eq teq ceq vs with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind 
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) eq teq ceq vs | ∅ = (∨→ fillAllLower rll) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) eq teq ceq vs | ¬∅ x = (x ←∨→ fillAllLower rll) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (∨→ s) (lind ←∨) eq () ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs with complLₛ s₁
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ∅ with complLₛ s | inspect complLₛ s 
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) () teq ceq vs | ∅ | ∅ | [ e ]
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
-- --     is = compl≡¬∅⇒replace-compl≡¬∅ s lind e teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (x ←∨) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ¬∅ x with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ¬∅ x | ∅ = (∨→ x) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (lind ←∨) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x ←∨→ x₁) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ ↓ (∨→ lind) () teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨) (∨→ lind) eq () ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rrl} (∨→ s) (∨→ lind) eq teq ceq vs with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rrl} (∨→ s) (∨→ lind) eq teq ceq vs | ∅ = (fillAllLower lll ←∨) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∨ rrl} (∨→ s) (∨→ lind) eq teq ceq vs | ¬∅ x = (fillAllLower lll ←∨→ x) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs with complLₛ s
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ∅ with complLₛ s₁ | inspect complLₛ s₁
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) () teq ceq vs | ∅ | ∅ | e
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
-- --     is = compl≡¬∅⇒replace-compl≡¬∅ s₁ lind e teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
-- --     mx = replacePartOf s₁ to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (∨→ x) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ¬∅ x with complLₛ mx where
-- --     mx = replacePartOf s₁ to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ¬∅ x | ∅ = (x ←∨) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∨→ s₁) (∨→ lind) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x₁ ←∨→ x) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ ↓ (lind ←∂) () teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) eq teq ceq vs with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind 
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) eq teq ceq vs | ∅ = (∂→ fillAllLower rll) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) eq teq ceq vs | ¬∅ x = (x ←∂→ fillAllLower rll) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (∂→ s) (lind ←∂) eq () ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs with complLₛ s₁
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ∅ with complLₛ s | inspect complLₛ s 
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) () teq ceq vs | ∅ | ∅ | [ e ]
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
-- --     is = compl≡¬∅⇒replace-compl≡¬∅ s lind e teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (x ←∂) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ¬∅ x with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ¬∅ x | ∅ = (∂→ x) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (lind ←∂) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x ←∂→ x₁) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ ↓ (∂→ lind) () teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂) (∂→ lind) eq () ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rrl} (∂→ s) (∂→ lind) eq teq ceq vs with complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rrl} (∂→ s) (∂→ lind) eq teq ceq vs | ∅ = (fillAllLower lll ←∂) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ {ll = lll ∂ rrl} (∂→ s) (∂→ lind) eq teq ceq vs | ¬∅ x = (fillAllLower lll ←∂→ x) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs with complLₛ s
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ∅ with complLₛ s₁ | inspect complLₛ s₁
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) () teq ceq vs | ∅ | ∅ | e
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] with is where
-- --     is = compl≡¬∅⇒replace-compl≡¬∅ s₁ lind e teq ceq vs
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , iseq with complLₛ mx where
-- --     mx = replacePartOf s₁ to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ∅ | ¬∅ x | [ e ] | iscs , () | ∅
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ∅ | ¬∅ x₁ | [ e ] | iscs , iseq | ¬∅ x = (∂→ x) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ¬∅ x with complLₛ mx where
-- --     mx = replacePartOf s₁ to vs at lind
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ¬∅ x | ∅ = (x ←∂) , refl
-- --   compl≡¬∅⇒replace-compl≡¬∅ (s ←∂→ s₁) (∂→ lind) eq teq ceq vs | ¬∅ x₁ | ¬∅ x = (x₁ ←∂→ x) , refl
  
  
    
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ : ∀{i u ll ell pll} → (s : SetLL ll) → (lind : IndexLL {i} {u} pll ll)
-- --           → (vs : SetLL ell) 
-- --           → complLₛ vs ≡ ∅
-- --           → let mx = replacePartOf s to vs at lind in
-- --           ∀{cs} → 
-- --           (cmeq : complLₛ mx ≡ ¬∅ cs) →
-- --           Σ (SetLL ll) (λ x → complLₛ s ≡ ¬∅ x)
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s ↓ vs cv cmeq with complLₛ vs
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s ↓ vs refl () | .∅
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∧) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf ↓ to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∧) vs cv () | ∅ | [ e ]
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∧) vs cv cmeq | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∧) vs cv cmeq | ¬∅ x | [ e ] | proj3 , ()
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) vs cv cmeq  with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) vs cv cmeq | ∅ = (∧→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (lind ←∧) vs cv cmeq | ¬∅ x = (x ←∧→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (∧→ s) (lind ←∧) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∧ rll} (∧→ s) (lind ←∧) vs cv cmeq | ∅ = (fillAllLower lll ←∧) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∧ rll} (∧→ s) (lind ←∧) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∧→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq with complLₛ s₁
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv () | ∅ | ∅ | e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (x ←∧) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ¬∅ x with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ¬∅ x | ∅ = (∧→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (lind ←∧) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x ←∧→ x₁) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∧→ lind) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf ↓ to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∧→ lind) vs cv () | ∅ | e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∧→ lind) vs cv cmeq | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∧→ lind) vs cv cmeq | ¬∅ x | [ e ] | proj₃ , ()
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (∧→ lind) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (∧→ lind) vs cv cmeq | ∅ = (∧→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (s ←∧) (∧→ lind) vs cv cmeq | ¬∅ x = (x ←∧→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∧ rll} (∧→ s) (∧→ lind) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∧ rll} (∧→ s) (∧→ lind) vs cv cmeq | ∅ = (fillAllLower lll ←∧) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∧ rll} (∧→ s) (∧→ lind) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∧→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf s₁ to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv () | ∅ | ∅ | e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s₁ lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s₁
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (∧→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ¬∅ x with complLₛ s₁
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ¬∅ x | ∅ = (x ←∧) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∧→ s₁) (∧→ lind) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x₁ ←∧→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∨) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf ↓ to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∨) vs cv () | ∅ | [ e ]
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∨) vs cv cmeq | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∨) vs cv cmeq | ¬∅ x | [ e ] | proj3 , ()
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) vs cv cmeq  with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) vs cv cmeq | ∅ = (∨→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (lind ←∨) vs cv cmeq | ¬∅ x = (x ←∨→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (∨→ s) (lind ←∨) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∨ rll} (∨→ s) (lind ←∨) vs cv cmeq | ∅ = (fillAllLower lll ←∨) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∨ rll} (∨→ s) (lind ←∨) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∨→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq with complLₛ s₁
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv () | ∅ | ∅ | e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (x ←∨) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ¬∅ x with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ¬∅ x | ∅ = (∨→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (lind ←∨) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x ←∨→ x₁) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∨→ lind) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf ↓ to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∨→ lind) vs cv () | ∅ | e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∨→ lind) vs cv cmeq | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∨→ lind) vs cv cmeq | ¬∅ x | [ e ] | proj₃ , ()
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (∨→ lind) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (∨→ lind) vs cv cmeq | ∅ = (∨→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (s ←∨) (∨→ lind) vs cv cmeq | ¬∅ x = (x ←∨→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∨ rll} (∨→ s) (∨→ lind) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∨ rll} (∨→ s) (∨→ lind) vs cv cmeq | ∅ = (fillAllLower lll ←∨) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∨ rll} (∨→ s) (∨→ lind) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∨→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf s₁ to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv () | ∅ | ∅ | e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s₁ lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s₁
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (∨→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ¬∅ x with complLₛ s₁
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ¬∅ x | ∅ = (x ←∨) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∨→ s₁) (∨→ lind) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x₁ ←∨→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∂) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf ↓ to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∂) vs cv () | ∅ | [ e ]
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∂) vs cv cmeq | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (lind ←∂) vs cv cmeq | ¬∅ x | [ e ] | proj3 , ()
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) vs cv cmeq  with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) vs cv cmeq | ∅ = (∂→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (lind ←∂) vs cv cmeq | ¬∅ x = (x ←∂→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (∂→ s) (lind ←∂) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∂ rll} (∂→ s) (lind ←∂) vs cv cmeq | ∅ = (fillAllLower lll ←∂) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∂ rll} (∂→ s) (lind ←∂) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∂→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq with complLₛ s₁
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf s to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv () | ∅ | ∅ | e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (x ←∂) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ¬∅ x with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ¬∅ x | ∅ = (∂→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (lind ←∂) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x ←∂→ x₁) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∂→ lind) vs cv cmeq with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf ↓ to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∂→ lind) vs cv () | ∅ | e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∂→ lind) vs cv cmeq | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ ↓ (∂→ lind) vs cv cmeq | ¬∅ x | [ e ] | proj₃ , ()
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (∂→ lind) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (∂→ lind) vs cv cmeq | ∅ = (∂→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (s ←∂) (∂→ lind) vs cv cmeq | ¬∅ x = (x ←∂→ fillAllLower rll) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {ll = lll ∂ rll} (∂→ s) (∂→ lind) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∂ rll} (∂→ s) (∂→ lind) vs cv cmeq | ∅ = (fillAllLower lll ←∂) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ {u = _} {lll ∂ rll} (∂→ s) (∂→ lind) vs cv cmeq | ¬∅ x = (fillAllLower lll ←∂→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq with complLₛ s
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ∅ with complLₛ mx | inspect complLₛ mx where
-- --     mx = replacePartOf s₁ to vs at lind
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv () | ∅ | ∅ | e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] with is where
-- --     is = vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ s₁ lind vs cv e
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , proj4 with complLₛ s₁
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ∅ | ¬∅ x | [ e ] | proj₃ , () | ∅
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ∅ | ¬∅ x₁ | [ e ] | proj₃ , proj4 | ¬∅ x = (∂→ x) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ¬∅ x with complLₛ s₁
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ¬∅ x | ∅ = (x ←∂) , refl
-- --   vcompl≡∅&repl-compl≡¬∅⇒compl≡¬∅ (s ←∂→ s₁) (∂→ lind) vs cv cmeq | ¬∅ x₁ | ¬∅ x = (x₁ ←∂→ x) , refl
  




-- --   onlyInsideUnique : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) 
-- --                    → (a : onlyInside s ind) → (b : onlyInside s ind)
-- --                    → a ≡ b
-- --   onlyInsideUnique ↓ ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
-- --   onlyInsideUnique ↓ (ind ←∧) () b
-- --   onlyInsideUnique ↓ (∧→ ind) () b
-- --   onlyInsideUnique ↓ (ind ←∨) () b
-- --   onlyInsideUnique ↓ (∨→ ind) () b
-- --   onlyInsideUnique ↓ (ind ←∂) () b
-- --   onlyInsideUnique ↓ (∂→ ind) () b
-- --   onlyInsideUnique (s ←∧) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
-- --   onlyInsideUnique (s ←∧) (ind ←∧) (onlyInsideC←∧←∧ a) (onlyInsideC←∧←∧ b) with (onlyInsideUnique s ind a b)
-- --   onlyInsideUnique (s ←∧) (ind ←∧) (onlyInsideC←∧←∧ a) (onlyInsideC←∧←∧ .a) | refl = refl
-- --   onlyInsideUnique (s ←∧) (∧→ ind) () b
-- --   onlyInsideUnique (∧→ s) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
-- --   onlyInsideUnique (∧→ s) (ind ←∧) () b
-- --   onlyInsideUnique (∧→ s) (∧→ ind) (onlyInsideC∧→∧→ a) (onlyInsideC∧→∧→ b) with (onlyInsideUnique s ind a b)
-- --   onlyInsideUnique (∧→ s) (∧→ ind) (onlyInsideC∧→∧→ a) (onlyInsideC∧→∧→ .a) | refl = refl
-- --   onlyInsideUnique (s ←∧→ s₁) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
-- --   onlyInsideUnique (s ←∧→ s₁) (ind ←∧) () b
-- --   onlyInsideUnique (s ←∧→ s₁) (∧→ ind) () b
-- --   onlyInsideUnique (s ←∨) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
-- --   onlyInsideUnique (s ←∨) (ind ←∨) (onlyInsideC←∨←∨ a) (onlyInsideC←∨←∨ b) with (onlyInsideUnique s ind a b)
-- --   onlyInsideUnique (s ←∨) (ind ←∨) (onlyInsideC←∨←∨ a) (onlyInsideC←∨←∨ .a) | refl = refl
-- --   onlyInsideUnique (s ←∨) (∨→ ind) () b
-- --   onlyInsideUnique (∨→ s) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
-- --   onlyInsideUnique (∨→ s) (ind ←∨) () b
-- --   onlyInsideUnique (∨→ s) (∨→ ind) (onlyInsideC∨→∨→ a) (onlyInsideC∨→∨→ b) with (onlyInsideUnique s ind a b)
-- --   onlyInsideUnique (∨→ s) (∨→ ind) (onlyInsideC∨→∨→ a) (onlyInsideC∨→∨→ .a) | refl = refl
-- --   onlyInsideUnique (s ←∨→ s₁) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
-- --   onlyInsideUnique (s ←∨→ s₁) (ind ←∨) () b
-- --   onlyInsideUnique (s ←∨→ s₁) (∨→ ind) () b
-- --   onlyInsideUnique (s ←∂) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
-- --   onlyInsideUnique (s ←∂) (ind ←∂) (onlyInsideC←∂←∂ a) (onlyInsideC←∂←∂ b) with (onlyInsideUnique s ind a b)
-- --   onlyInsideUnique (s ←∂) (ind ←∂) (onlyInsideC←∂←∂ a) (onlyInsideC←∂←∂ .a) | refl = refl
-- --   onlyInsideUnique (s ←∂) (∂→ ind) () b
-- --   onlyInsideUnique (∂→ s) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
-- --   onlyInsideUnique (∂→ s) (ind ←∂) () b
-- --   onlyInsideUnique (∂→ s) (∂→ ind) (onlyInsideC∂→∂→ a) (onlyInsideC∂→∂→ b) with (onlyInsideUnique s ind a b)
-- --   onlyInsideUnique (∂→ s) (∂→ ind) (onlyInsideC∂→∂→ a) (onlyInsideC∂→∂→ .a) | refl = refl
-- --   onlyInsideUnique (s ←∂→ s₁) ↓ onlyInsideCs↓ onlyInsideCs↓ = refl
-- --   onlyInsideUnique (s ←∂→ s₁) (ind ←∂) () b
-- --   onlyInsideUnique (s ←∂→ s₁) (∂→ ind) () b


-- --   isOnlyInside : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → Dec (onlyInside s ind)
-- --   isOnlyInside ↓ ↓ = yes onlyInsideCs↓
-- --   isOnlyInside ↓ (ind ←∧) = no (λ ())
-- --   isOnlyInside ↓ (∧→ ind) = no (λ ())
-- --   isOnlyInside ↓ (ind ←∨) = no (λ ())
-- --   isOnlyInside ↓ (∨→ ind) = no (λ ())
-- --   isOnlyInside ↓ (ind ←∂) = no (λ ())
-- --   isOnlyInside ↓ (∂→ ind) = no (λ ())
-- --   isOnlyInside (s ←∧) ↓ = yes onlyInsideCs↓
-- --   isOnlyInside (s ←∧) (ind ←∧) with (isOnlyInside s ind)
-- --   isOnlyInside (s ←∧) (ind ←∧) | yes p = yes (onlyInsideC←∧←∧ p)
-- --   isOnlyInside (s ←∧) (ind ←∧) | no ¬p = no (λ {(onlyInsideC←∧←∧ x) → ¬p x})
-- --   isOnlyInside (s ←∧) (∧→ ind) = no (λ ())
-- --   isOnlyInside (∧→ s) ↓ = yes onlyInsideCs↓
-- --   isOnlyInside (∧→ s) (ind ←∧) = no (λ ())
-- --   isOnlyInside (∧→ s) (∧→ ind) with (isOnlyInside s ind)
-- --   isOnlyInside (∧→ s) (∧→ ind) | yes p = yes (onlyInsideC∧→∧→ p)
-- --   isOnlyInside (∧→ s) (∧→ ind) | no ¬p = no (λ { (onlyInsideC∧→∧→ x) → ¬p x})
-- --   isOnlyInside (s ←∧→ s₁) ↓ = yes onlyInsideCs↓
-- --   isOnlyInside (s ←∧→ s₁) (ind ←∧) = no (λ ())
-- --   isOnlyInside (s ←∧→ s₁) (∧→ ind) = no (λ ())
-- --   isOnlyInside (s ←∨) ↓ = yes onlyInsideCs↓
-- --   isOnlyInside (s ←∨) (ind ←∨) with (isOnlyInside s ind)
-- --   isOnlyInside (s ←∨) (ind ←∨) | yes p = yes (onlyInsideC←∨←∨ p)
-- --   isOnlyInside (s ←∨) (ind ←∨) | no ¬p = no ( λ { (onlyInsideC←∨←∨ x) → ¬p x})
-- --   isOnlyInside (s ←∨) (∨→ ind) = no (λ ())
-- --   isOnlyInside (∨→ s) ↓ = yes onlyInsideCs↓
-- --   isOnlyInside (∨→ s) (ind ←∨) = no (λ ())
-- --   isOnlyInside (∨→ s) (∨→ ind) with (isOnlyInside s ind)
-- --   isOnlyInside (∨→ s) (∨→ ind) | yes p = yes (onlyInsideC∨→∨→ p)
-- --   isOnlyInside (∨→ s) (∨→ ind) | no ¬p = no ( λ { (onlyInsideC∨→∨→ x) → ¬p x})
-- --   isOnlyInside (s ←∨→ s₁) ↓ = yes onlyInsideCs↓
-- --   isOnlyInside (s ←∨→ s₁) (ind ←∨) = no (λ ())
-- --   isOnlyInside (s ←∨→ s₁) (∨→ ind) = no (λ ())
-- --   isOnlyInside (s ←∂) ↓ = yes onlyInsideCs↓
-- --   isOnlyInside (s ←∂) (ind ←∂) with (isOnlyInside s ind)
-- --   isOnlyInside (s ←∂) (ind ←∂) | yes p = yes (onlyInsideC←∂←∂ p)
-- --   isOnlyInside (s ←∂) (ind ←∂) | no ¬p = no ( λ { (onlyInsideC←∂←∂ x) → ¬p x})
-- --   isOnlyInside (s ←∂) (∂→ ind) = no (λ ())
-- --   isOnlyInside (∂→ s) ↓ = yes onlyInsideCs↓
-- --   isOnlyInside (∂→ s) (ind ←∂) = no (λ ())
-- --   isOnlyInside (∂→ s) (∂→ ind) with (isOnlyInside s ind)
-- --   isOnlyInside (∂→ s) (∂→ ind) | yes p = yes (onlyInsideC∂→∂→ p)
-- --   isOnlyInside (∂→ s) (∂→ ind) | no ¬p = no (λ { (onlyInsideC∂→∂→ x) → ¬p x})
-- --   isOnlyInside (s ←∂→ s₁) ↓ = yes onlyInsideCs↓
-- --   isOnlyInside (s ←∂→ s₁) (ind ←∂) = no (λ ())
-- --   isOnlyInside (s ←∂→ s₁) (∂→ ind) = no (λ ())




-- --   hitsAtLeastOnceUnique : ∀{i u ll rll} → (s : SetLL ll) → (ind : IndexLL {i} {u} rll ll) → (a : hitsAtLeastOnce s ind) → (b : hitsAtLeastOnce s ind) → a ≡ b
-- --   hitsAtLeastOnceUnique ↓ ind hitsAtLeastOnce↓ hitsAtLeastOnce↓ = refl
-- --   hitsAtLeastOnceUnique (s ←∧) ↓ hitsAtLeastOnce←∧↓ hitsAtLeastOnce←∧↓ = refl
-- --   hitsAtLeastOnceUnique (s ←∧) (ind ←∧) (hitsAtLeastOnce←∧←∧ a) (hitsAtLeastOnce←∧←∧ b) with (hitsAtLeastOnceUnique s ind a b)
-- --   hitsAtLeastOnceUnique (s ←∧) (ind ←∧) (hitsAtLeastOnce←∧←∧ a) (hitsAtLeastOnce←∧←∧ .a) | refl = refl
-- --   hitsAtLeastOnceUnique (s ←∧) (∧→ ind) () b
-- --   hitsAtLeastOnceUnique (∧→ s) ↓ hitsAtLeastOnce∧→↓ hitsAtLeastOnce∧→↓ = refl
-- --   hitsAtLeastOnceUnique (∧→ s) (ind ←∧) () b
-- --   hitsAtLeastOnceUnique (∧→ s) (∧→ ind) (hitsAtLeastOnce∧→∧→ a) (hitsAtLeastOnce∧→∧→ b) with (hitsAtLeastOnceUnique s ind a b)
-- --   hitsAtLeastOnceUnique (∧→ s) (∧→ ind) (hitsAtLeastOnce∧→∧→ a) (hitsAtLeastOnce∧→∧→ .a) | refl = refl
-- --   hitsAtLeastOnceUnique (s ←∧→ s₁) ↓ hitsAtLeastOnce←∧→↓ hitsAtLeastOnce←∧→↓ = refl
-- --   hitsAtLeastOnceUnique (s ←∧→ s₁) (ind ←∧) (hitsAtLeastOnce←∧→←∧ a) (hitsAtLeastOnce←∧→←∧ b) with (hitsAtLeastOnceUnique s ind a b)
-- --   hitsAtLeastOnceUnique (s ←∧→ s₁) (ind ←∧) (hitsAtLeastOnce←∧→←∧ a) (hitsAtLeastOnce←∧→←∧ .a) | refl = refl
-- --   hitsAtLeastOnceUnique (s ←∧→ s₁) (∧→ ind) (hitsAtLeastOnce←∧→∧→ a) (hitsAtLeastOnce←∧→∧→ b) with (hitsAtLeastOnceUnique s₁ ind a b)
-- --   hitsAtLeastOnceUnique (s ←∧→ s₁) (∧→ ind) (hitsAtLeastOnce←∧→∧→ a) (hitsAtLeastOnce←∧→∧→ .a) | refl = refl
-- --   hitsAtLeastOnceUnique (s ←∨) ↓ hitsAtLeastOnce←∨↓ hitsAtLeastOnce←∨↓ = refl
-- --   hitsAtLeastOnceUnique (s ←∨) (ind ←∨) (hitsAtLeastOnce←∨←∨ a) (hitsAtLeastOnce←∨←∨ b) with (hitsAtLeastOnceUnique s ind a b)
-- --   hitsAtLeastOnceUnique (s ←∨) (ind ←∨) (hitsAtLeastOnce←∨←∨ a) (hitsAtLeastOnce←∨←∨ .a) | refl = refl
-- --   hitsAtLeastOnceUnique (s ←∨) (∨→ ind) () b
-- --   hitsAtLeastOnceUnique (∨→ s) ↓ hitsAtLeastOnce∨→↓ hitsAtLeastOnce∨→↓ = refl
-- --   hitsAtLeastOnceUnique (∨→ s) (ind ←∨) () b
-- --   hitsAtLeastOnceUnique (∨→ s) (∨→ ind) (hitsAtLeastOnce∨→∨→ a) (hitsAtLeastOnce∨→∨→ b) with (hitsAtLeastOnceUnique s ind a b)
-- --   hitsAtLeastOnceUnique (∨→ s) (∨→ ind) (hitsAtLeastOnce∨→∨→ a) (hitsAtLeastOnce∨→∨→ .a) | refl = refl
-- --   hitsAtLeastOnceUnique (s ←∨→ s₁) ↓ hitsAtLeastOnce←∨→↓ hitsAtLeastOnce←∨→↓ = refl
-- --   hitsAtLeastOnceUnique (s ←∨→ s₁) (ind ←∨) (hitsAtLeastOnce←∨→←∨ a) (hitsAtLeastOnce←∨→←∨ b) with (hitsAtLeastOnceUnique s ind a b)
-- --   hitsAtLeastOnceUnique (s ←∨→ s₁) (ind ←∨) (hitsAtLeastOnce←∨→←∨ a) (hitsAtLeastOnce←∨→←∨ .a) | refl = refl
-- --   hitsAtLeastOnceUnique (s ←∨→ s₁) (∨→ ind) (hitsAtLeastOnce←∨→∨→ a) (hitsAtLeastOnce←∨→∨→ b) with (hitsAtLeastOnceUnique s₁ ind a b)
-- --   hitsAtLeastOnceUnique (s ←∨→ s₁) (∨→ ind) (hitsAtLeastOnce←∨→∨→ a) (hitsAtLeastOnce←∨→∨→ .a) | refl = refl
-- --   hitsAtLeastOnceUnique (s ←∂) ↓ hitsAtLeastOnce←∂↓ hitsAtLeastOnce←∂↓ = refl
-- --   hitsAtLeastOnceUnique (s ←∂) (ind ←∂) (hitsAtLeastOnce←∂←∂ a) (hitsAtLeastOnce←∂←∂ b) with (hitsAtLeastOnceUnique s ind a b)
-- --   hitsAtLeastOnceUnique (s ←∂) (ind ←∂) (hitsAtLeastOnce←∂←∂ a) (hitsAtLeastOnce←∂←∂ .a) | refl = refl
-- --   hitsAtLeastOnceUnique (s ←∂) (∂→ ind) () b
-- --   hitsAtLeastOnceUnique (∂→ s) ↓ hitsAtLeastOnce∂→↓ hitsAtLeastOnce∂→↓ = refl
-- --   hitsAtLeastOnceUnique (∂→ s) (ind ←∂) () b
-- --   hitsAtLeastOnceUnique (∂→ s) (∂→ ind) (hitsAtLeastOnce∂→∂→ a) (hitsAtLeastOnce∂→∂→ b) with (hitsAtLeastOnceUnique s ind a b)
-- --   hitsAtLeastOnceUnique (∂→ s) (∂→ ind) (hitsAtLeastOnce∂→∂→ a) (hitsAtLeastOnce∂→∂→ .a) | refl = refl
-- --   hitsAtLeastOnceUnique (s ←∂→ s₁) ↓ hitsAtLeastOnce←∂→↓ hitsAtLeastOnce←∂→↓ = refl
-- --   hitsAtLeastOnceUnique (s ←∂→ s₁) (ind ←∂) (hitsAtLeastOnce←∂→←∂ a) (hitsAtLeastOnce←∂→←∂ b) with (hitsAtLeastOnceUnique s ind a b)
-- --   hitsAtLeastOnceUnique (s ←∂→ s₁) (ind ←∂) (hitsAtLeastOnce←∂→←∂ a) (hitsAtLeastOnce←∂→←∂ .a) | refl = refl
-- --   hitsAtLeastOnceUnique (s ←∂→ s₁) (∂→ ind) (hitsAtLeastOnce←∂→∂→ a) (hitsAtLeastOnce←∂→∂→ b) with (hitsAtLeastOnceUnique s₁ ind a b)
-- --   hitsAtLeastOnceUnique (s ←∂→ s₁) (∂→ ind) (hitsAtLeastOnce←∂→∂→ a) (hitsAtLeastOnce←∂→∂→ .a) | refl = refl





-- --   ho-spec : ∀{i u ll rll tll ic ns} → {s : SetLL (expLLT ic tll)} → {ind : IndexLL {i} {u} rll ll} → {{eq : sl-ext {ic = ic} s ≡ ¬∅ ns}} → hitsAtLeastOnce s (expInd ic tll ind) → hitsAtLeastOnce ns ind
-- --   ho-spec {ic = ic←∧} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-spec {ic = ic←∧} {s = s ←∧} {{eq = refl}} (hitsAtLeastOnce←∧←∧ ho) = ho
-- --   ho-spec {ic = ic←∧} {s = ∧→ s} {{eq = ()}} ho
-- --   ho-spec {ic = ic←∧} {s = s ←∧→ s₁} {{eq = refl}} (hitsAtLeastOnce←∧→←∧ ho) = ho
-- --   ho-spec {ic = ic∧→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-spec {ic = ic∧→} {s = s ←∧} {{eq = ()}} ho
-- --   ho-spec {ic = ic∧→} {s = ∧→ s} {{eq = refl}} (hitsAtLeastOnce∧→∧→ ho) = ho
-- --   ho-spec {ic = ic∧→} {s = s ←∧→ s₁} {{eq = refl}} (hitsAtLeastOnce←∧→∧→ ho) = ho
-- --   ho-spec {ic = ic←∨} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-spec {ic = ic←∨} {s = s ←∨} {{eq = refl}} (hitsAtLeastOnce←∨←∨ ho) = ho
-- --   ho-spec {ic = ic←∨} {s = ∨→ s} {{eq = ()}} ho
-- --   ho-spec {ic = ic←∨} {s = s ←∨→ s₁} {{eq = refl}} (hitsAtLeastOnce←∨→←∨ ho) = ho
-- --   ho-spec {ic = ic∨→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-spec {ic = ic∨→} {s = s ←∨} {{eq = ()}} ho
-- --   ho-spec {ic = ic∨→} {s = ∨→ s} {{eq = refl}} (hitsAtLeastOnce∨→∨→ ho) = ho
-- --   ho-spec {ic = ic∨→} {s = s ←∨→ s₁} {{eq = refl}} (hitsAtLeastOnce←∨→∨→ ho) = ho
-- --   ho-spec {ic = ic←∂} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-spec {ic = ic←∂} {s = s ←∂} {{eq = refl}} (hitsAtLeastOnce←∂←∂ ho) = ho
-- --   ho-spec {ic = ic←∂} {s = ∂→ s} {{eq = ()}} ho
-- --   ho-spec {ic = ic←∂} {s = s ←∂→ s₁} {{eq = refl}} (hitsAtLeastOnce←∂→←∂ ho) = ho
-- --   ho-spec {ic = ic∂→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-spec {ic = ic∂→} {s = s ←∂} {{eq = ()}} ho
-- --   ho-spec {ic = ic∂→} {s = ∂→ s} {{eq = refl}} (hitsAtLeastOnce∂→∂→ ho) = ho
-- --   ho-spec {ic = ic∂→} {s = s ←∂→ s₁} {{eq = refl}} (hitsAtLeastOnce←∂→∂→ ho) = ho
  
  
  
-- --   ho-ext : ∀{i u ll rll tll ic ns} → {s : SetLL (expLLT ic tll)} → {ind : IndexLL {i} {u} rll ll} → {{eq : sl-ext {ic = ic} s ≡ ¬∅ ns}} → hitsAtLeastOnce ns ind → hitsAtLeastOnce s (expInd ic tll ind)
-- --   ho-ext {ic = ic←∧} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-ext {ic = ic←∧} {s = s ←∧} {{eq = refl}} ho = hitsAtLeastOnce←∧←∧ ho
-- --   ho-ext {ic = ic←∧} {s = ∧→ s} {{eq = ()}} ho
-- --   ho-ext {ic = ic←∧} {s = s ←∧→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∧→←∧ ho
-- --   ho-ext {ic = ic∧→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-ext {ic = ic∧→} {s = s ←∧} {{eq = ()}} ho
-- --   ho-ext {ic = ic∧→} {s = ∧→ s} {{eq = refl}} ho = hitsAtLeastOnce∧→∧→ ho
-- --   ho-ext {ic = ic∧→} {s = s ←∧→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∧→∧→ ho
-- --   ho-ext {ic = ic←∨} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-ext {ic = ic←∨} {s = s ←∨} {{eq = refl}} ho = hitsAtLeastOnce←∨←∨ ho
-- --   ho-ext {ic = ic←∨} {s = ∨→ s} {{eq = ()}} ho
-- --   ho-ext {ic = ic←∨} {s = s ←∨→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∨→←∨ ho
-- --   ho-ext {ic = ic∨→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-ext {ic = ic∨→} {s = s ←∨} {{eq = ()}} ho
-- --   ho-ext {ic = ic∨→} {s = ∨→ s} {{eq = refl}} ho = hitsAtLeastOnce∨→∨→ ho
-- --   ho-ext {ic = ic∨→} {s = s ←∨→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∨→∨→ ho
-- --   ho-ext {ic = ic←∂} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-ext {ic = ic←∂} {s = s ←∂} {{eq = refl}} ho = hitsAtLeastOnce←∂←∂ ho
-- --   ho-ext {ic = ic←∂} {s = ∂→ s} {{eq = ()}} ho
-- --   ho-ext {ic = ic←∂} {s = s ←∂→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∂→←∂ ho
-- --   ho-ext {ic = ic∂→} {s = ↓} {{eq = refl}} ho = hitsAtLeastOnce↓
-- --   ho-ext {ic = ic∂→} {s = s ←∂} {{eq = ()}} ho
-- --   ho-ext {ic = ic∂→} {s = ∂→ s} {{eq = refl}} ho = hitsAtLeastOnce∂→∂→ ho
-- --   ho-ext {ic = ic∂→} {s = s ←∂→ s₁} {{eq = refl}} ho = hitsAtLeastOnce←∂→∂→ ho
  
  
  
-- --   ¬ho-spec : ∀{i u ll rll tll ic ns} → {s : SetLL (expLLT ic tll)} → {ind : IndexLL {i} {u} rll ll} → {{eq : sl-ext {ic = ic} s ≡ ¬∅ ns}} → ¬ (hitsAtLeastOnce s (expInd ic tll ind)) → ¬ (hitsAtLeastOnce ns ind)
-- --   ¬ho-spec {ic = ic} {s = s} {{eq = eq}} ¬ho y = ¬ho (ho-ext y)
  
  
  


-- --   doesItHitAtLeastOnce : ∀{i u ll q} → (s : SetLL ll) → (ind : IndexLL {i} {u} q ll) → Dec (hitsAtLeastOnce s ind)
-- --   doesItHitAtLeastOnce ↓ ind = yes hitsAtLeastOnce↓
-- --   doesItHitAtLeastOnce (s ←∧) ↓ = yes hitsAtLeastOnce←∧↓
-- --   doesItHitAtLeastOnce (s ←∧) (ind ←∧) with (doesItHitAtLeastOnce s ind)
-- --   doesItHitAtLeastOnce (s ←∧) (ind ←∧) | yes p = yes (hitsAtLeastOnce←∧←∧ p)
-- --   doesItHitAtLeastOnce (s ←∧) (ind ←∧) | no ¬p = no (λ {(hitsAtLeastOnce←∧←∧ x) → ¬p x})
-- --   doesItHitAtLeastOnce (s ←∧) (∧→ ind) = no (λ ())
-- --   doesItHitAtLeastOnce (∧→ s) ↓ = yes hitsAtLeastOnce∧→↓
-- --   doesItHitAtLeastOnce (∧→ s) (ind ←∧) = no (λ ())
-- --   doesItHitAtLeastOnce (∧→ s) (∧→ ind) with (doesItHitAtLeastOnce s ind)
-- --   doesItHitAtLeastOnce (∧→ s) (∧→ ind) | yes p = yes (hitsAtLeastOnce∧→∧→ p)
-- --   doesItHitAtLeastOnce (∧→ s) (∧→ ind) | no ¬p = no (λ {(hitsAtLeastOnce∧→∧→ x) → ¬p x})
-- --   doesItHitAtLeastOnce (s ←∧→ s₁) ↓ = yes hitsAtLeastOnce←∧→↓
-- --   doesItHitAtLeastOnce (s ←∧→ s₁) (ind ←∧) with (doesItHitAtLeastOnce s ind)
-- --   doesItHitAtLeastOnce (s ←∧→ s₁) (ind ←∧) | yes p = yes (hitsAtLeastOnce←∧→←∧ p)
-- --   doesItHitAtLeastOnce (s ←∧→ s₁) (ind ←∧) | no ¬p = no (λ {(hitsAtLeastOnce←∧→←∧ x) → ¬p x})
-- --   doesItHitAtLeastOnce (s ←∧→ s₁) (∧→ ind) with (doesItHitAtLeastOnce s₁ ind)
-- --   doesItHitAtLeastOnce (s ←∧→ s₁) (∧→ ind) | yes p = yes (hitsAtLeastOnce←∧→∧→ p) 
-- --   doesItHitAtLeastOnce (s ←∧→ s₁) (∧→ ind) | no ¬p = no (λ {(hitsAtLeastOnce←∧→∧→ x) → ¬p x})
-- --   doesItHitAtLeastOnce (s ←∨) ↓ = yes hitsAtLeastOnce←∨↓
-- --   doesItHitAtLeastOnce (s ←∨) (ind ←∨) with (doesItHitAtLeastOnce s ind)
-- --   doesItHitAtLeastOnce (s ←∨) (ind ←∨) | yes p = yes (hitsAtLeastOnce←∨←∨ p) 
-- --   doesItHitAtLeastOnce (s ←∨) (ind ←∨) | no ¬p = no (λ {(hitsAtLeastOnce←∨←∨ x) → ¬p x})
-- --   doesItHitAtLeastOnce (s ←∨) (∨→ ind) = no (λ ())
-- --   doesItHitAtLeastOnce (∨→ s) ↓ = yes hitsAtLeastOnce∨→↓
-- --   doesItHitAtLeastOnce (∨→ s) (ind ←∨) = no (λ ())
-- --   doesItHitAtLeastOnce (∨→ s) (∨→ ind) with (doesItHitAtLeastOnce s ind)
-- --   doesItHitAtLeastOnce (∨→ s) (∨→ ind) | yes p = yes (hitsAtLeastOnce∨→∨→ p) 
-- --   doesItHitAtLeastOnce (∨→ s) (∨→ ind) | no ¬p = no (λ {(hitsAtLeastOnce∨→∨→ x) → ¬p x})
-- --   doesItHitAtLeastOnce (s ←∨→ s₁) ↓ = yes hitsAtLeastOnce←∨→↓
-- --   doesItHitAtLeastOnce (s ←∨→ s₁) (ind ←∨) with (doesItHitAtLeastOnce s ind)
-- --   doesItHitAtLeastOnce (s ←∨→ s₁) (ind ←∨) | yes p = yes (hitsAtLeastOnce←∨→←∨ p) 
-- --   doesItHitAtLeastOnce (s ←∨→ s₁) (ind ←∨) | no ¬p = no (λ {(hitsAtLeastOnce←∨→←∨ x) → ¬p x})
-- --   doesItHitAtLeastOnce (s ←∨→ s₁) (∨→ ind) with (doesItHitAtLeastOnce s₁ ind)
-- --   doesItHitAtLeastOnce (s ←∨→ s₁) (∨→ ind) | yes p = yes (hitsAtLeastOnce←∨→∨→ p)
-- --   doesItHitAtLeastOnce (s ←∨→ s₁) (∨→ ind) | no ¬p = no (λ {(hitsAtLeastOnce←∨→∨→ x) → ¬p x})
-- --   doesItHitAtLeastOnce (s ←∂) ↓ = yes hitsAtLeastOnce←∂↓
-- --   doesItHitAtLeastOnce (s ←∂) (ind ←∂) with (doesItHitAtLeastOnce s ind)
-- --   doesItHitAtLeastOnce (s ←∂) (ind ←∂) | yes p = yes (hitsAtLeastOnce←∂←∂ p) 
-- --   doesItHitAtLeastOnce (s ←∂) (ind ←∂) | no ¬p = no (λ {(hitsAtLeastOnce←∂←∂ x) → ¬p x})
-- --   doesItHitAtLeastOnce (s ←∂) (∂→ ind) = no (λ ())
-- --   doesItHitAtLeastOnce (∂→ s) ↓ = yes hitsAtLeastOnce∂→↓
-- --   doesItHitAtLeastOnce (∂→ s) (ind ←∂) = no (λ ())
-- --   doesItHitAtLeastOnce (∂→ s) (∂→ ind) with (doesItHitAtLeastOnce s ind)
-- --   doesItHitAtLeastOnce (∂→ s) (∂→ ind) | yes p = yes (hitsAtLeastOnce∂→∂→ p) 
-- --   doesItHitAtLeastOnce (∂→ s) (∂→ ind) | no ¬p = no (λ {(hitsAtLeastOnce∂→∂→ x) → ¬p x})
-- --   doesItHitAtLeastOnce (s ←∂→ s₁) ↓ = yes hitsAtLeastOnce←∂→↓
-- --   doesItHitAtLeastOnce (s ←∂→ s₁) (ind ←∂) with (doesItHitAtLeastOnce s ind)
-- --   doesItHitAtLeastOnce (s ←∂→ s₁) (ind ←∂) | yes p = yes (hitsAtLeastOnce←∂→←∂ p)
-- --   doesItHitAtLeastOnce (s ←∂→ s₁) (ind ←∂) | no ¬p = no (λ {(hitsAtLeastOnce←∂→←∂ x) → ¬p x})
-- --   doesItHitAtLeastOnce (s ←∂→ s₁) (∂→ ind) with (doesItHitAtLeastOnce s₁ ind)
-- --   doesItHitAtLeastOnce (s ←∂→ s₁) (∂→ ind) | yes p = yes (hitsAtLeastOnce←∂→∂→ p)
-- --   doesItHitAtLeastOnce (s ←∂→ s₁) (∂→ ind) | no ¬p = no (λ {(hitsAtLeastOnce←∂→∂→ x) → ¬p x})




-- --   ¬ho⇒del≡¬∅ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → ¬(hitsAtLeastOnce s ind) → Σ (SetLL (replLL ll ind fll)) (λ z → del s ind fll ≡ ¬∅ z)
-- --   ¬ho⇒del≡¬∅ {fll = fll} s ind ¬ho with del s ind fll | inspect (del s ind) fll
-- --   ¬ho⇒del≡¬∅ {fll = fll} s ind ¬ho | ∅ | [ eq ] = ⊥-elim (¬ho⇒¬del≡∅ s ind ¬ho eq)
-- --   ¬ho⇒del≡¬∅ {fll = fll} s ind ¬ho | ¬∅ x | [ eq ] = x , refl



-- --   trunc≡∅⇒¬mrpls≡∅ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → (ind : IndexLL rll ll) → (truncSetLL s ind ≡ ∅) → ¬ (mreplacePartOf (¬∅ s) to (∅ {ll = fll}) at ind ≡ ∅)
-- --   trunc≡∅⇒¬mrpls≡∅ s ind treq = ¬ho⇒¬del≡∅ s ind (trunc≡∅⇒¬ho s ind treq)


-- --   ho⇒¬trunc≡∅ : ∀ {i u ll pll} → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
-- --                  → (prf : hitsAtLeastOnce s ind) → ¬ (truncSetLL s ind ≡ ∅)
-- --   ho⇒¬trunc≡∅ s ind prf x = trunc≡∅⇒¬ho s ind x prf




-- --   oi⇒¬trunc≡∅ : ∀ {i u ll pll} → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
-- --                  → (prf : onlyInside s ind) → ¬ (truncSetLL s ind ≡ ∅)
-- --   oi⇒¬trunc≡∅ s ind prf = ho⇒¬trunc≡∅ s ind (oi⇒ho s ind prf)



  
-- --   ¬trho : ∀{i u ll pll rll} →  ∀ ltr → (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
-- --           → ¬ (hitsAtLeastOnce s ind) → (ut : UpTran {rll = rll} ind ltr)
-- --           → ¬ (hitsAtLeastOnce (SetLL.tran s ltr) (IndexLLProp.tran ind ltr ut))
-- --   ¬trho I s ind ¬ho indI = ¬ho
-- --   ¬trho (∂c ltr) ↓ .(_ ←∂) ¬ho (←∂∂c ut) = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (∂c ltr) ↓ .(∂→ _) ¬ho (∂→∂c ut) = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (∂c ltr) (s ←∂) (ind ←∂) ¬ho (←∂∂c ut) = ¬trho ltr (∂→ s) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ s) (∂→ ind))
-- --     ¬nho (hitsAtLeastOnce∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂←∂ x)
-- --   ¬trho (∂c ltr) (s ←∂) (∂→ ind) ¬ho (∂→∂c ut) = ¬trho ltr (∂→ s) (ind ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ s) (ind ←∂))
-- --     ¬nho ()
-- --   ¬trho (∂c ltr) (∂→ s) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce∂→↓
-- --   ¬trho (∂c ltr) (∂→ s) (ind ←∂) ¬ho (←∂∂c ut) = ¬trho ltr (s ←∂) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (∂→ ind))
-- --     ¬nho ()
-- --   ¬trho (∂c ltr) (∂→ s) (∂→ ind) ¬ho (∂→∂c ut) = ¬trho ltr (s ←∂) (ind ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (ind ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂←∂ x) = ¬ho (hitsAtLeastOnce∂→∂→ x)
-- --   ¬trho (∂c ltr) (s ←∂→ s₁) (ind ←∂) ¬ho (←∂∂c ut) = ¬trho ltr (s₁ ←∂→ s) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∂→ s) (∂→ ind))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
-- --   ¬trho (∂c ltr) (s ←∂→ s₁) (∂→ ind) ¬ho (∂→∂c ut)  = ¬trho ltr (s₁ ←∂→ s) (ind ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∂→ s) (ind ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
-- --   ¬trho (∧c ltr) ↓ .(_ ←∧) ¬ho (←∧∧c ut) = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (∧c ltr) ↓ .(∧→ _) ¬ho (∧→∧c ut) = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (∧c ltr) (s ←∧) (ind ←∧) ¬ho (←∧∧c ut) = ¬trho ltr (∧→ s) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ s) (∧→ ind))
-- --     ¬nho (hitsAtLeastOnce∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧←∧ x)
-- --   ¬trho (∧c ltr) (s ←∧) (∧→ ind) ¬ho (∧→∧c ut) = ¬trho ltr (∧→ s) (ind ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ s) (ind ←∧))
-- --     ¬nho ()
-- --   ¬trho (∧c ltr) (∧→ s) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce∧→↓
-- --   ¬trho (∧c ltr) (∧→ s) (ind ←∧) ¬ho (←∧∧c ut) = ¬trho ltr (s ←∧) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (∧→ ind))
-- --     ¬nho ()
-- --   ¬trho (∧c ltr) (∧→ s) (∧→ ind) ¬ho (∧→∧c ut) = ¬trho ltr (s ←∧) (ind ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (ind ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧←∧ x) = ¬ho (hitsAtLeastOnce∧→∧→ x)
-- --   ¬trho (∧c ltr) (s ←∧→ s₁) (ind ←∧) ¬ho (←∧∧c ut) = ¬trho ltr (s₁ ←∧→ s) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∧→ s) (∧→ ind))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
-- --   ¬trho (∧c ltr) (s ←∧→ s₁) (∧→ ind) ¬ho (∧→∧c ut)  = ¬trho ltr (s₁ ←∧→ s) (ind ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∧→ s) (ind ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
-- --   ¬trho (∨c ltr) ↓ .(_ ←∨) ¬ho (←∨∨c ut) = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (∨c ltr) ↓ .(∨→ _) ¬ho (∨→∨c ut) = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (∨c ltr) (s ←∨) (ind ←∨) ¬ho (←∨∨c ut) = ¬trho ltr (∨→ s) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ s) (∨→ ind))
-- --     ¬nho (hitsAtLeastOnce∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨←∨ x)
-- --   ¬trho (∨c ltr) (s ←∨) (∨→ ind) ¬ho (∨→∨c ut) = ¬trho ltr (∨→ s) (ind ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ s) (ind ←∨))
-- --     ¬nho ()
-- --   ¬trho (∨c ltr) (∨→ s) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce∨→↓
-- --   ¬trho (∨c ltr) (∨→ s) (ind ←∨) ¬ho (←∨∨c ut) = ¬trho ltr (s ←∨) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (∨→ ind))
-- --     ¬nho ()
-- --   ¬trho (∨c ltr) (∨→ s) (∨→ ind) ¬ho (∨→∨c ut) = ¬trho ltr (s ←∨) (ind ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (ind ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨←∨ x) = ¬ho (hitsAtLeastOnce∨→∨→ x)
-- --   ¬trho (∨c ltr) (s ←∨→ s₁) (ind ←∨) ¬ho (←∨∨c ut) = ¬trho ltr (s₁ ←∨→ s) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∨→ s) (∨→ ind))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
-- --   ¬trho (∨c ltr) (s ←∨→ s₁) (∨→ ind) ¬ho (∨→∨c ut)  = ¬trho ltr (s₁ ←∨→ s) (ind ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s₁ ←∨→ s) (ind ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
-- --   ¬trho (∧∧d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (∧∧d ltr) (↓ ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut)
-- --                                       = λ _ → ¬ho (hitsAtLeastOnce←∧←∧ hitsAtLeastOnce↓)
-- --   ¬trho (∧∧d ltr) ((s ←∧) ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (s ←∧) (ind ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (ind ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧←∧ x))
  
-- --   ¬trho (∧∧d ltr) ((∧→ s) ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut)  = ¬trho ltr (∧→ (s ←∧)) (ind ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧)) (ind ←∧))
-- --     ¬nho ()
  
-- --   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧)) (ind ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧)) (ind ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→←∧ x))
  
-- --   ¬trho (∧∧d ltr) (↓ ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = λ _ → ¬ho (hitsAtLeastOnce←∧←∧ hitsAtLeastOnce↓)
-- --   ¬trho (∧∧d ltr) ((s ←∧) ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧) (∧→ (ind ←∧)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (∧→ (ind ←∧)))
-- --     ¬nho ()
  
-- --   ¬trho (∧∧d ltr) ((∧→ s) ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (∧→ (s ←∧)) (∧→ (ind ←∧)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧)) (∧→ (ind ←∧)))
-- --     ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce∧→∧→ x))
  
-- --   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧)) (∧→ (ind ←∧)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧)) (∧→ (ind ←∧)))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→∧→ x))
  
-- --   ¬trho (∧∧d ltr) (↓ ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧)) (∧→ (∧→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧)) (∧→ (∧→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ ())
  
-- --   ¬trho (∧∧d ltr) ((s ←∧) ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧) (∧→ (∧→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧) (∧→ (∧→ ind)))
-- --     ¬nho ()
  
-- --   ¬trho (∧∧d ltr) ((∧→ s) ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (∧→ (s ←∧)) (∧→ (∧→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧)) (∧→ (∧→ ind)))
-- --     ¬nho (hitsAtLeastOnce∧→∧→ ())
  
-- --   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧)) (∧→ (∧→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧)) (∧→ (∧→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ ())
  
-- --   ¬trho (∧∧d ltr) (∧→ s) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (∧→ (∧→ s)) (ind ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ (∧→ s)) (ind ←∧))
-- --     ¬nho ()
  
-- --   ¬trho (∧∧d ltr) (∧→ s) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (∧→ (∧→ s)) (∧→ (ind ←∧)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ (∧→ s)) (∧→ (ind ←∧)))
-- --     ¬nho (hitsAtLeastOnce∧→∧→ ())
  
-- --   ¬trho (∧∧d ltr) (∧→ s) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (∧→ (∧→ s)) (∧→ (∧→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ (∧→ s)) (∧→ (∧→ ind)))
-- --     ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce∧→∧→ x)
  
  
  
-- --   ¬trho (∧∧d ltr) (↓ ←∧→ s₁) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧→ s₁)) (ind ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧→ s₁)) (ind ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓)
   
-- --   ¬trho (∧∧d ltr) ((s ←∧) ←∧→ s₁) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (∧→ s₁)) (ind ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (∧→ s₁)) (ind ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧←∧ x))
  
-- --   ¬trho (∧∧d ltr) ((∧→ s) ←∧→ s₁) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut) = ¬trho ltr (∧→ (s ←∧→ s₁)) (ind ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧→ s₁)) (ind ←∧))
-- --     ¬nho ()
  
-- --   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧→ s₂) ((ind ←∧) ←∧) ¬ho (←∧]←∧∧∧d ut)  = ¬trho ltr (s ←∧→ (s₁ ←∧→ s₂)) (ind ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧→ s₂)) (ind ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ x))
  
  
-- --   ¬trho (∧∧d ltr) (↓ ←∧→ s₁) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (ind ←∧)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (ind ←∧)))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce←∧→←∧ hitsAtLeastOnce↓)
   
-- --   ¬trho (∧∧d ltr) ((s ←∧) ←∧→ s₁) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (∧→ s₁)) (∧→ (ind ←∧)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (∧→ s₁)) (∧→ (ind ←∧)))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ ())
  
-- --   ¬trho (∧∧d ltr) ((∧→ s) ←∧→ s₁) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (∧→ (s ←∧→ s₁)) (∧→ (ind ←∧)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧→ s₁)) (∧→ (ind ←∧)))
-- --     ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce∧→∧→ x))
  
-- --   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧→ s₂) ((∧→ ind) ←∧) ¬ho (∧→]←∧∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (ind ←∧)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (ind ←∧)))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ x))
  
-- --   ¬trho (∧∧d ltr) (↓ ←∧→ s₁) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (∧→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∧→ (↓ ←∧→ s₁)) (∧→ (∧→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
   
-- --   ¬trho (∧∧d ltr) ((s ←∧) ←∧→ s₁) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧→ (∧→ s₁)) (∧→ (∧→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (∧→ s₁)) (∧→ (∧→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
-- --   ¬trho (∧∧d ltr) ((∧→ s) ←∧→ s₁) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (∧→ (s ←∧→ s₁)) (∧→ (∧→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ (s ←∧→ s₁)) (∧→ (∧→ ind)))
-- --     ¬nho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
-- --   ¬trho (∧∧d ltr) ((s ←∧→ s₁) ←∧→ s₂) (∧→ ind) ¬ho (∧→∧∧d ut) = ¬trho ltr (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (∧→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∧→ (s₁ ←∧→ s₂)) (∧→ (∧→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
-- --   ¬trho (¬∧∧d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (¬∧∧d ltr) (s ←∧) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce←∧↓
-- --   ¬trho (¬∧∧d ltr) (s ←∧) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s ←∧) ←∧) ((ind ←∧) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s ←∧) ←∧) ((ind ←∧) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧←∧ x)
  
-- --   ¬trho (¬∧∧d ltr) (s ←∧) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s ←∧) ←∧) ((∧→ ind) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s ←∧) ←∧) ((∧→ ind) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧←∧ ())
  
-- --   ¬trho (¬∧∧d ltr) (s ←∧) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s ←∧) ←∧) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s ←∧) ←∧) (∧→ ind))
-- --     ¬nho ()
  
-- --   ¬trho (¬∧∧d ltr) (∧→ ↓) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ ())
  
-- --   ¬trho (¬∧∧d ltr) (∧→ (s ←∧)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((∧→ s) ←∧) ((ind ←∧) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧) ((ind ←∧) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧←∧ ())
  
-- --   ¬trho (¬∧∧d ltr) (∧→ (∧→ s)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr (∧→ s) ((ind ←∧) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ s) ((ind ←∧) ←∧))
-- --     ¬nho ()
  
-- --   ¬trho (¬∧∧d ltr) (∧→ (s ←∧→ s₁)) (ind ←∧) ¬ho (←∧¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧→ s₁) ((ind ←∧) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧→ s₁) ((ind ←∧) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ ())
  
  
-- --   ¬trho (¬∧∧d ltr) (∧→ ↓) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr ((∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce∧→∧→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∧∧d ltr) (∧→ (s ←∧)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧) ((∧→ ind) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧) ((∧→ ind) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧←∧ x))
  
-- --   ¬trho (¬∧∧d ltr) (∧→ (∧→ s)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr (∧→ s) ((∧→ ind) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ s) ((∧→ ind) ←∧))
-- --     ¬nho ()
  
-- --   ¬trho (¬∧∧d ltr) (∧→ (s ←∧→ s₁)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧→ s₁) ((∧→ ind) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧→ s₁) ((∧→ ind) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce∧→∧→ x)) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→←∧ x))
  
  
-- --   ¬trho (¬∧∧d ltr) (∧→ ↓) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut)   = ¬trho ltr ((∧→ ↓) ←∧→ ↓) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∧→ ↓) ←∧→ ↓) (∧→ ind))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce∧→∧→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∧∧d ltr) (∧→ (s ←∧)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧) (∧→ ind))
-- --     ¬nho ()
  
-- --   ¬trho (¬∧∧d ltr) (∧→ (∧→ s)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr (∧→ s) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∧→ s) (∧→ ind))
-- --     ¬nho (hitsAtLeastOnce∧→∧→ x) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce∧→∧→ x))
  
-- --   ¬trho (¬∧∧d ltr) (∧→ (s ←∧→ s₁)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut)  = ¬trho ltr ((∧→ s) ←∧→ s₁) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∧→ s) ←∧→ s₁) (∧→ ind))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce∧→∧→ (hitsAtLeastOnce←∧→∧→ x))
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ ↓) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ ↓) ←∧→ ↓) ((ind ←∧) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧) ((ind ←∧) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧) ((ind ←∧) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (∧→ s)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧) ←∧→ s) ((ind ←∧) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧) ←∧→ s) ((ind ←∧) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧→ s₂)) (ind ←∧) ¬ho (←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧→ s₂) ((ind ←∧) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧→ s₂) ((ind ←∧) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→←∧ x)) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ ↓) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ ↓) ←∧→ ↓) ((∧→ ind) ←∧))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧) ((∧→ ind) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧) ((∧→ ind) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧←∧ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧←∧ x))
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (∧→ s)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧) ←∧→ s) ((∧→ ind) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧) ←∧→ s) ((∧→ ind) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ ())
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧→ s₂)) (∧→ (ind ←∧)) ¬ho (∧→[←∧¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧→ s₂) ((∧→ ind) ←∧) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧→ s₂) ((∧→ ind) ←∧))
-- --     ¬nho (hitsAtLeastOnce←∧→←∧ (hitsAtLeastOnce←∧→∧→ x)) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→←∧ x))
  
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ ↓) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ ↓) ←∧→ ↓) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ ↓) ←∧→ ↓) (∧→ ind))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce←∧→∧→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧) (∧→ ind))
-- --     ¬nho ()
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (∧→ s)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧) ←∧→ s) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧) ←∧→ s) (∧→ ind))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce∧→∧→ x))
  
-- --   ¬trho (¬∧∧d ltr) (s₁ ←∧→ (s ←∧→ s₂)) (∧→ (∧→ ind)) ¬ho (∧→[∧→¬∧∧d ut) = ¬trho ltr ((s₁ ←∧→ s) ←∧→ s₂) (∧→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∧→ s) ←∧→ s₂) (∧→ ind))
-- --     ¬nho (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→∧→ (hitsAtLeastOnce←∧→∧→ x))
  
  
-- --   ¬trho (∨∨d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (∨∨d ltr) (↓ ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut)
-- --                                       = λ _ → ¬ho (hitsAtLeastOnce←∨←∨ hitsAtLeastOnce↓)
-- --   ¬trho (∨∨d ltr) ((s ←∨) ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (s ←∨) (ind ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (ind ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨←∨ x) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨←∨ x))
  
-- --   ¬trho (∨∨d ltr) ((∨→ s) ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut)  = ¬trho ltr (∨→ (s ←∨)) (ind ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨)) (ind ←∨))
-- --     ¬nho ()
  
-- --   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨)) (ind ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨)) (ind ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→←∨ x))
  
-- --   ¬trho (∨∨d ltr) (↓ ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = λ _ → ¬ho (hitsAtLeastOnce←∨←∨ hitsAtLeastOnce↓)
-- --   ¬trho (∨∨d ltr) ((s ←∨) ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨) (∨→ (ind ←∨)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (∨→ (ind ←∨)))
-- --     ¬nho ()
  
-- --   ¬trho (∨∨d ltr) ((∨→ s) ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (∨→ (s ←∨)) (∨→ (ind ←∨)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨)) (∨→ (ind ←∨)))
-- --     ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce∨→∨→ x))
  
-- --   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨)) (∨→ (ind ←∨)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨)) (∨→ (ind ←∨)))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→∨→ x))
  
-- --   ¬trho (∨∨d ltr) (↓ ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨)) (∨→ (∨→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨)) (∨→ (∨→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ ())
  
-- --   ¬trho (∨∨d ltr) ((s ←∨) ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨) (∨→ (∨→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨) (∨→ (∨→ ind)))
-- --     ¬nho ()
  
-- --   ¬trho (∨∨d ltr) ((∨→ s) ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (∨→ (s ←∨)) (∨→ (∨→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨)) (∨→ (∨→ ind)))
-- --     ¬nho (hitsAtLeastOnce∨→∨→ ())
  
-- --   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨)) (∨→ (∨→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨)) (∨→ (∨→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ ())
  
-- --   ¬trho (∨∨d ltr) (∨→ s) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (∨→ (∨→ s)) (ind ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ (∨→ s)) (ind ←∨))
-- --     ¬nho ()
  
-- --   ¬trho (∨∨d ltr) (∨→ s) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (∨→ (∨→ s)) (∨→ (ind ←∨)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ (∨→ s)) (∨→ (ind ←∨)))
-- --     ¬nho (hitsAtLeastOnce∨→∨→ ())
  
-- --   ¬trho (∨∨d ltr) (∨→ s) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (∨→ (∨→ s)) (∨→ (∨→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ (∨→ s)) (∨→ (∨→ ind)))
-- --     ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce∨→∨→ x)
  
  
  
-- --   ¬trho (∨∨d ltr) (↓ ←∨→ s₁) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨→ s₁)) (ind ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨→ s₁)) (ind ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓)
   
-- --   ¬trho (∨∨d ltr) ((s ←∨) ←∨→ s₁) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (∨→ s₁)) (ind ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (∨→ s₁)) (ind ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨←∨ x))
  
-- --   ¬trho (∨∨d ltr) ((∨→ s) ←∨→ s₁) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut) = ¬trho ltr (∨→ (s ←∨→ s₁)) (ind ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨→ s₁)) (ind ←∨))
-- --     ¬nho ()
  
-- --   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨→ s₂) ((ind ←∨) ←∨) ¬ho (←∨]←∨∨∨d ut)  = ¬trho ltr (s ←∨→ (s₁ ←∨→ s₂)) (ind ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨→ s₂)) (ind ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ x))
  
  
-- --   ¬trho (∨∨d ltr) (↓ ←∨→ s₁) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (ind ←∨)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (ind ←∨)))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce←∨→←∨ hitsAtLeastOnce↓)
   
-- --   ¬trho (∨∨d ltr) ((s ←∨) ←∨→ s₁) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (∨→ s₁)) (∨→ (ind ←∨)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (∨→ s₁)) (∨→ (ind ←∨)))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ ())
  
-- --   ¬trho (∨∨d ltr) ((∨→ s) ←∨→ s₁) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (∨→ (s ←∨→ s₁)) (∨→ (ind ←∨)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨→ s₁)) (∨→ (ind ←∨)))
-- --     ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce∨→∨→ x))
  
-- --   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨→ s₂) ((∨→ ind) ←∨) ¬ho (∨→]←∨∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (ind ←∨)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (ind ←∨)))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ x))
  
-- --   ¬trho (∨∨d ltr) (↓ ←∨→ s₁) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (∨→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∨→ (↓ ←∨→ s₁)) (∨→ (∨→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
   
-- --   ¬trho (∨∨d ltr) ((s ←∨) ←∨→ s₁) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨→ (∨→ s₁)) (∨→ (∨→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (∨→ s₁)) (∨→ (∨→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
-- --   ¬trho (∨∨d ltr) ((∨→ s) ←∨→ s₁) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (∨→ (s ←∨→ s₁)) (∨→ (∨→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ (s ←∨→ s₁)) (∨→ (∨→ ind)))
-- --     ¬nho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
-- --   ¬trho (∨∨d ltr) ((s ←∨→ s₁) ←∨→ s₂) (∨→ ind) ¬ho (∨→∨∨d ut) = ¬trho ltr (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (∨→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∨→ (s₁ ←∨→ s₂)) (∨→ (∨→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
-- --   ¬trho (¬∨∨d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (¬∨∨d ltr) (s ←∨) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce←∨↓
-- --   ¬trho (¬∨∨d ltr) (s ←∨) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s ←∨) ←∨) ((ind ←∨) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s ←∨) ←∨) ((ind ←∨) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨←∨ x)
  
-- --   ¬trho (¬∨∨d ltr) (s ←∨) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s ←∨) ←∨) ((∨→ ind) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s ←∨) ←∨) ((∨→ ind) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨←∨ ())
  
-- --   ¬trho (¬∨∨d ltr) (s ←∨) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s ←∨) ←∨) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s ←∨) ←∨) (∨→ ind))
-- --     ¬nho ()
  
-- --   ¬trho (¬∨∨d ltr) (∨→ ↓) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ ())
  
-- --   ¬trho (¬∨∨d ltr) (∨→ (s ←∨)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((∨→ s) ←∨) ((ind ←∨) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨) ((ind ←∨) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨←∨ ())
  
-- --   ¬trho (¬∨∨d ltr) (∨→ (∨→ s)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr (∨→ s) ((ind ←∨) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ s) ((ind ←∨) ←∨))
-- --     ¬nho ()
  
-- --   ¬trho (¬∨∨d ltr) (∨→ (s ←∨→ s₁)) (ind ←∨) ¬ho (←∨¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨→ s₁) ((ind ←∨) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨→ s₁) ((ind ←∨) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ ())
  
  
-- --   ¬trho (¬∨∨d ltr) (∨→ ↓) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr ((∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce∨→∨→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∨∨d ltr) (∨→ (s ←∨)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨) ((∨→ ind) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨) ((∨→ ind) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨←∨ x))
  
-- --   ¬trho (¬∨∨d ltr) (∨→ (∨→ s)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr (∨→ s) ((∨→ ind) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ s) ((∨→ ind) ←∨))
-- --     ¬nho ()
  
-- --   ¬trho (¬∨∨d ltr) (∨→ (s ←∨→ s₁)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨→ s₁) ((∨→ ind) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨→ s₁) ((∨→ ind) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce∨→∨→ x)) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→←∨ x))
  
  
-- --   ¬trho (¬∨∨d ltr) (∨→ ↓) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut)   = ¬trho ltr ((∨→ ↓) ←∨→ ↓) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∨→ ↓) ←∨→ ↓) (∨→ ind))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce∨→∨→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∨∨d ltr) (∨→ (s ←∨)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨) (∨→ ind))
-- --     ¬nho ()
  
-- --   ¬trho (¬∨∨d ltr) (∨→ (∨→ s)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr (∨→ s) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∨→ s) (∨→ ind))
-- --     ¬nho (hitsAtLeastOnce∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce∨→∨→ x))
  
-- --   ¬trho (¬∨∨d ltr) (∨→ (s ←∨→ s₁)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut)  = ¬trho ltr ((∨→ s) ←∨→ s₁) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∨→ s) ←∨→ s₁) (∨→ ind))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ (hitsAtLeastOnce←∨→∨→ x))
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ ↓) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ ↓) ←∨→ ↓) ((ind ←∨) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨) ((ind ←∨) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨) ((ind ←∨) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (∨→ s)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨) ←∨→ s) ((ind ←∨) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨) ←∨→ s) ((ind ←∨) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨→ s₂)) (ind ←∨) ¬ho (←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨→ s₂) ((ind ←∨) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨→ s₂) ((ind ←∨) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→←∨ x)) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ ↓) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ ↓) ←∨→ ↓) ((∨→ ind) ←∨))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨) ((∨→ ind) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨) ((∨→ ind) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨←∨ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨←∨ x))
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (∨→ s)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨) ←∨→ s) ((∨→ ind) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨) ←∨→ s) ((∨→ ind) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ ())
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨→ s₂)) (∨→ (ind ←∨)) ¬ho (∨→[←∨¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨→ s₂) ((∨→ ind) ←∨) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨→ s₂) ((∨→ ind) ←∨))
-- --     ¬nho (hitsAtLeastOnce←∨→←∨ (hitsAtLeastOnce←∨→∨→ x)) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→←∨ x))
  
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ ↓) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ ↓) ←∨→ ↓) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ ↓) ←∨→ ↓) (∨→ ind))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce←∨→∨→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨) (∨→ ind))
-- --     ¬nho ()
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (∨→ s)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨) ←∨→ s) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨) ←∨→ s) (∨→ ind))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce∨→∨→ x))
  
-- --   ¬trho (¬∨∨d ltr) (s₁ ←∨→ (s ←∨→ s₂)) (∨→ (∨→ ind)) ¬ho (∨→[∨→¬∨∨d ut) = ¬trho ltr ((s₁ ←∨→ s) ←∨→ s₂) (∨→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∨→ s) ←∨→ s₂) (∨→ ind))
-- --     ¬nho (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→∨→ (hitsAtLeastOnce←∨→∨→ x))
  
  
-- --   ¬trho (∂∂d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (∂∂d ltr) (↓ ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut)
-- --                                       = λ _ → ¬ho (hitsAtLeastOnce←∂←∂ hitsAtLeastOnce↓)
-- --   ¬trho (∂∂d ltr) ((s ←∂) ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (s ←∂) (ind ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (ind ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂←∂ x) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂←∂ x))
  
-- --   ¬trho (∂∂d ltr) ((∂→ s) ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut)  = ¬trho ltr (∂→ (s ←∂)) (ind ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂)) (ind ←∂))
-- --     ¬nho ()
  
-- --   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂)) (ind ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂)) (ind ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→←∂ x))
  
-- --   ¬trho (∂∂d ltr) (↓ ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = λ _ → ¬ho (hitsAtLeastOnce←∂←∂ hitsAtLeastOnce↓)
-- --   ¬trho (∂∂d ltr) ((s ←∂) ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂) (∂→ (ind ←∂)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (∂→ (ind ←∂)))
-- --     ¬nho ()
  
-- --   ¬trho (∂∂d ltr) ((∂→ s) ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (∂→ (s ←∂)) (∂→ (ind ←∂)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂)) (∂→ (ind ←∂)))
-- --     ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce∂→∂→ x))
  
-- --   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂)) (∂→ (ind ←∂)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂)) (∂→ (ind ←∂)))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→∂→ x))
  
-- --   ¬trho (∂∂d ltr) (↓ ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂)) (∂→ (∂→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂)) (∂→ (∂→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ ())
  
-- --   ¬trho (∂∂d ltr) ((s ←∂) ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂) (∂→ (∂→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂) (∂→ (∂→ ind)))
-- --     ¬nho ()
  
-- --   ¬trho (∂∂d ltr) ((∂→ s) ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (∂→ (s ←∂)) (∂→ (∂→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂)) (∂→ (∂→ ind)))
-- --     ¬nho (hitsAtLeastOnce∂→∂→ ())
  
-- --   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂)) (∂→ (∂→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂)) (∂→ (∂→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ ())
  
-- --   ¬trho (∂∂d ltr) (∂→ s) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (∂→ (∂→ s)) (ind ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ (∂→ s)) (ind ←∂))
-- --     ¬nho ()
  
-- --   ¬trho (∂∂d ltr) (∂→ s) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (∂→ (∂→ s)) (∂→ (ind ←∂)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ (∂→ s)) (∂→ (ind ←∂)))
-- --     ¬nho (hitsAtLeastOnce∂→∂→ ())
  
-- --   ¬trho (∂∂d ltr) (∂→ s) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (∂→ (∂→ s)) (∂→ (∂→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ (∂→ s)) (∂→ (∂→ ind)))
-- --     ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce∂→∂→ x)
  
  
  
-- --   ¬trho (∂∂d ltr) (↓ ←∂→ s₁) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂→ s₁)) (ind ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂→ s₁)) (ind ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓)
   
-- --   ¬trho (∂∂d ltr) ((s ←∂) ←∂→ s₁) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (∂→ s₁)) (ind ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (∂→ s₁)) (ind ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂←∂ x))
  
-- --   ¬trho (∂∂d ltr) ((∂→ s) ←∂→ s₁) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut) = ¬trho ltr (∂→ (s ←∂→ s₁)) (ind ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂→ s₁)) (ind ←∂))
-- --     ¬nho ()
  
-- --   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂→ s₂) ((ind ←∂) ←∂) ¬ho (←∂]←∂∂∂d ut)  = ¬trho ltr (s ←∂→ (s₁ ←∂→ s₂)) (ind ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂→ s₂)) (ind ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ x))
  
  
-- --   ¬trho (∂∂d ltr) (↓ ←∂→ s₁) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (ind ←∂)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (ind ←∂)))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce←∂→←∂ hitsAtLeastOnce↓)
   
-- --   ¬trho (∂∂d ltr) ((s ←∂) ←∂→ s₁) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (∂→ s₁)) (∂→ (ind ←∂)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (∂→ s₁)) (∂→ (ind ←∂)))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ ())
  
-- --   ¬trho (∂∂d ltr) ((∂→ s) ←∂→ s₁) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (∂→ (s ←∂→ s₁)) (∂→ (ind ←∂)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂→ s₁)) (∂→ (ind ←∂)))
-- --     ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce∂→∂→ x))
  
-- --   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂→ s₂) ((∂→ ind) ←∂) ¬ho (∂→]←∂∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (ind ←∂)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (ind ←∂)))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ x))
  
-- --   ¬trho (∂∂d ltr) (↓ ←∂→ s₁) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (∂→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (↓ ←∂→ (↓ ←∂→ s₁)) (∂→ (∂→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
   
-- --   ¬trho (∂∂d ltr) ((s ←∂) ←∂→ s₁) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂→ (∂→ s₁)) (∂→ (∂→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (∂→ s₁)) (∂→ (∂→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
-- --   ¬trho (∂∂d ltr) ((∂→ s) ←∂→ s₁) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (∂→ (s ←∂→ s₁)) (∂→ (∂→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ (s ←∂→ s₁)) (∂→ (∂→ ind)))
-- --     ¬nho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
-- --   ¬trho (∂∂d ltr) ((s ←∂→ s₁) ←∂→ s₂) (∂→ ind) ¬ho (∂→∂∂d ut) = ¬trho ltr (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (∂→ ind)) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (s ←∂→ (s₁ ←∂→ s₂)) (∂→ (∂→ ind)))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
-- --   ¬trho (¬∂∂d ltr) ↓ ind ¬ho ut = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬trho (¬∂∂d ltr) (s ←∂) ↓ ¬ho ut = λ _ → ¬ho hitsAtLeastOnce←∂↓
-- --   ¬trho (¬∂∂d ltr) (s ←∂) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s ←∂) ←∂) ((ind ←∂) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s ←∂) ←∂) ((ind ←∂) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂←∂ x)
  
-- --   ¬trho (¬∂∂d ltr) (s ←∂) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s ←∂) ←∂) ((∂→ ind) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s ←∂) ←∂) ((∂→ ind) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂←∂ ())
  
-- --   ¬trho (¬∂∂d ltr) (s ←∂) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s ←∂) ←∂) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s ←∂) ←∂) (∂→ ind))
-- --     ¬nho ()
  
-- --   ¬trho (¬∂∂d ltr) (∂→ ↓) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ ())
  
-- --   ¬trho (¬∂∂d ltr) (∂→ (s ←∂)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((∂→ s) ←∂) ((ind ←∂) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂) ((ind ←∂) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂←∂ ())
  
-- --   ¬trho (¬∂∂d ltr) (∂→ (∂→ s)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr (∂→ s) ((ind ←∂) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ s) ((ind ←∂) ←∂))
-- --     ¬nho ()
  
-- --   ¬trho (¬∂∂d ltr) (∂→ (s ←∂→ s₁)) (ind ←∂) ¬ho (←∂¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂→ s₁) ((ind ←∂) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂→ s₁) ((ind ←∂) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ ())
  
  
-- --   ¬trho (¬∂∂d ltr) (∂→ ↓) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr ((∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce∂→∂→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∂∂d ltr) (∂→ (s ←∂)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂) ((∂→ ind) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂) ((∂→ ind) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂←∂ x))
  
-- --   ¬trho (¬∂∂d ltr) (∂→ (∂→ s)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr (∂→ s) ((∂→ ind) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ s) ((∂→ ind) ←∂))
-- --     ¬nho ()
  
-- --   ¬trho (¬∂∂d ltr) (∂→ (s ←∂→ s₁)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂→ s₁) ((∂→ ind) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂→ s₁) ((∂→ ind) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce∂→∂→ x)) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→←∂ x))
  
  
-- --   ¬trho (¬∂∂d ltr) (∂→ ↓) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut)   = ¬trho ltr ((∂→ ↓) ←∂→ ↓) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∂→ ↓) ←∂→ ↓) (∂→ ind))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce∂→∂→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∂∂d ltr) (∂→ (s ←∂)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂) (∂→ ind))
-- --     ¬nho ()
  
-- --   ¬trho (¬∂∂d ltr) (∂→ (∂→ s)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr (∂→ s) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce (∂→ s) (∂→ ind))
-- --     ¬nho (hitsAtLeastOnce∂→∂→ x) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce∂→∂→ x))
  
-- --   ¬trho (¬∂∂d ltr) (∂→ (s ←∂→ s₁)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut)  = ¬trho ltr ((∂→ s) ←∂→ s₁) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((∂→ s) ←∂→ s₁) (∂→ ind))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce∂→∂→ (hitsAtLeastOnce←∂→∂→ x))
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ ↓) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ ↓) ←∂→ ↓) ((ind ←∂) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂) ((ind ←∂) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂) ((ind ←∂) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (∂→ s)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂) ←∂→ s) ((ind ←∂) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂) ←∂→ s) ((ind ←∂) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂→ s₂)) (ind ←∂) ¬ho (←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂→ s₂) ((ind ←∂) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂→ s₂) ((ind ←∂) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→←∂ x)) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ ↓) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ ↓) ←∂→ ↓) ((∂→ ind) ←∂))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂) ((∂→ ind) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂) ((∂→ ind) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂←∂ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂←∂ x))
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (∂→ s)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂) ←∂→ s) ((∂→ ind) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂) ←∂→ s) ((∂→ ind) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ ())
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂→ s₂)) (∂→ (ind ←∂)) ¬ho (∂→[←∂¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂→ s₂) ((∂→ ind) ←∂) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂→ s₂) ((∂→ ind) ←∂))
-- --     ¬nho (hitsAtLeastOnce←∂→←∂ (hitsAtLeastOnce←∂→∂→ x)) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→←∂ x))
  
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ ↓) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ ↓) ←∂→ ↓) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ ↓) ←∂→ ↓) (∂→ ind))
-- --     ¬nho x = ¬ho (hitsAtLeastOnce←∂→∂→ hitsAtLeastOnce↓)
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂) (∂→ ind))
-- --     ¬nho ()
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (∂→ s)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂) ←∂→ s) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂) ←∂→ s) (∂→ ind))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce∂→∂→ x))
  
-- --   ¬trho (¬∂∂d ltr) (s₁ ←∂→ (s ←∂→ s₂)) (∂→ (∂→ ind)) ¬ho (∂→[∂→¬∂∂d ut) = ¬trho ltr ((s₁ ←∂→ s) ←∂→ s₂) (∂→ ind) ¬nho ut where
-- --     ¬nho : ¬ (hitsAtLeastOnce ((s₁ ←∂→ s) ←∂→ s₂) (∂→ ind))
-- --     ¬nho (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→∂→ (hitsAtLeastOnce←∂→∂→ x))
  
  
  




-- -- Extending a set gives us onlyInside and hitsAtLeastOnce immediately because the rest is empty.

-- ext⇒oi : ∀{i u pll ll} → ∀ {s} → {ind : IndexLL {i} {u} pll ll}
--          → onlyInside (s-extend ind s) ind
-- ext⇒oi {s = s} {↓} = oIs↓
-- ext⇒oi {s = s} {ic d ind} = oIic {{ieq = ext⇒oi}}


-- hoind+⇒ho : ∀{i u pll rll ll} → {s : SetLL {i} {u} ll}
--             → {ind : IndexLL pll ll}
--             → (lind : IndexLL rll pll)
--             → {{eq : hitsAtLeastOnce s (ind +ᵢ lind)}}
--             → (hitsAtLeastOnce s ind) 
-- hoind+⇒ho {s = s} {↓} lind {{eq}} = hLOs↓
-- hoind+⇒ho {s = ↓} {ic d ind} lind {{eq}} = hLO↓ic
-- hoind+⇒ho {s = sic ds s} {ic .ds ind} lind {{hLOsic}} = hLOsic {{ieq = hoind+⇒ho lind}}
-- hoind+⇒ho {s = sbc s s₁} {ic d ind} lind {{hLOsbc}} = hLOsbc {{ieq = hoind+⇒ho lind}}

  

























-- -- module _ where

-- --   ¬ord&ext⇒¬ho' : ∀{i u pll rll ll tll} → ∀ (s : SetLL tll) → (ind : IndexLL {i} {u} pll ll)
-- --         → (lind : IndexLL rll ll) → (nord : ¬ Orderedᵢ lind ind) → (fnord : ¬ Orderedᵢ ind lind)
-- --         → ¬ hitsAtLeastOnce (extendg ind s) (¬ord-morph lind ind tll fnord)
-- --   ¬ord&ext⇒¬ho' s ↓ lind nord _ = λ _ → nord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&ext⇒¬ho' s (ind ←∧) ↓ nord fnord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
-- --   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∧ ri} {tll} s (ind ←∧) (lind ←∧) nord fnord = hf where
  
-- --     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (SetLL (_ ∧ ri) ∋ (extendg ind s ←∧)) ((¬ord-morph lind ind tll (¬ord-spec fnord)) ←∧)
-- --     hf (hitsAtLeastOnce←∧←∧ x) = is x
  
-- --   ¬ord&ext⇒¬ho' s (ind ←∧) (∧→ lind) nord _ = λ ()
-- --   ¬ord&ext⇒¬ho' s (∧→ ind) ↓ nord _ = λ _ → nord (a≤ᵢb ≤ᵢ↓)
-- --   ¬ord&ext⇒¬ho' s (∧→ ind) (lind ←∧) nord _ = λ ()
-- --   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∧ ri} {tll} s (∧→ ind) (∧→ lind) nord fnord = hf where
  
-- --     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (SetLL (li ∧ _) ∋ (∧→ extendg ind s)) (∧→ (¬ord-morph lind ind tll (¬ord-spec fnord)))
-- --     hf (hitsAtLeastOnce∧→∧→ x) = is x
-- --   ¬ord&ext⇒¬ho' s (ind ←∨) ↓ nord _ = λ _ → nord (a≤ᵢb ≤ᵢ↓)
-- --   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∨ ri} {tll} s (ind ←∨) (lind ←∨) nord fnord = hf where
  
-- --     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (SetLL (_ ∨ ri) ∋ (extendg ind s ←∨)) ((¬ord-morph lind ind tll (¬ord-spec fnord)) ←∨)
-- --     hf (hitsAtLeastOnce←∨←∨ x) = is x
  
-- --   ¬ord&ext⇒¬ho' s (ind ←∨) (∨→ lind) nord _ = λ ()
-- --   ¬ord&ext⇒¬ho' s (∨→ ind) ↓ nord _ = λ _ → nord (a≤ᵢb ≤ᵢ↓)
-- --   ¬ord&ext⇒¬ho' s (∨→ ind) (lind ←∨) nord _ = λ ()
-- --   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∨ ri} {tll} s (∨→ ind) (∨→ lind) nord fnord = hf where
  
-- --     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (SetLL (li ∨ _) ∋ (∨→ extendg ind s)) (∨→ (¬ord-morph lind ind tll (¬ord-spec fnord)))
-- --     hf (hitsAtLeastOnce∨→∨→ x) = is x
  
-- --   ¬ord&ext⇒¬ho' s (ind ←∂) ↓ nord _ = λ _ → nord (a≤ᵢb ≤ᵢ↓)
-- --   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∂ ri} {tll} s (ind ←∂) (lind ←∂) nord fnord = hf where
  
-- --     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (SetLL (_ ∂ ri) ∋ (extendg ind s ←∂)) ((¬ord-morph lind ind tll (¬ord-spec fnord)) ←∂)
-- --     hf (hitsAtLeastOnce←∂←∂ x) = is x
  
-- --   ¬ord&ext⇒¬ho' s (ind ←∂) (∂→ lind) nord _ = λ ()
-- --   ¬ord&ext⇒¬ho' s (∂→ ind) ↓ nord _ = λ _ → nord (a≤ᵢb ≤ᵢ↓)
-- --   ¬ord&ext⇒¬ho' s (∂→ ind) (lind ←∂) nord _ = λ ()
-- --   ¬ord&ext⇒¬ho' {pll = pll} {_} {ll = li ∂ ri} {tll} s (∂→ ind) (∂→ lind) nord fnord = hf where
  
-- --     is = ¬ord&ext⇒¬ho' s ind lind (¬ord-spec nord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (SetLL (li ∂ _) ∋ (∂→ extendg ind s)) (∂→ (¬ord-morph lind ind tll (¬ord-spec fnord)))
-- --     hf (hitsAtLeastOnce∂→∂→ x) = is x
    
-- --   ¬ord&ext⇒¬ho : ∀{i u pll rll ll tll} → ∀ (s : SetLL tll) → (ind : IndexLL {i} {u} pll ll)
-- --           → (lind : IndexLL rll ll) → (nord : ¬ Orderedᵢ lind ind)
-- --           → ¬ hitsAtLeastOnce (extendg ind s) (¬ord-morph lind ind tll (flipNotOrdᵢ nord))
-- --   ¬ord&ext⇒¬ho s ind lind nord = ¬ord&ext⇒¬ho' s ind lind nord (flipNotOrdᵢ nord)



-- -- module _ where


-- --   ¬ord&¬ho-repl⇒¬ho' : ∀{i u rll pll ll tll} → (lind : IndexLL {i} {u} rll ll) → (s : SetLL ll) → ∀{rs : SetLL tll}
-- --         → ¬ (hitsAtLeastOnce s lind) → (ind : IndexLL pll ll)
-- --         → (nord : ¬ Orderedᵢ lind ind) → (fnord : ¬ Orderedᵢ ind lind)
-- --         → ¬ (hitsAtLeastOnce (replacePartOf s to rs at ind) (¬ord-morph lind ind tll fnord))
-- --   ¬ord&¬ho-repl⇒¬ho' ↓ s ¬ho ind ¬ord fnord = λ _ → ¬ord (a≤ᵢb ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧) {rs} ¬ho (ind ←∧) ¬ord fnord x
-- --                                    with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce←∧←∧ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧) {rs} ¬ho (ind ←∧) ¬ord fnord (hitsAtLeastOnce←∧←∧ x) | r = ⊥-elim (r x)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧) ¬ho (∧→ ind) ¬ord fnord (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (∧→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (lind ←∧) (∧→ s) {rs} ¬ho (ind ←∧) ¬ord fnord = hf where
    
-- --     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (extendg ind rs ←∧→ s) (¬ord-morph (lind ←∧) (ind ←∧) tll fnord)
-- --     hf (hitsAtLeastOnce←∧→←∧ x) = h1 x

-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (∧→ s) ¬ho (∧→ ind) ¬ord fnord = λ ()
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧→ s₁) {rs} ¬ho (ind ←∧) ¬ord fnord (hitsAtLeastOnce←∧→←∧ x) = is x where
-- --     hf : ¬ hitsAtLeastOnce s lind
-- --     hf x = ¬ho (hitsAtLeastOnce←∧→←∧ x)
  
-- --     is = ¬ord&¬ho-repl⇒¬ho' lind s {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∧) (s ←∧→ s₁) {rs} ¬ho (∧→ ind) ¬ord fnord (hitsAtLeastOnce←∧→←∧ x) = ¬ho (hitsAtLeastOnce←∧→←∧ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (s ←∧) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (s ←∧) ¬ho (ind ←∧) ¬ord fnord = λ ()
-- --   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (∧→ lind) (s ←∧) {rs} ¬ho (∧→ ind) ¬ord fnord = hf where
    
-- --     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (s ←∧→ extendg ind rs) (¬ord-morph (∧→ lind) (∧→ ind) tll (fnord))
-- --     hf (hitsAtLeastOnce←∧→∧→ x) = h1 x
  
-- --   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (∧→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (∧→ s) ¬ho (ind ←∧) ¬ord fnord (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce∧→∧→ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (∧→ s) {rs} ¬ho (∧→ ind) ¬ord fnord x
-- --                              with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce∧→∧→ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
-- --   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (∧→ s) ¬ho (∧→ ind) ¬ord fnord (hitsAtLeastOnce∧→∧→ x) | r = r x
-- --   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (s ←∧→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) ¬ord fnord (hitsAtLeastOnce←∧→∧→ x) = ¬ho (hitsAtLeastOnce←∧→∧→ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (∧→ lind) (s ←∧→ s₁) {rs} ¬ho (∧→ ind) ¬ord fnord (hitsAtLeastOnce←∧→∧→ x) = is x where
-- --     hf : ¬ hitsAtLeastOnce s₁ lind
-- --     hf x = ¬ho (hitsAtLeastOnce←∧→∧→ x)
  
-- --     is = ¬ord&¬ho-repl⇒¬ho' lind s₁ {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨) {rs} ¬ho (ind ←∨) ¬ord fnord x
-- --                                    with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce←∨←∨ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨) {rs} ¬ho (ind ←∨) ¬ord fnord (hitsAtLeastOnce←∨←∨ x) | r = ⊥-elim (r x)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨) ¬ho (∨→ ind) ¬ord fnord (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨←∨ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (∨→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (lind ←∨) (∨→ s) {rs} ¬ho (ind ←∨) ¬ord fnord = hf where
-- --     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (extendg ind rs ←∨→ s) (¬ord-morph (lind ←∨) (ind ←∨) tll (fnord))
-- --     hf (hitsAtLeastOnce←∨→←∨ x) = h1 x
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (∨→ s) ¬ho (∨→ ind) ¬ord fnord = λ ()
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨→ s₁) {rs} ¬ho (ind ←∨) ¬ord fnord (hitsAtLeastOnce←∨→←∨ x) = is x where
-- --     hf : ¬ hitsAtLeastOnce s lind
-- --     hf x = ¬ho (hitsAtLeastOnce←∨→←∨ x)
  
-- --     is = ¬ord&¬ho-repl⇒¬ho' lind s {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∨) (s ←∨→ s₁) {rs} ¬ho (∨→ ind) ¬ord fnord (hitsAtLeastOnce←∨→←∨ x) = ¬ho (hitsAtLeastOnce←∨→←∨ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (s ←∨) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (s ←∨) ¬ho (ind ←∨) ¬ord fnord = λ ()
-- --   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (∨→ lind) (s ←∨) {rs} ¬ho (∨→ ind) ¬ord fnord = hf where
-- --     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (s ←∨→ extendg ind rs) (¬ord-morph (∨→ lind) (∨→ ind) tll (fnord))
-- --     hf (hitsAtLeastOnce←∨→∨→ x) = h1 x
  
-- --   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (∨→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (∨→ s) ¬ho (ind ←∨) ¬ord fnord (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (∨→ s) {rs} ¬ho (∨→ ind) ¬ord fnord x
-- --                              with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce∨→∨→ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
-- --   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (∨→ s) ¬ho (∨→ ind) ¬ord fnord (hitsAtLeastOnce∨→∨→ x) | r = r x
-- --   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (s ←∨→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) ¬ord fnord (hitsAtLeastOnce←∨→∨→ x) = ¬ho (hitsAtLeastOnce←∨→∨→ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (∨→ lind) (s ←∨→ s₁) {rs} ¬ho (∨→ ind) ¬ord fnord (hitsAtLeastOnce←∨→∨→ x) = is x where
-- --     hf : ¬ hitsAtLeastOnce s₁ lind
-- --     hf x = ¬ho (hitsAtLeastOnce←∨→∨→ x)
  
-- --     is = ¬ord&¬ho-repl⇒¬ho' lind s₁ {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂) {rs} ¬ho (ind ←∂) ¬ord fnord x
-- --                                    with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce←∂←∂ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂) {rs} ¬ho (ind ←∂) ¬ord fnord (hitsAtLeastOnce←∂←∂ x) | r = ⊥-elim (r x)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂) ¬ho (∂→ ind) ¬ord fnord (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂←∂ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (∂→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (lind ←∂) (∂→ s) {rs} ¬ho (ind ←∂) ¬ord fnord = hf where
-- --     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (extendg ind rs ←∂→ s) (¬ord-morph (lind ←∂) (ind ←∂) tll (fnord))
-- --     hf (hitsAtLeastOnce←∂→←∂ x) = h1 x
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (∂→ s) ¬ho (∂→ ind) ¬ord fnord = λ ()
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂→ s₁) {rs} ¬ho (ind ←∂) ¬ord fnord (hitsAtLeastOnce←∂→←∂ x) = is x where
-- --     hf : ¬ hitsAtLeastOnce s lind
-- --     hf x = ¬ho (hitsAtLeastOnce←∂→←∂ x)
  
-- --     is = ¬ord&¬ho-repl⇒¬ho' lind s {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
-- --   ¬ord&¬ho-repl⇒¬ho' (lind ←∂) (s ←∂→ s₁) {rs} ¬ho (∂→ ind) ¬ord fnord (hitsAtLeastOnce←∂→←∂ x) = ¬ho (hitsAtLeastOnce←∂→←∂ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) ↓ ¬ho ind ¬ord fnord = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (s ←∂) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (s ←∂) ¬ho (ind ←∂) ¬ord fnord = λ ()
-- --   ¬ord&¬ho-repl⇒¬ho' {tll = tll} (∂→ lind) (s ←∂) {rs} ¬ho (∂→ ind) ¬ord fnord = hf where
    
-- --     h1 = ¬ord&ext⇒¬ho' rs ind lind (¬ord-spec ¬ord) (¬ord-spec fnord)
  
-- --     hf : ¬ hitsAtLeastOnce (s ←∂→ extendg ind rs) (¬ord-morph (∂→ lind) (∂→ ind) tll (fnord))
-- --     hf (hitsAtLeastOnce←∂→∂→ x) = h1 x
  
-- --   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (∂→ s) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (∂→ s) ¬ho (ind ←∂) ¬ord fnord (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce∂→∂→ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (∂→ s) {rs} ¬ho (∂→ ind) ¬ord fnord x
-- --                              with ¬ord&¬ho-repl⇒¬ho' lind s {rs} (λ z → ¬ho (hitsAtLeastOnce∂→∂→ z)) ind (¬ord-spec ¬ord) (¬ord-spec fnord) where
-- --   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (∂→ s) ¬ho (∂→ ind) ¬ord fnord (hitsAtLeastOnce∂→∂→ x) | r = r x
-- --   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (s ←∂→ s₁) ¬ho ↓ ¬ord fnord = λ _ → ¬ord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) ¬ord fnord (hitsAtLeastOnce←∂→∂→ x) = ¬ho (hitsAtLeastOnce←∂→∂→ x)
-- --   ¬ord&¬ho-repl⇒¬ho' (∂→ lind) (s ←∂→ s₁) {rs} ¬ho (∂→ ind) ¬ord fnord (hitsAtLeastOnce←∂→∂→ x) = is x where
-- --     hf : ¬ hitsAtLeastOnce s₁ lind
-- --     hf x = ¬ho (hitsAtLeastOnce←∂→∂→ x)
  
-- --     is = ¬ord&¬ho-repl⇒¬ho' lind s₁ {rs} hf ind (¬ord-spec ¬ord) (¬ord-spec fnord)
  

-- --   ¬ord&¬ho-repl⇒¬ho : ∀{i u rll pll ll tll} → (lind : IndexLL {i} {u} rll ll) → (s : SetLL ll) → ∀{rs : SetLL tll}
-- --           → ¬ (hitsAtLeastOnce s lind) → (ind : IndexLL pll ll)
-- --           → (nord : ¬ Orderedᵢ lind ind)
-- --           → ¬ (hitsAtLeastOnce (replacePartOf s to rs at ind) (¬ord-morph lind ind tll (flipNotOrdᵢ nord)))
-- --   ¬ord&¬ho-repl⇒¬ho lind s ¬ho ind nord = ¬ord&¬ho-repl⇒¬ho' lind s ¬ho ind nord (flipNotOrdᵢ nord)


-- -- module _ where

-- --     -- Not being Ordered is only necessary to morph the type of the index. but this statement is true in general.
-- --   ¬ord&¬ho-del⇒¬ho' : ∀{i u rll pll ll tll} → (lind : IndexLL {i} {u} rll ll) → (s : SetLL ll)
-- --         → ¬ (hitsAtLeastOnce s lind) → (ind : IndexLL pll ll) → ∀{ds}
-- --         → (nord : ¬ Orderedᵢ lind ind) → (fnord : ¬ Orderedᵢ ind lind)
-- --         → ¬∅ ds ≡ del s ind tll
-- --         → ¬ (hitsAtLeastOnce ds (¬ord-morph lind ind tll fnord))
-- --   ¬ord&¬ho-del⇒¬ho' ↓ s ¬ho ind nord fnord eqd = λ _ → nord (a≤ᵢb ≤ᵢ↓)
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∧) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∧) ↓ ¬ho (ind ←∧) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧) ¬ho (ind ←∧) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧) ¬ho (ind ←∧) nord fnord () y | ∅ | r
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧) ¬ho (ind ←∧) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
  
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∧) (∧→ s) ¬ho (ind ←∧) nord fnord refl = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord eqd with del s ind tll | inspect (del s ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord refl | ∅ | r = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
  
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∧) ↓ ¬ho (∧→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∧) (s ←∧) ¬ho (∧→ ind) nord fnord refl (hitsAtLeastOnce←∧←∧ x) = ¬ho (hitsAtLeastOnce←∧←∧ x)
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (∧→ s) ¬ho (∧→ ind) nord fnord eqd with del s ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (∧→ s) ¬ho (∧→ ind) nord fnord () | ∅
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (∧→ s) ¬ho (∧→ ind) nord fnord refl | ¬∅ x = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord eqd y with del s₁ ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∧→←∧ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∧) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∧→←∧ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' (∧→ lind) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-del⇒¬ho' (∧→ lind) ↓ ¬ho (ind ←∧) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧) ¬ho (ind ←∧) nord fnord eqd with del s ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧) ¬ho (ind ←∧) nord fnord () | ∅
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧) ¬ho (ind ←∧) nord fnord refl | ¬∅ x = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' (∧→ lind) (∧→ s) ¬ho (ind ←∧) nord fnord refl y = ¬ho (hitsAtLeastOnce∧→∧→ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord eqd y with del s ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∧→∧→ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (ind ←∧) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∧→∧→ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' (∧→ lind) ↓ ¬ho (∧→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' (∧→ lind) (s ←∧) ¬ho (∧→ ind) nord fnord refl = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (∧→ s) ¬ho (∧→ ind) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (∧→ s) ¬ho (∧→ ind) nord fnord () y | ∅ | r
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (∧→ s) ¬ho (∧→ ind) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord eqd with del s₁ ind tll | inspect (del s₁ ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord refl | ∅ | r =  λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∧→ lind) (s ←∧→ s₁) ¬ho (∧→ ind) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s₁ (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∨) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∨) ↓ ¬ho (ind ←∨) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨) ¬ho (ind ←∨) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨) ¬ho (ind ←∨) nord fnord () y | ∅ | r
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨) ¬ho (ind ←∨) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∨) (∨→ s) ¬ho (ind ←∨) nord fnord refl = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord eqd with del s ind tll | inspect (del s ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord refl | ∅ | r = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∨) ↓ ¬ho (∨→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∨) (s ←∨) ¬ho (∨→ ind) nord fnord refl x = ¬ho (hitsAtLeastOnce←∨←∨ (ho-spec x))
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (∨→ s) ¬ho (∨→ ind) nord fnord eqd with del s ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (∨→ s) ¬ho (∨→ ind) nord fnord () | ∅
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (∨→ s) ¬ho (∨→ ind) nord fnord refl | ¬∅ x = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord eqd y with del s₁ ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∨→←∨ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∨) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∨→←∨ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' (∨→ lind) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-del⇒¬ho' (∨→ lind) ↓ ¬ho (ind ←∨) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨) ¬ho (ind ←∨) nord fnord eqd with del s ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨) ¬ho (ind ←∨) nord fnord () | ∅
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨) ¬ho (ind ←∨) nord fnord refl | ¬∅ x = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' (∨→ lind) (∨→ s) ¬ho (ind ←∨) nord fnord refl (hitsAtLeastOnce∨→∨→ x) = ¬ho (hitsAtLeastOnce∨→∨→ x)
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord eqd y with del s ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∨→∨→ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (ind ←∨) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∨→∨→ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' (∨→ lind) ↓ ¬ho (∨→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' (∨→ lind) (s ←∨) ¬ho (∨→ ind) nord fnord refl = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (∨→ s) ¬ho (∨→ ind) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (∨→ s) ¬ho (∨→ ind) nord fnord () y | ∅ | r
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (∨→ s) ¬ho (∨→ ind) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord eqd with del s₁ ind tll | inspect (del s₁ ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord refl | ∅ | r = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∨→ lind) (s ←∨→ s₁) ¬ho (∨→ ind) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s₁ (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∂) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∂) ↓ ¬ho (ind ←∂) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂) ¬ho (ind ←∂) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂) ¬ho (ind ←∂) nord fnord () y | ∅ | r
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂) ¬ho (ind ←∂) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∂) (∂→ s) ¬ho (ind ←∂) nord fnord refl = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord eqd with del s ind tll | inspect (del s ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord refl | ∅ | r = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∂) ↓ ¬ho (∂→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' (lind ←∂) (s ←∂) ¬ho (∂→ ind) nord fnord refl y = ¬ho (hitsAtLeastOnce←∂←∂ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (∂→ s) ¬ho (∂→ ind) nord fnord eqd with del s ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (∂→ s) ¬ho (∂→ ind) nord fnord () | ∅
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (∂→ s) ¬ho (∂→ ind) nord fnord refl | ¬∅ x = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord eqd y with del s₁ ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∂→←∂ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (lind ←∂) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∂→←∂ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' (∂→ lind) s ¬ho ↓ nord fnord eqd = λ _ → nord (b≤ᵢa ≤ᵢ↓)
-- --   ¬ord&¬ho-del⇒¬ho' (∂→ lind) ↓ ¬ho (ind ←∂) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂) ¬ho (ind ←∂) nord fnord eqd with del s ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂) ¬ho (ind ←∂) nord fnord () | ∅
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂) ¬ho (ind ←∂) nord fnord refl | ¬∅ x = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' (∂→ lind) (∂→ s) ¬ho (ind ←∂) nord fnord refl y = ¬ho (hitsAtLeastOnce∂→∂→ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord eqd y with del s ind tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord refl y | ∅ = ¬ho (hitsAtLeastOnce←∂→∂→ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (ind ←∂) nord fnord refl y | ¬∅ x = ¬ho (hitsAtLeastOnce←∂→∂→ (ho-spec y))
-- --   ¬ord&¬ho-del⇒¬ho' (∂→ lind) ↓ ¬ho (∂→ ind) nord fnord eqd = λ _ → ¬ho hitsAtLeastOnce↓
-- --   ¬ord&¬ho-del⇒¬ho' (∂→ lind) (s ←∂) ¬ho (∂→ ind) nord fnord refl = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (∂→ s) ¬ho (∂→ ind) nord fnord eqd y with del s ind tll | inspect (del s ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (∂→ s) ¬ho (∂→ ind) nord fnord () y | ∅ | r
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (∂→ s) ¬ho (∂→ ind) nord fnord refl y | ¬∅ x | [ eq ] = is (ho-spec y) where
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord eqd with del s₁ ind tll | inspect (del s₁ ind) tll
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord refl | ∅ | r = λ ()
-- --   ¬ord&¬ho-del⇒¬ho' {tll = tll} (∂→ lind) (s ←∂→ s₁) ¬ho (∂→ ind) nord fnord refl | ¬∅ x | [ eq ] = λ y → is (ho-spec y) where
-- --     is =  ¬ord&¬ho-del⇒¬ho' lind s₁ (¬ho-spec ¬ho) ind (¬ord-spec nord) (¬ord-spec fnord) (sym eq)
  
-- --   ¬ord&¬ho-del⇒¬ho : ∀{i u rll pll ll tll} → (lind : IndexLL {i} {u} rll ll) → (s : SetLL ll)
-- --         → ¬ (hitsAtLeastOnce s lind) → (ind : IndexLL pll ll) → ∀{ds}
-- --         → (nord : ¬ Orderedᵢ lind ind)
-- --         → ¬∅ ds ≡ del s ind tll
-- --         → ¬ (hitsAtLeastOnce ds (¬ord-morph lind ind tll (flipNotOrdᵢ nord)))
-- --   ¬ord&¬ho-del⇒¬ho lind s ¬ho ind nord deq =  ¬ord&¬ho-del⇒¬ho' lind s ¬ho ind nord (flipNotOrdᵢ nord) deq



-- -- rl&¬ho-trunc⇒¬ho : ∀{i u pll rll ll x} → ∀ (s : SetLL ll) → (ind : IndexLL {i} {u} pll ll)
-- --       → ¬ hitsAtLeastOnce s ind
-- --       → (lind : IndexLL rll ll) → (rl : lind ≤ᵢ ind)
-- --       → ¬∅ x ≡ truncSetLL s lind
-- --       → ¬ hitsAtLeastOnce x ((ind -ᵢ lind) rl)
-- -- rl&¬ho-trunc⇒¬ho s ind ¬ho ↓ ≤ᵢ↓ refl = ¬ho
-- -- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (lind ←∧) rl tc = ⊥-elim (¬ho hitsAtLeastOnce↓)
-- -- rl&¬ho-trunc⇒¬ho (s ←∧) ↓ ¬ho (lind ←∧) rl tc = λ _ → ¬ho hitsAtLeastOnce←∧↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∧) (ind ←∧) ¬ho (lind ←∧) (≤ᵢ←∧ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∧←∧ z)) lind rl tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∧) (∧→ ind) ¬ho (lind ←∧) () tc
-- -- rl&¬ho-trunc⇒¬ho (∧→ s) ind ¬ho (lind ←∧) rl ()
-- -- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) ↓ ¬ho (lind ←∧) rl tc = λ _ → ¬ho hitsAtLeastOnce←∧→↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) (ind ←∧) ¬ho (lind ←∧) (≤ᵢ←∧ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∧→←∧ z)) lind rl tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) (∧→ ind) ¬ho (lind ←∧) () tc
-- -- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (∧→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∧) ind ¬ho (∧→ lind) rl ()
-- -- rl&¬ho-trunc⇒¬ho (∧→ s) ↓ ¬ho (∧→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce∧→↓
-- -- rl&¬ho-trunc⇒¬ho (∧→ s) (ind ←∧) ¬ho (∧→ lind) () tc
-- -- rl&¬ho-trunc⇒¬ho (∧→ s) (∧→ ind) ¬ho (∧→ lind) (≤ᵢ∧→ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∧→∧→ z)) lind rl tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) ↓ ¬ho (∧→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce←∧→↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) (ind ←∧) ¬ho (∧→ lind) () tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∧→ s₁) (∧→ ind) ¬ho (∧→ lind) (≤ᵢ∧→ rl) tc = rl&¬ho-trunc⇒¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∧→∧→ z)) lind rl tc
-- -- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (lind ←∨) rl tc = ⊥-elim (¬ho hitsAtLeastOnce↓)
-- -- rl&¬ho-trunc⇒¬ho (s ←∨) ↓ ¬ho (lind ←∨) rl tc = λ _ → ¬ho hitsAtLeastOnce←∨↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∨) (ind ←∨) ¬ho (lind ←∨) (≤ᵢ←∨ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∨←∨ z)) lind rl tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∨) (∨→ ind) ¬ho (lind ←∨) () tc
-- -- rl&¬ho-trunc⇒¬ho (∨→ s) ind ¬ho (lind ←∨) rl ()
-- -- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) ↓ ¬ho (lind ←∨) rl tc = λ _ → ¬ho hitsAtLeastOnce←∨→↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) (ind ←∨) ¬ho (lind ←∨) (≤ᵢ←∨ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∨→←∨ z)) lind rl tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) (∨→ ind) ¬ho (lind ←∨) () tc
-- -- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (∨→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∨) ind ¬ho (∨→ lind) rl ()
-- -- rl&¬ho-trunc⇒¬ho (∨→ s) ↓ ¬ho (∨→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce∨→↓
-- -- rl&¬ho-trunc⇒¬ho (∨→ s) (ind ←∨) ¬ho (∨→ lind) () tc
-- -- rl&¬ho-trunc⇒¬ho (∨→ s) (∨→ ind) ¬ho (∨→ lind) (≤ᵢ∨→ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∨→∨→ z)) lind rl tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) ↓ ¬ho (∨→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce←∨→↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) (ind ←∨) ¬ho (∨→ lind) () tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∨→ s₁) (∨→ ind) ¬ho (∨→ lind) (≤ᵢ∨→ rl) tc = rl&¬ho-trunc⇒¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∨→∨→ z)) lind rl tc
-- -- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (lind ←∂) rl tc = ⊥-elim (¬ho hitsAtLeastOnce↓)
-- -- rl&¬ho-trunc⇒¬ho (s ←∂) ↓ ¬ho (lind ←∂) rl tc = λ _ → ¬ho hitsAtLeastOnce←∂↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∂) (ind ←∂) ¬ho (lind ←∂) (≤ᵢ←∂ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∂←∂ z)) lind rl tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∂) (∂→ ind) ¬ho (lind ←∂) () tc
-- -- rl&¬ho-trunc⇒¬ho (∂→ s) ind ¬ho (lind ←∂) rl ()
-- -- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) ↓ ¬ho (lind ←∂) rl tc = λ _ → ¬ho hitsAtLeastOnce←∂→↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) (ind ←∂) ¬ho (lind ←∂) (≤ᵢ←∂ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce←∂→←∂ z)) lind rl tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) (∂→ ind) ¬ho (lind ←∂) () tc
-- -- rl&¬ho-trunc⇒¬ho ↓ ind ¬ho (∂→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∂) ind ¬ho (∂→ lind) rl ()
-- -- rl&¬ho-trunc⇒¬ho (∂→ s) ↓ ¬ho (∂→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce∂→↓
-- -- rl&¬ho-trunc⇒¬ho (∂→ s) (ind ←∂) ¬ho (∂→ lind) () tc
-- -- rl&¬ho-trunc⇒¬ho (∂→ s) (∂→ ind) ¬ho (∂→ lind) (≤ᵢ∂→ rl) tc = rl&¬ho-trunc⇒¬ho s ind (λ z → ¬ho (hitsAtLeastOnce∂→∂→ z)) lind rl tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) ↓ ¬ho (∂→ lind) rl tc = λ _ → ¬ho hitsAtLeastOnce←∂→↓
-- -- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) (ind ←∂) ¬ho (∂→ lind) () tc
-- -- rl&¬ho-trunc⇒¬ho (s ←∂→ s₁) (∂→ ind) ¬ho (∂→ lind) (≤ᵢ∂→ rl) tc = rl&¬ho-trunc⇒¬ho s₁ ind (λ z → ¬ho (hitsAtLeastOnce←∂→∂→ z)) lind rl tc





-- -- ¬ho⇒+ind¬ho : ∀{i u pll ll ell rll} → (s : SetLL ell) → (t : IndexLL {i} {u} rll ell)
-- --       → (lind : IndexLL pll ll)
-- --       → ¬ (hitsAtLeastOnce s t)
-- --       → ¬ (hitsAtLeastOnce (extendg lind s) (subst (λ x → IndexLL x (replLL ll lind ell)) (replLL-↓ {ell = ell} lind) (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) +ᵢ t))
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t ↓ ¬ho = ¬ho
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (lind ←∧) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (lind ←∧) ¬ho (hitsAtLeastOnce←∧←∧ x) | g | refl | e | q = q x
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (∧→ lind) ¬ho  x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (∧→ lind) ¬ho (hitsAtLeastOnce∧→∧→ x) | g | refl | e | q = q x
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (lind ←∨) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (lind ←∨) ¬ho (hitsAtLeastOnce←∨←∨ x) | g | refl | e | q = q x
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (∨→ lind) ¬ho  x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (∨→ lind) ¬ho (hitsAtLeastOnce∨→∨→ x) | g | refl | e | q = q x
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (lind ←∂) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (lind ←∂) ¬ho (hitsAtLeastOnce←∂←∂ x) | g | refl | e | q = q x
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = ell} s t (∂→ lind) ¬ho  x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho s t lind ¬ho
-- -- ¬ho⇒+ind¬ho {pll = pll} {ell = .g} s t (∂→ lind) ¬ho (hitsAtLeastOnce∂→∂→ x) | g | refl | e | q = q x



-- -- a≤b&¬ho-repl⇒¬ho : ∀{i u pll ll ell rll} → ∀ (s : SetLL ll) → (y : SetLL ell) → (t : IndexLL {i} {u} rll ell)
-- --       → (lind : IndexLL pll ll)
-- --       → ¬ (hitsAtLeastOnce y t)
-- --       → ¬ (hitsAtLeastOnce (replacePartOf s to y at lind) (subst (λ x → IndexLL x (replLL ll lind ell)) (replLL-↓ {ell = ell} lind) (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) +ᵢ t))
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} s y t ↓ ¬ho = ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (lind ←∧) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (lind ←∧) ¬ho (hitsAtLeastOnce←∧→←∧ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∧) y t (lind ←∧) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∧) y t (lind ←∧) ¬ho (hitsAtLeastOnce←∧←∧ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∧→ s) y t (lind ←∧) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∧→ s) y t (lind ←∧) ¬ho (hitsAtLeastOnce←∧→←∧ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∧→ s₁) y t (lind ←∧) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∧→ s₁) y t (lind ←∧) ¬ho (hitsAtLeastOnce←∧→←∧ x) | g | refl | e | q = q x

-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (∧→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (∧→ lind) ¬ho (hitsAtLeastOnce←∧→∧→ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∧) y t (∧→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∧) y t (∧→ lind) ¬ho (hitsAtLeastOnce←∧→∧→ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∧→ s) y t (∧→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∧→ s) y t (∧→ lind) ¬ho (hitsAtLeastOnce∧→∧→ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∧→ s₁) y t (∧→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s₁ y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∧→ s₁) y t (∧→ lind) ¬ho (hitsAtLeastOnce←∧→∧→ x) | g | refl | e | q = q x

-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (lind ←∨) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (lind ←∨) ¬ho (hitsAtLeastOnce←∨→←∨ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∨) y t (lind ←∨) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∨) y t (lind ←∨) ¬ho (hitsAtLeastOnce←∨←∨ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∨→ s) y t (lind ←∨) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∨→ s) y t (lind ←∨) ¬ho (hitsAtLeastOnce←∨→←∨ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∨→ s₁) y t (lind ←∨) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∨→ s₁) y t (lind ←∨) ¬ho (hitsAtLeastOnce←∨→←∨ x) | g | refl | e | q = q x

-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (∨→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (∨→ lind) ¬ho (hitsAtLeastOnce←∨→∨→ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∨) y t (∨→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∨) y t (∨→ lind) ¬ho (hitsAtLeastOnce←∨→∨→ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∨→ s) y t (∨→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∨→ s) y t (∨→ lind) ¬ho (hitsAtLeastOnce∨→∨→ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∨→ s₁) y t (∨→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s₁ y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∨→ s₁) y t (∨→ lind) ¬ho (hitsAtLeastOnce←∨→∨→ x) | g | refl | e | q = q x

-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (lind ←∂) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (lind ←∂) ¬ho (hitsAtLeastOnce←∂→←∂ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∂) y t (lind ←∂) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∂) y t (lind ←∂) ¬ho (hitsAtLeastOnce←∂←∂ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∂→ s) y t (lind ←∂) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∂→ s) y t (lind ←∂) ¬ho (hitsAtLeastOnce←∂→←∂ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∂→ s₁) y t (lind ←∂) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∂→ s₁) y t (lind ←∂) ¬ho (hitsAtLeastOnce←∂→←∂ x) | g | refl | e | q = q x

-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} ↓ y t (∂→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho ↓ y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} ↓ y t (∂→ lind) ¬ho (hitsAtLeastOnce←∂→∂→ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∂) y t (∂→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | ¬ho⇒+ind¬ho y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∂) y t (∂→ lind) ¬ho (hitsAtLeastOnce←∂→∂→ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (∂→ s) y t (∂→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (∂→ s) y t (∂→ lind) ¬ho (hitsAtLeastOnce∂→∂→ x) | g | refl | e | q = q x
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = ell} (s ←∂→ s₁) y t (∂→ lind) ¬ho x with replLL pll ((lind -ᵢ lind) (≤ᵢ-reflexive lind)) ell | replLL-↓ {ell = ell} lind | (a≤ᵢb-morph lind lind ell (≤ᵢ-reflexive lind)) | a≤b&¬ho-repl⇒¬ho s₁ y t lind ¬ho
-- -- a≤b&¬ho-repl⇒¬ho {pll = pll} {ell = .g} (s ←∂→ s₁) y t (∂→ lind) ¬ho (hitsAtLeastOnce←∂→∂→ x) | g | refl | e | q = q x






  
  
-- -- module _ where

-- --   open import IndexLLProp
  
-- --   ho-trans : ∀{i u pll rll ll} → ∀ s → (ind1 : IndexLL {i} {u} pll ll) → (ind2 : IndexLL rll pll)
-- --          → (ho1 : hitsAtLeastOnce s ind1) → hitsAtLeastOnce (truncHOSetLL s ind1 ho1) ind2
-- --          → hitsAtLeastOnce s (ind1 +ᵢ ind2)
-- --   ho-trans ↓ ind ind2 ho1 ho2 = hitsAtLeastOnce↓
-- --   ho-trans (s ←∧) ↓ ind2 ho1 ho2 = ho2
-- --   ho-trans (s ←∧) (ind ←∧) ind2 (hitsAtLeastOnce←∧←∧ ho1) ho2 = hitsAtLeastOnce←∧←∧ r where
-- --     r = ho-trans s ind ind2 ho1 ho2
-- --   ho-trans (s ←∧) (∧→ ind) ind2 () ho2
-- --   ho-trans (∧→ s) ↓ ind2 ho1 ho2 = ho2
-- --   ho-trans (∧→ s) (ind ←∧) ind2 () ho2
-- --   ho-trans (∧→ s) (∧→ ind) ind2 (hitsAtLeastOnce∧→∧→ ho1) ho2 = hitsAtLeastOnce∧→∧→ r where
-- --     r = ho-trans s ind ind2 ho1 ho2
-- --   ho-trans (s ←∧→ s₁) ↓ ind2 ho1 ho2 = ho2
-- --   ho-trans (s ←∧→ s₁) (ind ←∧) ind2 (hitsAtLeastOnce←∧→←∧ ho1) ho2 = hitsAtLeastOnce←∧→←∧ r where
-- --     r = ho-trans s ind ind2 ho1 ho2
-- --   ho-trans (s ←∧→ s₁) (∧→ ind) ind2 (hitsAtLeastOnce←∧→∧→ ho1) ho2 = hitsAtLeastOnce←∧→∧→ r where
-- --     r = ho-trans s₁ ind ind2 ho1 ho2
-- --   ho-trans (s ←∨) ↓ ind2 ho1 ho2 = ho2
-- --   ho-trans (s ←∨) (ind ←∨) ind2 (hitsAtLeastOnce←∨←∨ ho1) ho2 = hitsAtLeastOnce←∨←∨ r where
-- --     r = ho-trans s ind ind2 ho1 ho2
-- --   ho-trans (s ←∨) (∨→ ind) ind2 () ho2
-- --   ho-trans (∨→ s) ↓ ind2 ho1 ho2 = ho2
-- --   ho-trans (∨→ s) (ind ←∨) ind2 () ho2
-- --   ho-trans (∨→ s) (∨→ ind) ind2 (hitsAtLeastOnce∨→∨→ ho1) ho2 = hitsAtLeastOnce∨→∨→ r where
-- --     r = ho-trans s ind ind2 ho1 ho2
-- --   ho-trans (s ←∨→ s₁) ↓ ind2 ho1 ho2 = ho2
-- --   ho-trans (s ←∨→ s₁) (ind ←∨) ind2 (hitsAtLeastOnce←∨→←∨ ho1) ho2 = hitsAtLeastOnce←∨→←∨ r where
-- --     r = ho-trans s ind ind2 ho1 ho2
-- --   ho-trans (s ←∨→ s₁) (∨→ ind) ind2 (hitsAtLeastOnce←∨→∨→ ho1) ho2 = hitsAtLeastOnce←∨→∨→ r where
-- --     r = ho-trans s₁ ind ind2 ho1 ho2
-- --   ho-trans (s ←∂) ↓ ind2 ho1 ho2 = ho2
-- --   ho-trans (s ←∂) (ind ←∂) ind2 (hitsAtLeastOnce←∂←∂ ho1) ho2 = hitsAtLeastOnce←∂←∂ r where
-- --     r = ho-trans s ind ind2 ho1 ho2
-- --   ho-trans (s ←∂) (∂→ ind) ind2 () ho2
-- --   ho-trans (∂→ s) ↓ ind2 ho1 ho2 = ho2
-- --   ho-trans (∂→ s) (ind ←∂) ind2 () ho2
-- --   ho-trans (∂→ s) (∂→ ind) ind2 (hitsAtLeastOnce∂→∂→ ho1) ho2 = hitsAtLeastOnce∂→∂→ r where
-- --     r = ho-trans s ind ind2 ho1 ho2
-- --   ho-trans (s ←∂→ s₁) ↓ ind2 ho1 ho2 = ho2
-- --   ho-trans (s ←∂→ s₁) (ind ←∂) ind2 (hitsAtLeastOnce←∂→←∂ ho1) ho2 = hitsAtLeastOnce←∂→←∂ r where
-- --     r = ho-trans s ind ind2 ho1 ho2
-- --   ho-trans (s ←∂→ s₁) (∂→ ind) ind2 (hitsAtLeastOnce←∂→∂→ ho1) ho2 = hitsAtLeastOnce←∂→∂→ r where
-- --     r = ho-trans s₁ ind ind2 ho1 ho2


-- --   oi-trans : ∀{i u pll rll ll} → ∀ s → (ind1 : IndexLL {i} {u} pll ll) → (ind2 : IndexLL rll pll)
-- --          → (oi1 : onlyInside s ind1) → onlyInside (truncHOSetLL s ind1 (oi⇒ho s ind1 oi1)) ind2
-- --          → onlyInside s (ind1 +ᵢ ind2)
-- --   oi-trans ↓ ↓ ind2 oi1 oi2 = oi2
-- --   oi-trans ↓ (x ←∧) ind2 () oi2
-- --   oi-trans ↓ (∧→ x) ind2 () oi2
-- --   oi-trans ↓ (x ←∨) ind2 () oi2
-- --   oi-trans ↓ (∨→ x) ind2 () oi2
-- --   oi-trans ↓ (x ←∂) ind2 () oi2
-- --   oi-trans ↓ (∂→ x) ind2 () oi2
-- --   oi-trans (s ←∧) ↓ ind2 oi1 oi2 = oi2
-- --   oi-trans (s ←∧) (ind1 ←∧) ind2 (onlyInsideC←∧←∧ oi1) oi2 = onlyInsideC←∧←∧ r where
-- --     r = oi-trans s ind1 ind2 oi1 oi2
-- --   oi-trans (s ←∧) (∧→ ind1) ind2 () oi2
-- --   oi-trans (∧→ s) ↓ ind2 oi1 oi2 = oi2
-- --   oi-trans (∧→ s) (ind1 ←∧) ind2 () oi2
-- --   oi-trans (∧→ s) (∧→ ind1) ind2 (onlyInsideC∧→∧→ oi1) oi2 = onlyInsideC∧→∧→ r where
-- --     r = oi-trans s ind1 ind2 oi1 oi2
-- --   oi-trans (s ←∧→ s₁) ↓ ind2 oi1 oi2 = oi2
-- --   oi-trans (s ←∧→ s₁) (ind1 ←∧) ind2 () oi2
-- --   oi-trans (s ←∧→ s₁) (∧→ ind1) ind2 () oi2
-- --   oi-trans (s ←∨) ↓ ind2 oi1 oi2 = oi2
-- --   oi-trans (s ←∨) (ind1 ←∨) ind2 (onlyInsideC←∨←∨ oi1) oi2 = onlyInsideC←∨←∨ r where
-- --     r = oi-trans s ind1 ind2 oi1 oi2
-- --   oi-trans (s ←∨) (∨→ ind1) ind2 () oi2
-- --   oi-trans (∨→ s) ↓ ind2 oi1 oi2 = oi2
-- --   oi-trans (∨→ s) (ind1 ←∨) ind2 () oi2
-- --   oi-trans (∨→ s) (∨→ ind1) ind2 (onlyInsideC∨→∨→ oi1) oi2 = onlyInsideC∨→∨→ r where
-- --     r = oi-trans s ind1 ind2 oi1 oi2
-- --   oi-trans (s ←∨→ s₁) ↓ ind2 oi1 oi2 = oi2
-- --   oi-trans (s ←∨→ s₁) (ind1 ←∨) ind2 () oi2
-- --   oi-trans (s ←∨→ s₁) (∨→ ind1) ind2 () oi2
-- --   oi-trans (s ←∂) ↓ ind2 oi1 oi2 = oi2
-- --   oi-trans (s ←∂) (ind1 ←∂) ind2 (onlyInsideC←∂←∂ oi1) oi2 = onlyInsideC←∂←∂ r where
-- --     r = oi-trans s ind1 ind2 oi1 oi2
-- --   oi-trans (s ←∂) (∂→ ind1) ind2 () oi2
-- --   oi-trans (∂→ s) ↓ ind2 oi1 oi2 = oi2
-- --   oi-trans (∂→ s) (ind1 ←∂) ind2 () oi2
-- --   oi-trans (∂→ s) (∂→ ind1) ind2 (onlyInsideC∂→∂→ oi1) oi2 = onlyInsideC∂→∂→ r where
-- --     r = oi-trans s ind1 ind2 oi1 oi2
-- --   oi-trans (s ←∂→ s₁) ↓ ind2 oi1 oi2 = oi2
-- --   oi-trans (s ←∂→ s₁) (ind1 ←∂) ind2 () oi2
-- --   oi-trans (s ←∂→ s₁) (∂→ ind1) ind2 () oi2



-- -- TODO contruct s ≡ ↓ is not needed here.
-- --   ¬contr≡↓⇒¬contrdel≡↓ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → (ind : IndexLL rll ll) → ∀{x} → del s ind fll ≡ ¬∅ x → ¬ (contruct x ≡ ↓)
-- --   ¬contr≡↓⇒¬contrdel≡↓ s eq ↓ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∧) deq = ⊥-elim (eq refl)
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) deq with del s ind fll 
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) () | ∅
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧) eq (ind ←∧) refl | ¬∅ di = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ (∧→ s) eq (ind ←∧) refl = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) deq with del s ind fll | inspect (λ x → del s x fll) ind
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ∅ | [ eq1 ] = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
-- --   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∧ rs} {fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
-- --     hf : ¬ (contruct s₁ ≡ ↓)
-- --     hf x with contruct s₁
-- --     hf refl | .↓ = ⊥-elim (eq refl)

-- --     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∧→ t)) ≡ ↓)
-- --     hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
-- --     hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
-- --     hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
-- --     hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
-- --     hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
-- --     hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
-- --     hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
-- --     hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∧ rs} {fll = fll} (s ←∧→ s₁) eq (ind ←∧) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
-- --     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
-- --     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∧→ s₁)) ≡ ↓)
-- --     hf t eq x with contruct t | isEq (contruct t) ↓
-- --     hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
-- --     hf t eq₁ x | ↓ | no ¬p = eq₁ refl
-- --     hf t eq₁ () | g ←∧ | no ¬p
-- --     hf t eq₁ () | ∧→ g | no ¬p
-- --     hf t eq₁ () | g ←∧→ g₁ | no ¬p 
-- --     hf t eq₁ () | g ←∨ | no ¬p 
-- --     hf t eq₁ () | ∨→ g | no ¬p 
-- --     hf t eq₁ () | g ←∨→ g₁ | no ¬p 
-- --     hf t eq₁ () | g ←∂ | no ¬p 
-- --     hf t eq₁ () | ∂→ g | no ¬p 
-- --     hf t eq₁ () | g ←∂→ g₁ | no ¬p 
-- --   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∧→ ind) deq = ⊥-elim (eq refl)
-- --   ¬contr≡↓⇒¬contrdel≡↓ (s ←∧) eq (∧→ ind) refl = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) deq with del s ind fll
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) () | ∅
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∧→ s) eq (∧→ ind) refl | ¬∅ x = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ∅ | r = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
-- --   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
-- --     hf : ¬ (contruct s ≡ ↓)
-- --     hf x with contruct s
-- --     hf refl | .↓ = ⊥-elim (eq refl)

-- --     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∧→ t)) ≡ ↓)
-- --     hf2 t e eq x with contruct e | isEq (contruct e) ↓
-- --     hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
-- --     hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
-- --     hf2 t e eq₂ () | ce ←∧ | no ¬p
-- --     hf2 t e eq₂ () | ∧→ ce | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∨ | no ¬p 
-- --     hf2 t e eq₂ () | ∨→ ce | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∂ | no ¬p 
-- --     hf2 t e eq₂ () | ∂→ ce | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∧→ s₁) eq (∧→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
-- --     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
-- --     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∧→ t)) ≡ ↓)
-- --     hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
-- --     hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
-- --     hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
-- --     hf t eq₁ () | ↓ | g ←∧ | no ¬p
-- --     hf t eq₁ () | ↓ | ∧→ g | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∨ | no ¬p 
-- --     hf t eq₁ () | ↓ | ∨→ g | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∂ | no ¬p 
-- --     hf t eq₁ () | ↓ | ∂→ g | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
-- --     hf t eq₁ () | r ←∧ | g | no ¬p 
-- --     hf t eq₁ () | ∧→ r | g | no ¬p 
-- --     hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
-- --     hf t eq₁ () | r ←∨ | g | no ¬p 
-- --     hf t eq₁ () | ∨→ r | g | no ¬p 
-- --     hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
-- --     hf t eq₁ () | r ←∂ | g | no ¬p 
-- --     hf t eq₁ () | ∂→ r | g | no ¬p 
-- --     hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 

-- --   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∨) deq = ⊥-elim (eq refl)
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) deq with del s ind fll 
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) () | ∅
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨) eq (ind ←∨) refl | ¬∅ di = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ (∨→ s) eq (ind ←∨) refl = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) deq with del s ind fll | inspect (λ x → del s x fll) ind
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ∅ | [ eq1 ] = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
-- --   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∨ rs} {fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
-- --     hf : ¬ (contruct s₁ ≡ ↓)
-- --     hf x with contruct s₁
-- --     hf refl | .↓ = ⊥-elim (eq refl)

-- --     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∨→ t)) ≡ ↓)
-- --     hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
-- --     hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
-- --     hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
-- --     hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
-- --     hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
-- --     hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
-- --     hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
-- --     hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∨ rs} {fll = fll} (s ←∨→ s₁) eq (ind ←∨) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
-- --     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
-- --     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∨→ s₁)) ≡ ↓)
-- --     hf t eq x with contruct t | isEq (contruct t) ↓
-- --     hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
-- --     hf t eq₁ x | ↓ | no ¬p = eq₁ refl
-- --     hf t eq₁ () | g ←∧ | no ¬p
-- --     hf t eq₁ () | ∧→ g | no ¬p
-- --     hf t eq₁ () | g ←∧→ g₁ | no ¬p 
-- --     hf t eq₁ () | g ←∨ | no ¬p 
-- --     hf t eq₁ () | ∨→ g | no ¬p 
-- --     hf t eq₁ () | g ←∨→ g₁ | no ¬p 
-- --     hf t eq₁ () | g ←∂ | no ¬p 
-- --     hf t eq₁ () | ∂→ g | no ¬p 
-- --     hf t eq₁ () | g ←∂→ g₁ | no ¬p 
-- --   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∨→ ind) deq = ⊥-elim (eq refl)
-- --   ¬contr≡↓⇒¬contrdel≡↓ (s ←∨) eq (∨→ ind) refl = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) deq with del s ind fll
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) () | ∅
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∨→ s) eq (∨→ ind) refl | ¬∅ x = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ∅ | r = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
-- --   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
-- --     hf : ¬ (contruct s ≡ ↓)
-- --     hf x with contruct s
-- --     hf refl | .↓ = ⊥-elim (eq refl)

-- --     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∨→ t)) ≡ ↓)
-- --     hf2 t e eq x with contruct e | isEq (contruct e) ↓
-- --     hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
-- --     hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
-- --     hf2 t e eq₂ () | ce ←∧ | no ¬p
-- --     hf2 t e eq₂ () | ∧→ ce | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∨ | no ¬p 
-- --     hf2 t e eq₂ () | ∨→ ce | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∂ | no ¬p 
-- --     hf2 t e eq₂ () | ∂→ ce | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∨→ s₁) eq (∨→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
-- --     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
-- --     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∨→ t)) ≡ ↓)
-- --     hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
-- --     hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
-- --     hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
-- --     hf t eq₁ () | ↓ | g ←∧ | no ¬p
-- --     hf t eq₁ () | ↓ | ∧→ g | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∨ | no ¬p 
-- --     hf t eq₁ () | ↓ | ∨→ g | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∂ | no ¬p 
-- --     hf t eq₁ () | ↓ | ∂→ g | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
-- --     hf t eq₁ () | r ←∧ | g | no ¬p 
-- --     hf t eq₁ () | ∧→ r | g | no ¬p 
-- --     hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
-- --     hf t eq₁ () | r ←∨ | g | no ¬p 
-- --     hf t eq₁ () | ∨→ r | g | no ¬p 
-- --     hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
-- --     hf t eq₁ () | r ←∂ | g | no ¬p 
-- --     hf t eq₁ () | ∂→ r | g | no ¬p 
-- --     hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 

-- --   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (ind ←∂) deq = ⊥-elim (eq refl)
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) deq with del s ind fll 
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) () | ∅
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂) eq (ind ←∂) refl | ¬∅ di = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ (∂→ s) eq (ind ←∂) refl = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) deq with del s ind fll | inspect (λ x → del s x fll) ind
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ∅ | [ eq1 ] = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] with isEq (contruct s) ↓
-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | yes p with contruct s
-- --   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {rll = _} {ls ∂ rs} {fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | yes refl | .↓ = hf2 s₁ di hf where
-- --     hf : ¬ (contruct s₁ ≡ ↓)
-- --     hf x with contruct s₁
-- --     hf refl | .↓ = ⊥-elim (eq refl)

-- --     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct t ≡ ↓) → ¬ ((contruct (e ←∂→ t)) ≡ ↓)
-- --     hf2 t e eq x with contruct e | contruct t | isEq (contruct t) ↓
-- --     hf2 t e eq₁ x | ce | g | yes p = ⊥-elim (eq₁ p)
-- --     hf2 t e eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
-- --     hf2 t e eq₁ () | ↓ | g ←∧ | no ¬p
-- --     hf2 t e eq₁ () | ↓ | ∧→ g | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∨ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | ∨→ g | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∂ | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | ∂→ g | no ¬p 
-- --     hf2 t e eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∧ | g | no ¬p 
-- --     hf2 t e eq₁ () | ∧→ ce | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∧→ ce₁ | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∨ | g | no ¬p 
-- --     hf2 t e eq₁ () | ∨→ ce | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∨→ ce₁ | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∂ | g | no ¬p 
-- --     hf2 t e eq₁ () | ∂→ ce | g | no ¬p 
-- --     hf2 t e eq₁ () | ce ←∂→ ce₁ | g | no ¬p 

-- --   ¬contr≡↓⇒¬contrdel≡↓ {ll = ls ∂ rs} {fll = fll} (s ←∂→ s₁) eq (ind ←∂) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
-- --     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s ¬p ind eq1
-- --     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (t ←∂→ s₁)) ≡ ↓)
-- --     hf t eq x with contruct t | isEq (contruct t) ↓
-- --     hf t eq₁ x | g | yes p = ⊥-elim (eq₁ p)
-- --     hf t eq₁ x | ↓ | no ¬p = eq₁ refl
-- --     hf t eq₁ () | g ←∧ | no ¬p
-- --     hf t eq₁ () | ∧→ g | no ¬p
-- --     hf t eq₁ () | g ←∧→ g₁ | no ¬p 
-- --     hf t eq₁ () | g ←∨ | no ¬p 
-- --     hf t eq₁ () | ∨→ g | no ¬p 
-- --     hf t eq₁ () | g ←∨→ g₁ | no ¬p 
-- --     hf t eq₁ () | g ←∂ | no ¬p 
-- --     hf t eq₁ () | ∂→ g | no ¬p 
-- --     hf t eq₁ () | g ←∂→ g₁ | no ¬p 
-- --   ¬contr≡↓⇒¬contrdel≡↓ ↓ eq (∂→ ind) deq = ⊥-elim (eq refl)
-- --   ¬contr≡↓⇒¬contrdel≡↓ (s ←∂) eq (∂→ ind) refl = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) deq with del s ind fll
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) () | ∅
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (∂→ s) eq (∂→ ind) refl | ¬∅ x = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq with del s₁ ind fll | inspect (λ x → del s₁ x fll) ind
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ∅ | r = λ ()
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq | ¬∅ di | [ eq₁ ] with isEq (contruct s₁) ↓
-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) deq | ¬∅ di | [ eq₁ ] | yes p with contruct s₁
-- --   ¬contr≡↓⇒¬contrdel≡↓ {i} {u} {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ¬∅ di | [ eq₁ ] | yes refl | .↓ = hf2 di s hf where
-- --     hf : ¬ (contruct s ≡ ↓)
-- --     hf x with contruct s
-- --     hf refl | .↓ = ⊥-elim (eq refl)

-- --     hf2 : ∀{ls rs} → (t : SetLL {i} {u} rs) → (e : SetLL ls) → ¬ (contruct e ≡ ↓) → ¬ ((contruct (e ←∂→ t)) ≡ ↓)
-- --     hf2 t e eq x with contruct e | isEq (contruct e) ↓
-- --     hf2 t e eq₁ x | ce | yes p = ⊥-elim (eq₁ p)
-- --     hf2 t e eq₂ x | ↓ | no ¬p = eq₂ refl
-- --     hf2 t e eq₂ () | ce ←∧ | no ¬p
-- --     hf2 t e eq₂ () | ∧→ ce | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∧→ ce₁ | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∨ | no ¬p 
-- --     hf2 t e eq₂ () | ∨→ ce | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∨→ ce₁ | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∂ | no ¬p 
-- --     hf2 t e eq₂ () | ∂→ ce | no ¬p 
-- --     hf2 t e eq₂ () | ce ←∂→ ce₁ | no ¬p 

-- --   ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} (s ←∂→ s₁) eq (∂→ ind) refl | ¬∅ di | [ eq1 ] | no ¬p = hf di is where
-- --     is = ¬contr≡↓⇒¬contrdel≡↓ {fll = fll} s₁ ¬p ind eq1
-- --     hf : ∀{ll} → ∀ t → ¬ (contruct {ll = ll} t ≡ ↓) → ¬ ((contruct (s ←∂→ t)) ≡ ↓)
-- --     hf t eq x with contruct s | contruct t | isEq (contruct t) ↓
-- --     hf t eq₁ x | r | g | yes p = ⊥-elim (eq₁ p)
-- --     hf t eq₁ x | ↓ | ↓ | no ¬p = eq₁ refl
-- --     hf t eq₁ () | ↓ | g ←∧ | no ¬p
-- --     hf t eq₁ () | ↓ | ∧→ g | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∧→ g₁ | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∨ | no ¬p 
-- --     hf t eq₁ () | ↓ | ∨→ g | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∨→ g₁ | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∂ | no ¬p 
-- --     hf t eq₁ () | ↓ | ∂→ g | no ¬p 
-- --     hf t eq₁ () | ↓ | g ←∂→ g₁ | no ¬p 
-- --     hf t eq₁ () | r ←∧ | g | no ¬p 
-- --     hf t eq₁ () | ∧→ r | g | no ¬p 
-- --     hf t eq₁ () | r ←∧→ r₁ | g | no ¬p 
-- --     hf t eq₁ () | r ←∨ | g | no ¬p 
-- --     hf t eq₁ () | ∨→ r | g | no ¬p 
-- --     hf t eq₁ () | r ←∨→ r₁ | g | no ¬p 
-- --     hf t eq₁ () | r ←∂ | g | no ¬p 
-- --     hf t eq₁ () | ∂→ r | g | no ¬p 
-- --     hf t eq₁ () | r ←∂→ r₁ | g | no ¬p 


-- -- module _ where

-- --   open Data.Product
  
-- --   ¬contr≡↓&trunc≡∅⇒¬contrdel≡↓ : ∀{i u rll ll fll} → (s : SetLL {i} {u} ll) → ¬ (contruct s ≡ ↓) → (ind : IndexLL rll ll) → (truncSetLL s ind ≡ ∅)
-- --                                  → Σ (SetLL (replLL ll ind fll)) (λ x → (del s ind fll ≡ ¬∅ x) × (¬ (contruct x ≡ ↓)))
-- --   ¬contr≡↓&trunc≡∅⇒¬contrdel≡↓ {fll = fll} s ceq ind treq with del s ind fll | inspect (λ x → del s x fll) ind
-- --   ... | ∅ | [ eq ] = ⊥-elim (d eq) where
-- --     d = trunc≡∅⇒¬mrpls≡∅ {fll = fll} s ind treq
-- --   ... | ¬∅ x | [ eq ] = (x , refl , c) where
-- --     c = ¬contr≡↓⇒¬contrdel≡↓ s ceq ind eq



