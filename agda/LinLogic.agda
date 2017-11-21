
module LinLogic where

open import Common
open import Data.Unit
import Relation.Binary.PropositionalEquality


data LLCT : Set where
      -- Both sub-trees need to be sent or received.
      -- Corresponds to the tensor connective.
  ∧ : LLCT
      -- Only one sub-tree can be sent or received
      -- Corresponds to the sum connective.
  ∨ : LLCT

module _ where

  open import Data.Vec 

  -- TODO IMPORTANT: Maybe we need to add a 4th connector
  -- If any of the inputs is received, "proceed" with the next com.
  -- This is different from ∨ or ∂ because more than one inputs may be received.
  -- It is closer to the ∧ because all inputs might potentially arive.
  -- This connector can potentially be emulated by using an ∧ that has a timeout of zero after
  -- it receives the first input. (The remaining inputs will be set to the empty constructor.)

  mutual
    -- Linear Logic Connectives : Used to describe the input
    -- and output of an agent.
    data LinLogic (i : Size) {u} : Set (lsuc u) where
      -- When nothing is sent or received
      ∅    :                                            LinLogic i
      -- Contains a function that computes a dependent type.
      τ    : ∀{n} {dt : Vec (Set u) n} → genT dt      → LinLogic i
      -- This is a constructor that indicates that this part of LinLogic is abstract.
      -- It can be considered a variable.
      abs    :                                          LinLogic i
      -- The input or output of a linear function.
      -- The function can be recursive or corecursive.
      call : ∞LinLogic i {u}                          → LinLogic i
      _<_>_ : LinLogic i {u} → LLCT → LinLogic i {u}  → LinLogic i

    record ∞LinLogic (i : Size) {u} : Set (lsuc u) where
      coinductive
      field
        step : {j : Size< i} → LinLogic j {u = u}


  open ∞LinLogic public


-- According to https://ncatlab.org/nlab/show/linear+logic , we have associativity and distributive rules.
-- Since we do not have the 'par' connective, I haven't added its distributive rule.


-- IMPORTANT : The transformations here are contrained by the information that an agent has to where to send
-- his output. His version of LinFun should provide him enough information to do so.

-- Transformations so as to construct
-- the correct sub-tree that is to be the input of a linear function.
data LLTr {i : Size} {u} (rll : LinLogic i {u}) : LinLogic i {u} → Set (lsuc u) where
  -- Identity
  I     : LLTr rll rll
  -- Commutative transformations for ∂, ∧ and ∨.
  cₜᵣ    : ∀{r l il} → LLTr rll (r < il > l) → LLTr rll (l < il > r)
  -- Distributive transformations.
  
-- IMPORTANT : The agent to whom to send r depends on the knowledge of ∨'s answer, this is impossible.
-- If all l₁ l₂ and r were sent to the same agent , then it would be possible, but the same function is
-- done with a com that simply performs the transformation and send the output to oneself.
-- Based on ncatlab, this should have been possible, but is not because our system is multi-agent.
--  ∧∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ < ∧ > r) < ∨ > (l₂ < ∧ > r)) → LLTr rll ((l₁ < ∨ > l₂) < ∧ > r)

-- IMPORTANT : Possible only one possible LinDepT r can exist because the previous is not possible, thus the answer of ∨
-- is derived from a single com and only one brunch is executed.
--  ¬∧∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ < ∨ > l₂) < ∧ > r) → LLTr rll ((l₁ < ∧ > r) < ∨ > (l₂ < ∧ > r))


-- IMPORTANT : POSSIBLE to duplicate resources but unnecessary because It is COM that should be doing that. 
--  ∧∧d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ < ∧ > r) < ∧ > (l₂ < ∧ > r)) → LLTr rll ((l₁ < ∧ > l₂) < ∧ > r)

-- IMPORTANT : Not possible to halve resources. Both agents will send the same type of data because they have
-- no knowledge of what the other is doing.
--  ¬∧∧d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ < ∧ > l₂) < ∧ > r) → LLTr rll ((l₁ < ∧ > r) < ∧ > (l₂ < ∧ > r))

-- IMPORTANT : This is not possible because the choice of the left ∨ will not happen if r happens.
-- Thus the choice where to send r is undetermined.
--   ∨∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∨ r) ∨ (l₂ ∨ r)) → LLTr rll ((l₁ ∨ l₂) ∨ r)

  -- IMPORTANT : The creator of output r can derive the choices for both ∨.
  -- Thus it must send the decision to the rest of the agents, so that they do not wait.
--  ¬∨∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ < ∨ > l₂) < ∨ > r) → LLTr rll ((l₁ < ∨ > r) < ∨ > (l₂ < ∨ > r))

-- Here , we need to guarantee that ∅ is not the input of any other com. ∅ should be at the edges ,
-- not in the middle.
--  ∨∧d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ < ∨ > r) < ∧ > (l₂ < ∨ > ∅)) → LLTr rll ((l₁ < ∧ > l₂) < ∨ > r)
  
-- IMPORTANT : The two ∨ are different from one another, thus they can have different answers.
--  ¬∨∧d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∧ l₂) ∨ r) → LLTr rll ((l₁ ∨ r) ∧ (l₂ ∨ r))

-- Associative transformations
  aₜᵣ   : ∀{l₁ l₂ r il} → LLTr rll (l₁ < il > (l₂ < il > r)) → LLTr rll ((l₁ < il > l₂ ) < il > r )
--  ¬dₜᵣ is derivable from dₜᵣ and cₜᵣ
--  ¬aₜᵣ   : ∀{l₁ l₂ r il} → LLTr rll ((l₁ < il > l₂ ) < il > r ) → LLTr rll (l₁ < il > (l₂ < il > r))

-- TODO Associative transformations where il is different per tr.
-- TODO

--
--revTr : ∀{i u rll ll} → LLTr {i} {u} rll ll → LLTr ll rll
--revTr {i} {u} {orll} {oll} ltr = revTr` ltr I where
--  revTr` : ∀{x} → LLTr {i} {u} orll x → LLTr oll x → LLTr oll orll
--  revTr` I nltr = nltr
--  revTr` (cₜᵣ ltr) nltr = revTr` ltr (cₜᵣ nltr)
--  revTr` (aₜᵣ ltr) nltr = revTr` ltr (¬aₜᵣ nltr)
--  revTr` (¬aₜᵣ ltr) nltr = revTr` ltr (aₜᵣ nltr)


data IndexLLCT : Set where
  ic← : IndexLLCT 
  ic→ : IndexLLCT

~ict : IndexLLCT → IndexLLCT
~ict ic← = ic→
~ict ic→ = ic←

module _ where

  open Relation.Binary.PropositionalEquality

isEqICT : (a b : IndexLLCT) → Dec (a ≡ b)
isEqICT ic← ic← = yes refl
isEqICT ic← ic→ = no (λ ())
isEqICT ic→ ic← = no (λ ())
isEqICT ic→ ic→ = yes refl



expLLT : ∀{i u} → {il : LLCT} → (ll : LinLogic i {u}) → IndexLLCT → (rl : LinLogic i {u}) → LinLogic i {u}
expLLT {il = il} ll ic← rl = ll < il > rl
expLLT {il = il} ll ic→ rl = rl < il > ll


  
-- expLLT⇒eq : ∀{i u lla llb tlla tllb icta ictb}
--             → ∀ il
--             → icta ≡ ictb
--             → {{eqa : il ≡ expLLT {i} {u} lla icta tlla}}
--             → {{eqb : il ≡ expLLT llb ictb tllb}}
--             → (lla ≡ llb) × (tlla ≡ tllb) × ((icta , lla , tlla , eqa) ≡ (ictb , llb , tllb , eqb))
-- expLLT⇒eq {icta = ic←∧} _ refl {{refl}} {{refl}} = refl , refl , refl
-- expLLT⇒eq {icta = ic∧→} _ refl {{refl}} {{refl}} = refl , refl , refl
-- expLLT⇒eq {icta = ic←∨} _ refl {{refl}} {{refl}} = refl , refl , refl
-- expLLT⇒eq {icta = ic∨→} _ refl {{refl}} {{refl}} = refl , refl , refl
-- expLLT⇒eq {icta = ic←∂} _ refl {{refl}} {{refl}} = refl , refl , refl
-- expLLT⇒eq {icta = ic∂→} _ refl {{refl}} {{refl}} = refl , refl , refl


-- instance
--   rexpLLT⇒IndOp : ∀{i u ict1 ict2 il x1 x2 y1 y2} → ¬ ict1 ≡ ict2
--         → il ≡ expLLT {i} {u} x1 ict1 x2
--         → il ≡ expLLT {i} {u} y1 ict2 y2
--         → IndOpLLCT ict1 ict2
--   rexpLLT⇒IndOp {ict1 = ic←∧} {ic←∧} ¬p _ _ = ⊥-elim (¬p refl)
--   rexpLLT⇒IndOp {ict1 = ic←∧} {ic∧→} ¬p _ _ = ∧op
--   rexpLLT⇒IndOp {ict1 = ic←∧} {ic←∨} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∧} {ic∨→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∧} {ic←∂} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∧} {ic∂→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∧→} {ic←∧} ¬p _ _ = ∧opi
--   rexpLLT⇒IndOp {ict1 = ic∧→} {ic∧→} ¬p _ _ = ⊥-elim (¬p refl)
--   rexpLLT⇒IndOp {ict1 = ic∧→} {ic←∨} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∧→} {ic∨→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∧→} {ic←∂} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∧→} {ic∂→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∨} {ic←∧} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∨} {ic∧→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∨} {ic←∨} ¬p _ _ = ⊥-elim (¬p refl)
--   rexpLLT⇒IndOp {ict1 = ic←∨} {ic∨→} ¬p _ _ = ∨op
--   rexpLLT⇒IndOp {ict1 = ic←∨} {ic←∂} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∨} {ic∂→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∨→} {ic←∧} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∨→} {ic∧→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∨→} {ic←∨} ¬p _ _ = ∨opi
--   rexpLLT⇒IndOp {ict1 = ic∨→} {ic∨→} ¬p _ _ = ⊥-elim (¬p refl)
--   rexpLLT⇒IndOp {ict1 = ic∨→} {ic←∂} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∨→} {ic∂→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∂} {ic←∧} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∂} {ic∧→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∂} {ic←∨} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∂} {ic∨→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic←∂} {ic←∂} ¬p _ _ = ⊥-elim (¬p refl)
--   rexpLLT⇒IndOp {ict1 = ic←∂} {ic∂→} ¬p _ _ = ∂op
--   rexpLLT⇒IndOp {ict1 = ic∂→} {ic←∧} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∂→} {ic∧→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∂→} {ic←∨} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∂→} {ic∨→} ¬p refl ()
--   rexpLLT⇒IndOp {ict1 = ic∂→} {ic←∂} ¬p _ _ = ∂opi
--   rexpLLT⇒IndOp {ict1 = ic∂→} {ic∂→} ¬p _ _ = ⊥-elim (¬p refl)
  
-- module _ where

--   expLLT⇒req-abs : ∀{i u ll1 ll2 tll1 tll2 ict1 ict2} → ∀ il → IndOpLLCT ict1 ict2 → {{eqa : il ≡ expLLT {i} {u} ll1 ict1 tll1}} → {{eqb : il ≡ expLLT ll2 ict2 tll2}} → (ll1 ≡ tll2) × (ll2 ≡ tll1)
--   expLLT⇒req-abs _ ∧op {{refl}} {{refl}} = refl , refl
--   expLLT⇒req-abs _ ∨op {{refl}} {{refl}} = refl , refl
--   expLLT⇒req-abs _ ∂op {{refl}} {{refl}} = refl , refl
--   expLLT⇒req-abs _ ∧opi {{refl}} {{refl}} = refl , refl
--   expLLT⇒req-abs _ ∨opi {{refl}} {{refl}} = refl , refl
--   expLLT⇒req-abs _ ∂opi {{refl}} {{refl}} = refl , refl

--   expLLT⇒req : ∀{i u ll1 ll2 tll1 tll2 ict1 ict2} → ∀ il → ¬ ict1 ≡ ict2 → {{eqa : il ≡ expLLT {i} {u} ll1 ict1 tll1}} → {{eqb : il ≡ expLLT ll2 ict2 tll2}} → (ll1 ≡ tll2) × (ll2 ≡ tll1)
--   expLLT⇒req il ¬p {{eqa = eqa}} {{eqb = eqb}} = expLLT⇒req-abs il (rexpLLT⇒IndOp ¬p eqa eqb)
  


-- indOp⇒rexpLLT : ∀{i u ll tll ict1 ict2}
--       → {{iop : IndOpLLCT ict1 ict2}}
--       → expLLT {i} {u} ll ict2 tll ≡ expLLT tll ict1 ll
-- indOp⇒rexpLLT {{iop = ∧op}}  = refl
-- indOp⇒rexpLLT {{iop = ∨op}}  = refl
-- indOp⇒rexpLLT {{iop = ∂op}}  = refl
-- indOp⇒rexpLLT {{iop = ∧opi}} = refl
-- indOp⇒rexpLLT {{iop = ∨opi}} = refl
-- indOp⇒rexpLLT {{iop = ∂opi}} = refl


-- data IndU {i u il} (icta ictb : IndexLLCT) {lla llb tlla tllb : LinLogic i {u}} (eqa : il ≡ expLLT lla icta tlla) (eqb : il ≡ expLLT llb ictb tllb) : Set (lsuc u) where
--   ictEq : (icteq : icta ≡ ictb) → (lleq : lla ≡ llb) → (tlleq : tlla ≡ tllb) → (eqeq : (icta , lla , tlla , eqa) ≡ (ictb , llb , tllb , eqb)) → IndU _ _ _ _
--   ict¬Eq : (¬icteq : ¬ icta ≡ ictb) → (reqa : lla ≡ tllb) → (reqb : llb ≡ tlla) → IndU _ _ _ _

-- module _ where

--   compIndU-abs : ∀{i u il} → {icta ictb : IndexLLCT} {lla llb tlla tllb : LinLogic i {u}} {{eqa : il ≡ expLLT lla icta tlla}} {{eqb : il ≡ expLLT llb ictb tllb}} → Dec (icta ≡ ictb) → IndU icta ictb eqa eqb
--   compIndU-abs {il = il} (yes p) = ictEq p (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) where
--     r = expLLT⇒eq il p
--   compIndU-abs {il = il} (no ¬p) = ict¬Eq ¬p (proj₁ r) (proj₂ r) where
--     r = expLLT⇒req il ¬p
  
--   compIndU : ∀{i u il} (icta ictb : IndexLLCT) {lla llb tlla tllb : LinLogic i {u}} (eqa : il ≡ expLLT lla icta tlla) (eqb : il ≡ expLLT llb ictb tllb) → IndU icta ictb eqa eqb
--   compIndU icta ictb eqa eqb = compIndU-abs (isEqICT _ _)


pickLL : ∀{u i} → IndexLLCT → ∀ ll rl → LinLogic i {u}
pickLL ic← ll rl = ll
pickLL ic→ ll rl = rl

-- Indexes over a specific node of a linear logic tree. 
data IndexLL {i : Size} {u} (rll : LinLogic i {u}) : LinLogic i {u} → Set (lsuc u) where
  ↓   :                             IndexLL rll rll
  ic : ∀{l r} → {il : LLCT} → (d : IndexLLCT) → IndexLL rll (pickLL d l r) → IndexLL rll (l < il > r)



pickLL-id : ∀{u i} → ∀ d → (q : LinLogic i {u}) → q ≡ pickLL d q q
pickLL-id ic← _ = refl
pickLL-id ic→ _ = refl

pickLL-eq : ∀{u i} → (d : IndexLLCT) → (f g : IndexLLCT → (x y : LinLogic i {u}) → LinLogic i {u})
             → ∀ xf yf xg yg → ∀ {q a} → f ic← xf yf ≡ q → g ic→ xg yg ≡ a
             → pickLL d (f d xf yf) (g d xg yg) ≡ pickLL d q a
pickLL-eq ic← f g _ _ _ _ eqf eqg = eqf
pickLL-eq ic→ f g _ _ _ _ eqf eqg = eqg

pickLL-neq : ∀{u i} → (d1 d2 : IndexLLCT) → ¬ d1 ≡ d2 → (f g : IndexLLCT → (x y : LinLogic i {u}) → LinLogic i {u})
             → ∀ xf yf xg yg → ∀ {q a} → f ic→ xf yf ≡ q → g ic← xg yg ≡ a
             → pickLL d1 (f d2 xf yf) (g d2 xg yg) ≡ pickLL d1 q a
pickLL-neq ic← ic← eq f g _ _ _ _ eqf eqg = ⊥-elim (eq refl)
pickLL-neq ic← ic→ eq f g _ _ _ _ eqf eqg = eqf
pickLL-neq ic→ ic← eq f g _ _ _ _ eqf eqg = eqg
pickLL-neq ic→ ic→ eq f g _ _ _ _ eqf eqg = ⊥-elim (eq refl)


-- -- boo : ∀{u i lla tlla icta il eqa llb tllb ictb eqb fll rll ica icb} → ∀ a b
-- --           → ica ≡ ic {i} {u} {fll} {ll = lla} {tlla} {icta} {il} a {{eqa}}
-- --           → icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} {ictb} {il} b {{eqb}}
-- --           → IndU icta ictb eqa eqb


          

-- elimIndexLL : ∀{u u' i rll} → (P : ∀{ll} → IndexLL {i} {u} rll ll → Set u')
--               → P ↓
--               → (∀{ll tll all} → {ict : IndexLLCT} → {ind : IndexLL rll ll} → {eq : all ≡ (expLLT ll ict tll)} → P ind → P (ic ict eq ind))
--               → {ll : LinLogic i {u}} → (ind : IndexLL rll ll) → P ind 
-- elimIndexLL P p↓ pic ↓ = p↓
-- elimIndexLL P p↓ pic (ic _ _ ind) = pic (elimIndexLL P p↓ pic ind)




module _ where

  replLL : ∀{i u q ll} → (ind : IndexLL {i} {u} q ll) → LinLogic i {u} → LinLogic i {u}
  replLL ↓ c = c
  replLL (ic {l = l} {r} {il} d ind) c = (pickLL d (replLL ind c) l) < il > (pickLL d r (replLL ind c))

  
module _ where

  open Relation.Binary.PropositionalEquality


  replLL-id-abs : ∀ {i u} {l r : LinLogic i {u}} {il} (q : LinLogic i) → ∀ d → (ind : IndexLL q (pickLL d l r))
                  → ∀{w}
                  → w ≡ pickLL d l r
                  →   (pickLL d w l < il > pickLL d r w)
                    ≡
                      (l < il > r)
  replLL-id-abs {l = l} {r} {il} _ d _ refl = cong₂
        (λ x y → x < il >  y)
        (trans (pickLL-eq d pickLL (λ _ _ _ → l) l r l r refl refl) (sym (pickLL-id d l)))
        (trans (pickLL-eq d (λ _ _ _ → r) pickLL l r l r refl refl) (sym (pickLL-id d r))) 


  replLL-id : ∀{i u q ll} → (ind : IndexLL {i} {u} q ll) → replLL ind q ≡ ll
  replLL-id ↓ = refl
  replLL-id {q = q} (ic {l = l} {r = r} {il} d ind) = replLL-id-abs q d ind (replLL-id ind)


