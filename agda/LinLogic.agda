
module LinLogic where

open import Common
open import Data.Unit
import Relation.Binary.PropositionalEquality

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
      ∅    :                                       LinLogic i
      -- Contains a function that computes a dependent type.
      τ    : ∀{n} {dt : Vec (Set u) n} → genT dt → LinLogic i
      -- The input or output of a linear function.
      -- The function can be recursive or corecursive.
      call : ∞LinLogic i {u}                     → LinLogic i
      il[_]  : LinLogicI i {u}                     → LinLogic i

    data LinLogicI (i : Size) {u} : Set (lsuc u) where
      -- Both sub-trees need to be sent or received.
      _∧_  : LinLogic i {u} → LinLogic i {u}     → LinLogicI i
      -- Only one sub-tree can be sent or received
      -- and the protocol specification has no control
      -- over which choice will be made.
      _∨_  : LinLogic i {u} → LinLogic i {u}     → LinLogicI i
      -- Only one sub-tree can be sent or received
      -- and the protocol specification determines the choice
      -- based on the previous input of the agent.
      _∂_  : LinLogic i {u} → LinLogic i {u}     → LinLogicI i

    record ∞LinLogic (i : Size) {u} : Set (lsuc u) where
      coinductive
      field
        step : {j : Size< i} → LinLogic j {u = u}


  open ∞LinLogic public


-- TODO. Do we need more linear transformations?

-- Transformations of the Linear Logic so as to construct
-- the correct sub-tree that is to be the input of a linear function.
data LLTr {i : Size} {u} (rll : LinLogic i {u}) : LinLogic i {u} → Set (lsuc u) where
  -- Identity
  I     : LLTr rll rll
  -- Commutative transformations for ∂, ∧ and ∨.
  ∂c    : ∀{r l} → LLTr rll il[(r ∂ l)] → LLTr rll il[(l ∂ r)]
  ∧c    : ∀{r l} → LLTr rll il[(r ∧ l)] → LLTr rll il[(l ∧ r)]
  ∨c    : ∀{r l} → LLTr rll il[(r ∨ l)] → LLTr rll il[(l ∨ r)]
  -- Distributive transformations.
-- The agent to whom to send r depends on the knowledge of ∂'s answer, this this is impossible.  
--  ∧∂d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∧ r) ∂ (l₂ ∧ r)) → LLTr rll ((l₁ ∂ l₂) ∧ r)                   
  -- Not possible because there are two instances of LinDepT r and we do not know which to choose.
--  ¬∧∂d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∂ l₂) ∧ r) → LLTr rll ((l₁ ∧ r) ∂ (l₂ ∧ r))                
-- The agent to whom to send r depends on the knowledge of ∨'s answer, this this is impossible.  
--  ∧∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∧ r) ∨ (l₂ ∧ r)) → LLTr rll ((l₁ ∨ l₂) ∧ r)                   
  -- Not possible because there are two instances of LinDepT r and we do not know which to choose.
--  ¬∧∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∨ l₂) ∧ r) → LLTr rll ((l₁ ∧ r) ∨ (l₂ ∧ r))
-- Not possible to duplicate resources.  
--  ∧∧d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∧ r) ∧ (l₂ ∧ r)) → LLTr rll ((l₁ ∧ l₂) ∧ r)
-- Not possible to choose which path to take if r arrives, since ∂ might not be triggered at all.
-- The two are not the same.
--   ∨∂d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∨ r) ∂ (l₂ ∨ r)) → LLTr rll ((l₁ ∂ l₂) ∨ r)
  -- Not possible because there are two instances of LinDepT r and we do not know which to choose.
--  ¬∨∂d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∂ l₂) ∨ r) → LLTr rll ((l₁ ∨ r) ∂ (l₂ ∨ r))
-- Not possible to duplicate resources.  
--  ∨∧d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∨ r) ∧ (l₂ ∨ r)) → LLTr rll ((l₁ ∧ l₂) ∨ r)
-- Not possible to choose which path to take if r arrives, since ∂ might not be triggered at all.
-- The two are not the same.
--  ∂∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∂ r) ∨ (l₂ ∂ r)) → LLTr rll ((l₁ ∨ l₂) ∂ r)

-- Not possible because there are two instances of LinDepT r and we do not know which to choose.
--  ¬∂∨d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∨ l₂) ∂ r) → LLTr rll ((l₁ ∂ r) ∨ (l₂ ∂ r))
-- Not possible to duplicate resources.  
--  ∂∧d   : ∀{l₁ l₂ r} → LLTr rll ((l₁ ∂ r) ∧ (l₂ ∂ r)) → LLTr rll ((l₁ ∧ l₂) ∂ r)
-- Associative transformations
  ∧∧d   : ∀{l₁ l₂ r} → LLTr rll il[ l₁ ∧ il[ l₂ ∧ r ] ] → LLTr rll il[ il[ l₁ ∧ l₂ ] ∧ r ]
  ¬∧∧d   : ∀{l₁ l₂ r} → LLTr rll il[ il[ l₁ ∧ l₂ ] ∧ r ] → LLTr rll il[ l₁ ∧ il[ l₂ ∧ r ] ]
  ∨∨d   : ∀{l₁ l₂ r} → LLTr rll il[ l₁ ∨ il[ l₂ ∨ r ] ] → LLTr rll il[ il[ l₁ ∨ l₂ ] ∨ r ]
  ¬∨∨d   : ∀{l₁ l₂ r} → LLTr rll il[ il[ l₁ ∨ l₂ ] ∨ r ] → LLTr rll il[ l₁ ∨ il[ l₂ ∨ r ] ]
  ∂∂d   : ∀{l₁ l₂ r} → LLTr rll il[ l₁ ∂ il[ l₂ ∂ r ] ] → LLTr rll il[ il[ l₁ ∂ l₂ ] ∂ r ]
  ¬∂∂d   : ∀{l₁ l₂ r} → LLTr rll il[ il[ l₁ ∂ l₂ ] ∂ r ] → LLTr rll il[ l₁ ∂ il[ l₂ ∂ r ] ]


revTr : ∀{i u rll ll} → LLTr {i} {u} rll ll → LLTr ll rll
revTr {i} {u} {orll} {oll} ltr = revTr` ltr I where
  revTr` : ∀{x} → LLTr {i} {u} orll x → LLTr oll x → LLTr oll orll
  revTr` I nltr = nltr
  revTr` (∂c ltr) nltr = revTr` ltr (∂c nltr)
  revTr` (∧c ltr) nltr = revTr` ltr (∧c nltr)
  revTr` (∨c ltr) nltr = revTr` ltr (∨c nltr)
  revTr` (∧∧d ltr) nltr = revTr` ltr (¬∧∧d nltr)
  revTr` (¬∧∧d ltr) nltr = revTr` ltr (∧∧d nltr)
  revTr` (∨∨d ltr) nltr = revTr` ltr (¬∨∨d nltr)
  revTr` (¬∨∨d ltr) nltr = revTr` ltr (∨∨d nltr)
  revTr` (∂∂d ltr) nltr =  revTr` ltr (¬∂∂d nltr)
  revTr` (¬∂∂d ltr) nltr =  revTr` ltr (∂∂d nltr)


data IndexLLCT : Set where
  ic←∧ : IndexLLCT 
  ic∧→ : IndexLLCT
  ic←∨ : IndexLLCT
  ic∨→ : IndexLLCT
  ic←∂ : IndexLLCT
  ic∂→ : IndexLLCT


module _ where

  open Relation.Binary.PropositionalEquality
  -- TODO To be removed ?
--  decSym : ∀{u} → {A : Set u} → {a b : A} → Dec (a ≡ b) → Dec (b ≡ a)
--  decSym (yes p) = yes (sym p)
--  decSym (no ¬p) = no λ x → ¬p (sym x)

isEqICT : (a b : IndexLLCT) → Dec (a ≡ b)
isEqICT ic←∧ ic←∧ = yes refl
isEqICT ic←∧ ic∧→ = no (λ ())
isEqICT ic←∧ ic←∨ = no (λ ())
isEqICT ic←∧ ic∨→ = no (λ ())
isEqICT ic←∧ ic←∂ = no (λ ())
isEqICT ic←∧ ic∂→ = no (λ ())
isEqICT ic∧→ ic←∧ = no (λ ())
isEqICT ic∧→ ic∧→ = yes refl
isEqICT ic∧→ ic←∨ = no (λ ())
isEqICT ic∧→ ic∨→ = no (λ ())
isEqICT ic∧→ ic←∂ = no (λ ())
isEqICT ic∧→ ic∂→ = no (λ ())
isEqICT ic←∨ ic←∧ = no (λ ())
isEqICT ic←∨ ic∧→ = no (λ ())
isEqICT ic←∨ ic←∨ = yes refl
isEqICT ic←∨ ic∨→ = no (λ ())
isEqICT ic←∨ ic←∂ = no (λ ())
isEqICT ic←∨ ic∂→ = no (λ ())
isEqICT ic∨→ ic←∧ = no (λ ())
isEqICT ic∨→ ic∧→ = no (λ ())
isEqICT ic∨→ ic←∨ = no (λ ())
isEqICT ic∨→ ic∨→ = yes refl
isEqICT ic∨→ ic←∂ = no (λ ())
isEqICT ic∨→ ic∂→ = no (λ ())
isEqICT ic←∂ ic←∧ = no (λ ())
isEqICT ic←∂ ic∧→ = no (λ ())
isEqICT ic←∂ ic←∨ = no (λ ())
isEqICT ic←∂ ic∨→ = no (λ ())
isEqICT ic←∂ ic←∂ = yes refl
isEqICT ic←∂ ic∂→ = no (λ ())
isEqICT ic∂→ ic←∧ = no (λ ())
isEqICT ic∂→ ic∧→ = no (λ ())
isEqICT ic∂→ ic←∨ = no (λ ())
isEqICT ic∂→ ic∨→ = no (λ ())
isEqICT ic∂→ ic←∂ = no (λ ())
isEqICT ic∂→ ic∂→ = yes refl



expLLT : ∀{i u} → (ll : LinLogic i {u})  → IndexLLCT → (tll : LinLogic i {u}) → LinLogicI i {u}
expLLT {i} {u} ll ic←∧ tll = ll ∧ tll
expLLT {i} {u} ll ic∧→ tll = tll ∧ ll
expLLT {i} {u} ll ic←∨ tll = ll ∨ tll
expLLT {i} {u} ll ic∨→ tll = tll ∨ ll
expLLT {i} {u} ll ic←∂ tll = ll ∂ tll
expLLT {i} {u} ll ic∂→ tll = tll ∂ ll

  
expLLT⇒eq : ∀{i u lla llb tlla tllb icta ictb il}
            → icta ≡ ictb
            → (eqa : il ≡ expLLT {i} {u} lla icta tlla)
            → (eqb : il ≡ expLLT llb ictb tllb)
            → (lla ≡ llb) × (tlla ≡ tllb) × ((icta , lla , tlla , eqa) ≡ (ictb , llb , tllb , eqb))
expLLT⇒eq {icta = ic←∧} refl refl refl = refl , refl , refl
expLLT⇒eq {icta = ic∧→} refl refl refl = refl , refl , refl
expLLT⇒eq {icta = ic←∨} refl refl refl = refl , refl , refl
expLLT⇒eq {icta = ic∨→} refl refl refl = refl , refl , refl
expLLT⇒eq {icta = ic←∂} refl refl refl = refl , refl , refl
expLLT⇒eq {icta = ic∂→} refl refl refl = refl , refl , refl

expLLT⇒req : ∀{i u ll1 ll2 tll1 tll2 ict1 ict2 il} → ¬ ict1 ≡ ict2 → il ≡ expLLT {i} {u} ll1 ict1 tll1 → il ≡ expLLT ll2 ict2 tll2 → (ll1 ≡ tll2) × (ll2 ≡ tll1)
expLLT⇒req {ict1 = ic←∧} {ic←∧} ¬p eq = ⊥-elim (¬p refl)
expLLT⇒req {ict1 = ic←∧} {ic∧→} ¬p refl refl = refl , refl
expLLT⇒req {ict1 = ic←∧} {ic←∨} ¬p refl ()
expLLT⇒req {ict1 = ic←∧} {ic∨→} ¬p refl ()
expLLT⇒req {ict1 = ic←∧} {ic←∂} ¬p refl ()
expLLT⇒req {ict1 = ic←∧} {ic∂→} ¬p refl ()
expLLT⇒req {ict1 = ic∧→} {ic←∧} ¬p refl refl = refl , refl
expLLT⇒req {ict1 = ic∧→} {ic∧→} ¬p eq = ⊥-elim (¬p refl)
expLLT⇒req {ict1 = ic∧→} {ic←∨} ¬p refl ()
expLLT⇒req {ict1 = ic∧→} {ic∨→} ¬p refl ()
expLLT⇒req {ict1 = ic∧→} {ic←∂} ¬p refl ()
expLLT⇒req {ict1 = ic∧→} {ic∂→} ¬p refl ()
expLLT⇒req {ict1 = ic←∨} {ic←∧} ¬p refl ()
expLLT⇒req {ict1 = ic←∨} {ic∧→} ¬p refl ()
expLLT⇒req {ict1 = ic←∨} {ic←∨} ¬p eq = ⊥-elim (¬p refl)
expLLT⇒req {ict1 = ic←∨} {ic∨→} ¬p refl refl = refl , refl
expLLT⇒req {ict1 = ic←∨} {ic←∂} ¬p refl ()
expLLT⇒req {ict1 = ic←∨} {ic∂→} ¬p refl ()
expLLT⇒req {ict1 = ic∨→} {ic←∧} ¬p refl ()
expLLT⇒req {ict1 = ic∨→} {ic∧→} ¬p refl ()
expLLT⇒req {ict1 = ic∨→} {ic←∨} ¬p refl refl = refl , refl
expLLT⇒req {ict1 = ic∨→} {ic∨→} ¬p eq = ⊥-elim (¬p refl)
expLLT⇒req {ict1 = ic∨→} {ic←∂} ¬p refl ()
expLLT⇒req {ict1 = ic∨→} {ic∂→} ¬p refl ()
expLLT⇒req {ict1 = ic←∂} {ic←∧} ¬p refl ()
expLLT⇒req {ict1 = ic←∂} {ic∧→} ¬p refl ()
expLLT⇒req {ict1 = ic←∂} {ic←∨} ¬p refl ()
expLLT⇒req {ict1 = ic←∂} {ic∨→} ¬p refl ()
expLLT⇒req {ict1 = ic←∂} {ic←∂} ¬p eq = ⊥-elim (¬p refl)
expLLT⇒req {ict1 = ic←∂} {ic∂→} ¬p refl refl = refl , refl
expLLT⇒req {ict1 = ic∂→} {ic←∧} ¬p refl ()
expLLT⇒req {ict1 = ic∂→} {ic∧→} ¬p refl ()
expLLT⇒req {ict1 = ic∂→} {ic←∨} ¬p refl ()
expLLT⇒req {ict1 = ic∂→} {ic∨→} ¬p refl ()
expLLT⇒req {ict1 = ic∂→} {ic←∂} ¬p refl refl = refl , refl
expLLT⇒req {ict1 = ic∂→} {ic∂→} ¬p eq = ⊥-elim (¬p refl)



rexpLLT⇒req : ∀{i u ll tll ict1 ict2 il x1 x2 y1 y2} → ¬ ict1 ≡ ict2
      → il ≡ expLLT {i} {u} x1 ict1 x2
      → il ≡ expLLT {i} {u} y1 ict2 y2
      → expLLT {i} {u} ll ict2 tll ≡ expLLT tll ict1 ll
rexpLLT⇒req {ict1 = ic←∧} {ic←∧} ¬p eqa eqb = ⊥-elim (¬p refl)
rexpLLT⇒req {ict1 = ic←∧} {ic∧→} ¬p eqa eqb = refl
rexpLLT⇒req {ict1 = ic←∧} {ic←∨} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∧} {ic∨→} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∧} {ic←∂} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∧} {ic∂→} ¬p refl ()
rexpLLT⇒req {ict1 = ic∧→} {ic←∧} ¬p eqa eqb = refl
rexpLLT⇒req {ict1 = ic∧→} {ic∧→} ¬p eqa eqb = ⊥-elim (¬p refl)
rexpLLT⇒req {ict1 = ic∧→} {ic←∨} ¬p refl ()
rexpLLT⇒req {ict1 = ic∧→} {ic∨→} ¬p refl ()
rexpLLT⇒req {ict1 = ic∧→} {ic←∂} ¬p refl ()
rexpLLT⇒req {ict1 = ic∧→} {ic∂→} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∨} {ic←∧} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∨} {ic∧→} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∨} {ic←∨} ¬p eqa eqb = ⊥-elim (¬p refl)
rexpLLT⇒req {ict1 = ic←∨} {ic∨→} ¬p eqa eqb = refl
rexpLLT⇒req {ict1 = ic←∨} {ic←∂} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∨} {ic∂→} ¬p refl ()
rexpLLT⇒req {ict1 = ic∨→} {ic←∧} ¬p refl ()
rexpLLT⇒req {ict1 = ic∨→} {ic∧→} ¬p refl ()
rexpLLT⇒req {ict1 = ic∨→} {ic←∨} ¬p eqa eqb = refl
rexpLLT⇒req {ict1 = ic∨→} {ic∨→} ¬p eqa eqb = ⊥-elim (¬p refl)
rexpLLT⇒req {ict1 = ic∨→} {ic←∂} ¬p refl ()
rexpLLT⇒req {ict1 = ic∨→} {ic∂→} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∂} {ic←∧} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∂} {ic∧→} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∂} {ic←∨} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∂} {ic∨→} ¬p refl ()
rexpLLT⇒req {ict1 = ic←∂} {ic←∂} ¬p eqa eqb = ⊥-elim (¬p refl)
rexpLLT⇒req {ict1 = ic←∂} {ic∂→} ¬p eqa eqb = refl
rexpLLT⇒req {ict1 = ic∂→} {ic←∧} ¬p refl ()
rexpLLT⇒req {ict1 = ic∂→} {ic∧→} ¬p refl ()
rexpLLT⇒req {ict1 = ic∂→} {ic←∨} ¬p refl ()
rexpLLT⇒req {ict1 = ic∂→} {ic∨→} ¬p refl ()
rexpLLT⇒req {ict1 = ic∂→} {ic←∂} ¬p eqa eqb = refl
rexpLLT⇒req {ict1 = ic∂→} {ic∂→} ¬p eqa eqb = ⊥-elim (¬p refl)


data IndU {i u il} (icta ictb : IndexLLCT) {lla llb tlla tllb : LinLogic i {u}} (eqa : il ≡ expLLT lla icta tlla) (eqb : il ≡ expLLT llb ictb tllb) : Set (lsuc u) where
  ictEq : (icteq : icta ≡ ictb) → (lleq : lla ≡ llb) → (tlleq : tlla ≡ tllb) → (eqeq : (icta , lla , tlla , eqa) ≡ (ictb , llb , tllb , eqb)) → IndU _ _ _ _
  ict¬Eq : (¬icteq : ¬ icta ≡ ictb) → (reqa : lla ≡ tllb) → (reqb : llb ≡ tlla) → IndU _ _ _ _

module _ where

  compIndU-abs : ∀{i u il} {icta ictb : IndexLLCT} {lla llb tlla tllb : LinLogic i {u}} {eqa : il ≡ expLLT lla icta tlla} {eqb : il ≡ expLLT llb ictb tllb} → Dec (icta ≡ ictb) → IndU icta ictb eqa eqb
  compIndU-abs {eqa = eqa} {eqb} (yes p) = ictEq p (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) where
    r = expLLT⇒eq p eqa eqb
  compIndU-abs {eqa = eqa} {eqb} (no ¬p) = ict¬Eq ¬p (proj₁ r) (proj₂ r) where
    r = expLLT⇒req ¬p eqa eqb
  
  compIndU : ∀{i u il} {icta ictb : IndexLLCT} {lla llb tlla tllb : LinLogic i {u}} {eqa : il ≡ expLLT lla icta tlla} {eqb : il ≡ expLLT llb ictb tllb} → IndU icta ictb eqa eqb
  compIndU = compIndU-abs (isEqICT _ _)




-- Indexes over a specific node of a linear logic tree. 
data IndexLL {i : Size} {u} (rll : LinLogic i {u}) : LinLogic i {u} → Set (lsuc u) where
  ↓   :                             IndexLL rll rll
  ic : ∀{ll tll ict il} → IndexLL rll ll → {{eq : il ≡ (expLLT ll ict tll)}} → IndexLL rll il[ il ]



-- boo : ∀{u i lla tlla icta il eqa llb tllb ictb eqb fll rll ica icb} → ∀ a b
--           → ica ≡ ic {i} {u} {fll} {ll = lla} {tlla} {icta} {il} a {{eqa}}
--           → icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} {ictb} {il} b {{eqb}}
--           → IndU icta ictb eqa eqb


          

elimIndexLL : ∀{u u' i rll} → (P : ∀{ll} → IndexLL {i} {u} rll ll → Set u')
              → P ↓
              → (∀{ll tll all} → {ict : IndexLLCT} → {ind : IndexLL rll ll} → {{eq : all ≡ (expLLT ll ict tll)}} → P ind → P (ic {ll = ll} {tll} {ict} ind {{eq}} ))
              → {ll : LinLogic i {u}} → (ind : IndexLL rll ll) → P ind 
elimIndexLL P p↓ pic ↓ = p↓
elimIndexLL P p↓ pic (ic ind) = pic (elimIndexLL P p↓ pic ind)


-- TODO To be removed ?
data IndexLLGCT : Set where
  h : IndexLLGCT
  o : (ict : IndexLLCT) → IndexLLGCT 


-- TODO To be removed ?
expLLGT : ∀{i u} → {ll : LinLogic i {u}}  → IndexLLGCT → (tll : LinLogic i {u}) → LinLogic i {u}
expLLGT {ll = ll} h tll = ll
expLLGT {ll = ll} (o ict) tll = il[ expLLT ll ict tll ]



module _ where

  replLL : ∀{i u q ll} → (ind : IndexLL {i} {u} q ll) → LinLogic i {u} → LinLogic i {u}
  replLL ↓ c = c
  replLL (ic {ll = ll} {tll} {ict} ind) c = il[ expLLT (replLL ind c) ict tll ]

  
module _ where

  open import Relation.Binary.PropositionalEquality

  replLL-id : ∀{i u q ll} → (ind : IndexLL q ll) → (s : LinLogic i {u}) → q ≡ s → replLL ind s ≡ ll
  replLL-id ↓ s eq = sym eq
  replLL-id (ic {ll} {tll} {ict = ict} ind {{refl}}) s eq = cong (λ x → il[ expLLT x ict _ ]) (replLL-id ind s eq)
  
  
