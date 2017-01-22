--{-# OPTIONS --exact-split #-}
{-# OPTIONS --show-implicit #-}

module LinFun where

open import LinT public
open import Size
open import Function
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
import Level


-- We send to the receiver both the values the type depends and the value of the type. This way, we achieve locality in terms of finding the type of the incoming value.
-- We need to point that the receiver and the sender are the same node.

module _ where

  open SetLLMp
  open Level
  
  mutual
    data LFun {u} : {i : Size} → {j : Size< ↑ i} → {rll : LinLogic j {u}} → {ll : LinLogic i {u}} → Set (suc u) where
     I   : {i : Size} → ∀{rll} → LFun {i = i} {j = i} {rll = rll} {ll = rll}
     _⊂_ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{pll ll ell rll} → {ind : IndexLL pll ll} → (elf : LFun {i = i} {j = j} {rll = ell} {ll = pll})
           → {{prf : usesInput elf}} → LFun {i = j} {j = k} {rll = rll} {ll = (replLL ll ind ell)}
           → LFun {i = i} {j = k} {rll = rll} {ll = ll}
     --Do we need to set ltr as an instance variable?
     tr  : {i : Size} → {j : Size< ↑ i} → ∀{ll orll rll} → {{ltr : LLTr orll ll}} → LFun {i = i} {j = j} {rll = rll} {ll = orll} → LFun {i = i} {j = j} {rll = rll} {ll = ll}
     obs : {i : Size} → {j : Size< i} → {k : Size< ↑ j} → ∀{∞ll rll} → LFun {i = j} {j = k} {rll = rll} {ll = (step ∞ll)} → LFun {i = i} {j = k} {rll = rll} {ll = call ∞ll}
     com : {i : Size} → {j : Size< ↑ i} → {rll : LinLogic j} → {ll frll : LinLogic i} → ⦃ prfi : onlyOneNilOrNoNilFinite ll ≡ true ⦄
           → ⦃ prfo : onlyOneNilOrNoNilFinite frll ≡ true ⦄
           → (df : (ldt : LinDepT ll) → LinT ldt → LinDepT frll) → LFun {rll = rll} {ll = frll}
           → LFun {rll = rll} {ll = ll}
     call : {i : Size} → {j : Size< i} → ∀{ll ∞rll rll} → ∞LFun {∞rll = ∞rll} {ll = ll} → LFun {i = i} {j = j} {rll = rll} {ll = call ∞rll} → LFun {i = i} {j = j} {rll = rll} {ll = ll}
  
  
    record ∞LFun {i : Size} {u} {∞rll : ∞LinLogic i {u}} {ll : LinLogic i {u}} : Set (suc u) where
      coinductive
      field
        step : {j : Size< i} → LFun {i = i} {j = j} {rll = (step ∞rll)} {ll}


    usesInput : {i : Size} → {j : Size< ↑ i } → ∀{u rll ll} → LFun {u = u} {i = i} {j = j} {rll = rll} {ll = ll} → Set
    usesInput x = usesInput` x ∅ where
      usesInput` : {i : Size} → {j : Size< ↑ i} → ∀{u} → {rll : LinLogic j {u} } → {ll : LinLogic i {u} } → LFun {rll = rll} {ll = ll} → MSetLL ll → Set
      usesInput` I s = ⊥
      usesInput` (_⊂_ {j = j} {k = k} {ell = ell} {ind = ind} elf lf) ∅ = usesInput` {i = j} {j = k} lf (¬∅ (∅-add ind ell))
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ↓} elf lf) (¬∅ s) with (contruct $ add {i = i} {j = j} s ↓ ell)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ↓} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ↓} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∧} elf lf) (¬∅ s) with (contruct $ add s (ind ←∧) ell)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∧} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∧} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∧→ ind} elf lf) (¬∅ s) with (contruct $ add s (∧→ ind) ell)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∧→ ind} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∧→ ind} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∨} elf lf) (¬∅ s) with (contruct $ add s (ind ←∨) ell)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∨} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∨} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∨→ ind} elf lf) (¬∅ s) with (contruct $ add s (∨→ ind) ell)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∨→ ind} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∨→ ind} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∂} elf lf) (¬∅ s) with (contruct $ add s (ind ←∂) ell)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∂} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∂} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∂→ ind} elf lf) (¬∅ s) with (contruct $ add s (∂→ ind) ell)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∂→ ind} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∂→ ind} elf lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
      usesInput` (tr lf) ∅ = usesInput` lf ∅
      usesInput` (tr {{ltr = ltr}} lf) (¬∅ s) = usesInput` lf $ ¬∅ (SetLLMp.tran s ltr)
      usesInput` (obs {j = lj} {k = lk} {∞ll = ∞ll} x) s = usesInput` {i = lj} {j = lk} x (∅ {ll = (step ∞ll)})
      usesInput` (com df lf) s = ⊤
      usesInput` (call ∞x x) s = ⊥

open ∞LFun public



module _ where

  open SetLLMp
  open import Data.List
  open import Data.Nat

  -- Here we assume that cut removes call and obs as soon as the call is possible to be executed,
  -- thus if we reach at a call, we do not continue, it means that this specific subtree will not contain a com
  -- to execute this communication pattern.

  fstSp : ∀ {i u ll rll} → (s : SetLL {i} {u} ll) → (ltr : LLTr {i} {u} rll ll) → ⦃ prf : (zero < (length (sptran s ltr))) ⦄ 
          → SetLL {i} {u} rll
  fstSp s ltr {{prf = prf}} with (sptran s ltr)
  fstSp s ltr {{()}} | []
  fstSp s ltr {{prf}} | x ∷ r = x

  sndSp : ∀ {i u ll rll} → (s : SetLL {i} {u} ll) → (ltr : LLTr {i} {u} rll ll) → ⦃ prf : ((suc zero) < (length (sptran s ltr))) ⦄ 
          → SetLL {i} {u} rll
  sndSp s ltr {{prf = prf}} with (sptran s ltr)
  sndSp s ltr {{()}} | []
  sndSp s ltr {{s≤s ()}} | x ∷ []
  sndSp s ltr {{prf}} | x ∷ x₁ ∷ r = x₁

  data cuttable {u} : ∀{i} → {j : Size< ↑ i} → ∀{rll ll} → SetLL ll → LFun {u} {i} {j} {rll} {ll} → Set (Level.suc u) where
    cuttable-s-com : ∀{rll ll s frll prfi prfo  df lf}
                     → ⦃ prf : contruct s ≡ ↓ ⦄
                     → cuttable {u = u} s (com {rll = rll} {ll = ll} {frll = frll}  ⦃ prfi = prfi ⦄ ⦃ prfo = prfo ⦄ df lf)
    cuttable-s⊂-ex : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{ll rll ell pll s ind lf prf lf₁}
                     → ⦃ ex : exactHit {ll = ll} {rll = pll} (contruct s) ind ⦄
                     → cuttable {rll = ell} {ll = pll} (truncExSetLL {pll = pll} s ind {{prf = ex}}) lf
                     → cuttable {i = i} {j = k} {rll = rll} {ll = ll} s (_⊂_ {i = i} {j = j} {k = k} {pll = pll} {ll = ll} {ell = ell} {ind = ind} lf ⦃ prf = prf ⦄ lf₁)
    cuttable-s⊂-ho : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{ll rll pll ell s ind lf prf lf₁}
                     → ⦃ ¬ho : ¬ (hitsOnce {ll = ll} {rll = pll} s ind) ⦄
                     → cuttable {rll = rll} (replSetLL s ind {{prf = ¬ho }} ell) lf₁
                     → cuttable {i = i} {j = k} {rll = rll} {ll = ll} s (_⊂_ {i = i} {j = j} {k = k} {pll = pll} {ll = ll} {ell = ell} {ind = ind} lf ⦃ prf = prf ⦄ lf₁)
    cuttable-s-tr-fst : ∀{ll orll rll lf s ltr prftr}
                        → cuttable {rll = rll} {ll = orll} (fstSp s ltr ⦃ prf = prftr ⦄) lf
                        → cuttable s (tr {ll = ll} {orll = orll} {rll = rll} ⦃ ltr = ltr ⦄ lf)
    cuttable-s-tr-snd : ∀{ll orll rll lf s ltr prftr}
                        → cuttable {rll = rll} {ll = orll} (sndSp s ltr ⦃ prf = prftr ⦄) lf
                        → cuttable s (tr {ll = ll} {orll = orll} {rll = rll} ⦃ ltr = ltr ⦄ lf)


  helpFunEx : ∀{u} → {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{ll rll ell pll s ind lf prf lf₁} → cuttable {u = u} {i = i} {j = k} {rll = rll} {ll = ll} s (_⊂_ {i = i} {j = j} {k = k} {pll = pll} {ll = ll} {ell = ell} {ind = ind} lf ⦃ prf = prf ⦄ lf₁) → (ex : exactHit {i} {u} {ll} {pll} (contruct s) ind) → ¬ (cuttable {u} {i} {j} {ell} {pll} (truncExSetLL {pll = pll} s ind {{prf = ex}})) lf → ⊥
  helpFunEx {u} {i} {j} {k} {ll} {rll} {ell} {pll} {s} {ind} {lf} {prf} {lf₁} (cuttable-s⊂-ex {i = .i} {j = .j} {k = .k} {ll = .ll} {rll = .rll} {ell = .ell} {pll = .pll} {s = .s} {ind = .ind} {lf = .lf} {prf = .prf} {lf₁ = .lf₁} {{ex = .ex}} ct) ex ¬p = {!¬p !}
  helpFunEx {u} {i} {j} {k} {ll} {rll} {ell} {pll} {s} {ind} {lf} {prf} {lf₁} (cuttable-s⊂-ho {i = .i} {j = .j} {k = .k} {ll = .ll} {rll = .rll} {pll = .pll} {ell = .ell} {s = .s} {ind = .ind} {lf = .lf} {prf = .prf} {lf₁ = .lf₁} {{¬ho = ¬ho}} ct) ex p = {!!}

  canItBeCut : ∀{i} → {j : Size< ↑ i} → ∀{u rll ll} → (s : SetLL ll) → (lf : LFun {u} {i} {j} {rll} {ll}) → Dec (cuttable {i = i} {j = j} {rll = rll} {ll = ll} s lf)
  canItBeCut s I = no (λ ())
  canItBeCut {.gi} {.gk} {u} {.grll} {.gll} s (_⊂_ {gi} {gj} {gk} {gpll} {gll} {gell} {grll} {gind} glf glf₁) with (isExactHit {ll = gll} {rll = gpll} (contruct s) gind)
  canItBeCut {.gi} {.gk} {u} {.grll} {.gll} s (_⊂_ {gi} {gj} {gk} {gpll} {gll} {gell} {grll} {gind} glf glf₁) | yes gex with (canItBeCut {rll = gell} {ll = gpll} (truncExSetLL {pll = gpll} s gind {{prf = gex}}) glf)
  canItBeCut {.gi} {.gk} {u} {.grll} {.gll} s (_⊂_ {gi} {gj} {gk} {gpll} {gll} {gell} {grll} {gind} glf glf₁) | yes gex | (yes gp) = yes (cuttable-s⊂-ex {i = gi} {j = gj} {k = gk} ⦃ ex = gex ⦄ gp)
  canItBeCut {.gi} {.gk} {u} {.grll} {.gll} s (_⊂_ {gi} {gj} {gk} {gpll} {gll} {gell} {grll} {gind} glf glf₁) | yes gex | (no ¬gp) = no ((λ { (cuttable-s⊂-ex x) → {!¬gp x!}
                                                                                                                                         ; (cuttable-s⊂-ho x) → {!!} }))
  canItBeCut {_} {.k} s (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁)    | no ¬ex with (doesItHitOnce s ind)
  canItBeCut {_} {.k} s (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁)    | no ¬ex | (yes ho) = no {!!}
  canItBeCut {_} {.k} s (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁)  | no ¬ex | (no ¬ho) with (canItBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁)
  canItBeCut {_} {.k} s (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁)    | no ¬ex | (no ¬ho) | (yes p) = {!!}
  canItBeCut {_} {.k} s (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁)    | no ¬ex | (no ¬ho) | (no ¬p) = {!!}

--  canItBeCut s (lf ⊂ lf₁) = {!!}
  canItBeCut s (tr lf) = {!!}
  canItBeCut s (obs lf) = no (λ ())
  canItBeCut s (com df lf) = {!!}
  canItBeCut s (call x lf) = no (λ ())

--  canBeCut ↓ I = (false , ∅)
--  canBeCut ↓ (lf ⊂ lf₁) = (false , ∅)
--  canBeCut ↓ (tr {{ltr = ltr}} lf) = foldl (λ {(false , r) x → canBeCut x lf
--                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran ↓ ltr)
--  canBeCut ↓ (obs lf) = (false , ∅)
--  canBeCut ↓ (com {ll = ll} df lf) = (true , ll)
--  canBeCut ↓ (call x lf) = (false , ∅)
--  canBeCut (_ ←∧) I = (false , ∅)
--  canBeCut {j = .k} s@(_ ←∧) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
--  canBeCut {_} {.k} s@(_ ←∧) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
--  canBeCut {_} {.k} s@(_ ←∧) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
--  canBeCut {_} {.k} (_ ←∧) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
--  canBeCut {_} {.k} s@(_ ←∧) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
--  canBeCut s@(_ ←∧) (tr {{ltr = ltr}} lf) = foldl (λ {(false , r) x → canBeCut x lf
--                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
--  canBeCut (_ ←∧) (com {ll = ll} df lf) = (false , ∅)
--  canBeCut (_ ←∧) (call x₁ lf) = (false , ∅)
--  canBeCut (∧→ x) I = (false , ∅)
--  canBeCut {j = .k} s@(∧→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
--  canBeCut {_} {.k} s@(∧→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
--  canBeCut {_} {.k} s@(∧→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
--  canBeCut {_} {.k} (∧→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
--  canBeCut {_} {.k} s@(∧→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
--  canBeCut s@(∧→ x) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
--                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
--  canBeCut (∧→ x) (com {ll = ll} df lf) = (false , ∅)
--  canBeCut (∧→ x) (call x₁ lf) = (false , ∅)
--  canBeCut (x ←∧→ x₁) I = (false , ∅)
--  canBeCut {j = .k} s@(_ ←∧→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
--  canBeCut {_} {.k} s@(_ ←∧→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
--  canBeCut {_} {.k} s@(_ ←∧→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
--  canBeCut {_} {.k} (_ ←∧→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
--  canBeCut {_} {.k} s@(_ ←∧→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
--  canBeCut s@(x ←∧→ x₁) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
--                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
--  canBeCut s@(x ←∧→ x₁) (com {ll = ll} df lf) with (contruct s)
--  canBeCut (x ←∧→ x₁) (com {ll = ll} df lf) | ↓ = (true , ll)
--  canBeCut (x ←∧→ x₁) (com {ll = ll} df lf) | r ←∧ = (false , ∅)
--  canBeCut (x ←∧→ x₁) (com {ll = ll} df lf) | ∧→ r = (false , ∅)
--  canBeCut (x ←∧→ x₁) (com {ll = ll} df lf) | r ←∧→ r₁ = (false , ∅)
--  canBeCut (x ←∧→ x₁) (call x₂ lf) = (false , ∅)
--  canBeCut (_ ←∨) I = (false , ∅)
--  canBeCut {j = .k} s@(_ ←∨) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
--  canBeCut {_} {.k} s@(_ ←∨) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
--  canBeCut {_} {.k} s@(_ ←∨) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
--  canBeCut {_} {.k} (_ ←∨) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
--  canBeCut {_} {.k} s@(_ ←∨) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
--  canBeCut s@(_ ←∨) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
--                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
--  canBeCut (_ ←∨) (com {ll = ll} df lf) = (false , ∅)
--  canBeCut (_ ←∨) (call x₁ lf) = (false , ∅)
--  canBeCut (∨→ x) I = (false , ∅)
--  canBeCut {j = .k} s@(∨→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
--  canBeCut {_} {.k} s@(∨→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
--  canBeCut {_} {.k} s@(∨→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
--  canBeCut {_} {.k} (∨→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
--  canBeCut {_} {.k} s@(∨→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
--  canBeCut s@(∨→ x) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
--                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
--  canBeCut (∨→ x) (com {ll = ll} df lf) = (false , ∅)
--  canBeCut (∨→ x) (call x₁ lf) = (false , ∅)
--  canBeCut (x ←∨→ x₁) I = (false , ∅)
--  canBeCut {j = .k} s@(_ ←∨→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
--  canBeCut {_} {.k} s@(_ ←∨→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
--  canBeCut {_} {.k} s@(_ ←∨→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
--  canBeCut {_} {.k} (_ ←∨→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
--  canBeCut {_} {.k} s@(_ ←∨→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
--  canBeCut s@(x ←∨→ x₁) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
--                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
--  canBeCut s@(x ←∨→ x₁) (com {ll = ll} df lf) with (contruct s)
--  canBeCut (x ←∨→ x₁) (com {ll = ll} df lf) | ↓ = (true , ll)
--  canBeCut (x ←∨→ x₁) (com {ll = ll} df lf) | r ←∨ = (false , ∅)
--  canBeCut (x ←∨→ x₁) (com {ll = ll} df lf) | ∨→ r = (false , ∅)
--  canBeCut (x ←∨→ x₁) (com {ll = ll} df lf) | r ←∨→ r₁ = (false , ∅)
--  canBeCut (x ←∨→ x₁) (call x₂ lf) = (false , ∅)
--  canBeCut (_ ←∂) I = (false , ∅)
--  canBeCut {j = .k} s@(_ ←∂) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
--  canBeCut {_} {.k} s@(_ ←∂) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
--  canBeCut {_} {.k} s@(_ ←∂) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
--  canBeCut {_} {.k} (_ ←∂) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
--  canBeCut {_} {.k} s@(_ ←∂) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
--  canBeCut s@(_ ←∂) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
--                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
--  canBeCut (_ ←∂) (com {ll = ll} df lf) = (false , ∅)
--  canBeCut (_ ←∂) (call x₁ lf) = (false , ∅)
--  canBeCut (∂→ x) I = (false , ∅)
--  canBeCut {j = .k} s@(∂→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
--  canBeCut {_} {.k} s@(∂→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
--  canBeCut {_} {.k} s@(∂→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
--  canBeCut {_} {.k} (∂→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
--  canBeCut {_} {.k} s@(∂→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
--  canBeCut s@(∂→ x) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
--                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
--  canBeCut (∂→ x) (com {ll = ll} df lf) = (false , ∅)
--  canBeCut (∂→ x) (call x₁ lf) = (false , ∅)
--  canBeCut (x ←∂→ x₁) I = (false , ∅)
--  canBeCut {j = .k} s@(_ ←∂→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
--  canBeCut {_} {.k} s@(_ ←∂→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
--  canBeCut {_} {.k} s@(_ ←∂→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
--  canBeCut {_} {.k} (_ ←∂→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
--  canBeCut {_} {.k} s@(_ ←∂→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
--  canBeCut s@(x ←∂→ x₁) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
--                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
--  canBeCut s@(x ←∂→ x₁) (com {ll = ll} df lf) with (contruct s)
--  canBeCut (x ←∂→ x₁) (com {ll = ll} df lf) | ↓ = (true , ll)
--  canBeCut (x ←∂→ x₁) (com {ll = ll} df lf) | r ←∂ = (false , ∅)
--  canBeCut (x ←∂→ x₁) (com {ll = ll} df lf) | ∂→ r = (false , ∅)
--  canBeCut (x ←∂→ x₁) (com {ll = ll} df lf) | r ←∂→ r₁ = (false , ∅)
--  canBeCut (x ←∂→ x₁) (call x₂ lf) = (false , ∅)
--

  canBeCut : ∀{i} → {j : Size< ↑ i} → ∀{u rll ll} → SetLL ll → LFun {u} {i} {j} {rll} {ll} → Bool × LinLogic j {u}
  canBeCut ↓ I = (false , ∅)
  canBeCut ↓ (lf ⊂ lf₁) = (false , ∅)
  canBeCut ↓ (tr {{ltr = ltr}} lf) = foldl (λ {(false , r) x → canBeCut x lf
                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran ↓ ltr)
  canBeCut ↓ (obs lf) = (false , ∅)
  canBeCut ↓ (com {ll = ll} df lf) = (true , ll)
  canBeCut ↓ (call x lf) = (false , ∅)
  canBeCut (_ ←∧) I = (false , ∅)
  canBeCut {j = .k} s@(_ ←∧) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
  canBeCut {_} {.k} s@(_ ←∧) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
  canBeCut {_} {.k} s@(_ ←∧) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
  canBeCut {_} {.k} (_ ←∧) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
  canBeCut {_} {.k} s@(_ ←∧) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
  canBeCut s@(_ ←∧) (tr {{ltr = ltr}} lf) = foldl (λ {(false , r) x → canBeCut x lf
                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
  canBeCut (_ ←∧) (com {ll = ll} df lf) = (false , ∅)
  canBeCut (_ ←∧) (call x₁ lf) = (false , ∅)
  canBeCut (∧→ x) I = (false , ∅)
  canBeCut {j = .k} s@(∧→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
  canBeCut {_} {.k} s@(∧→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
  canBeCut {_} {.k} s@(∧→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
  canBeCut {_} {.k} (∧→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
  canBeCut {_} {.k} s@(∧→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
  canBeCut s@(∧→ x) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
  canBeCut (∧→ x) (com {ll = ll} df lf) = (false , ∅)
  canBeCut (∧→ x) (call x₁ lf) = (false , ∅)
  canBeCut (x ←∧→ x₁) I = (false , ∅)
  canBeCut {j = .k} s@(_ ←∧→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
  canBeCut {_} {.k} s@(_ ←∧→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
  canBeCut {_} {.k} s@(_ ←∧→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
  canBeCut {_} {.k} (_ ←∧→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
  canBeCut {_} {.k} s@(_ ←∧→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
  canBeCut s@(x ←∧→ x₁) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
  canBeCut s@(x ←∧→ x₁) (com {ll = ll} df lf) with (contruct s)
  canBeCut (x ←∧→ x₁) (com {ll = ll} df lf) | ↓ = (true , ll)
  canBeCut (x ←∧→ x₁) (com {ll = ll} df lf) | r ←∧ = (false , ∅)
  canBeCut (x ←∧→ x₁) (com {ll = ll} df lf) | ∧→ r = (false , ∅)
  canBeCut (x ←∧→ x₁) (com {ll = ll} df lf) | r ←∧→ r₁ = (false , ∅)
  canBeCut (x ←∧→ x₁) (call x₂ lf) = (false , ∅)
  canBeCut (_ ←∨) I = (false , ∅)
  canBeCut {j = .k} s@(_ ←∨) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
  canBeCut {_} {.k} s@(_ ←∨) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
  canBeCut {_} {.k} s@(_ ←∨) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
  canBeCut {_} {.k} (_ ←∨) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
  canBeCut {_} {.k} s@(_ ←∨) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
  canBeCut s@(_ ←∨) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
  canBeCut (_ ←∨) (com {ll = ll} df lf) = (false , ∅)
  canBeCut (_ ←∨) (call x₁ lf) = (false , ∅)
  canBeCut (∨→ x) I = (false , ∅)
  canBeCut {j = .k} s@(∨→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
  canBeCut {_} {.k} s@(∨→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
  canBeCut {_} {.k} s@(∨→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
  canBeCut {_} {.k} (∨→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
  canBeCut {_} {.k} s@(∨→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
  canBeCut s@(∨→ x) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
  canBeCut (∨→ x) (com {ll = ll} df lf) = (false , ∅)
  canBeCut (∨→ x) (call x₁ lf) = (false , ∅)
  canBeCut (x ←∨→ x₁) I = (false , ∅)
  canBeCut {j = .k} s@(_ ←∨→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
  canBeCut {_} {.k} s@(_ ←∨→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
  canBeCut {_} {.k} s@(_ ←∨→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
  canBeCut {_} {.k} (_ ←∨→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
  canBeCut {_} {.k} s@(_ ←∨→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
  canBeCut s@(x ←∨→ x₁) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
  canBeCut s@(x ←∨→ x₁) (com {ll = ll} df lf) with (contruct s)
  canBeCut (x ←∨→ x₁) (com {ll = ll} df lf) | ↓ = (true , ll)
  canBeCut (x ←∨→ x₁) (com {ll = ll} df lf) | r ←∨ = (false , ∅)
  canBeCut (x ←∨→ x₁) (com {ll = ll} df lf) | ∨→ r = (false , ∅)
  canBeCut (x ←∨→ x₁) (com {ll = ll} df lf) | r ←∨→ r₁ = (false , ∅)
  canBeCut (x ←∨→ x₁) (call x₂ lf) = (false , ∅)
  canBeCut (_ ←∂) I = (false , ∅)
  canBeCut {j = .k} s@(_ ←∂) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
  canBeCut {_} {.k} s@(_ ←∂) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
  canBeCut {_} {.k} s@(_ ←∂) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
  canBeCut {_} {.k} (_ ←∂) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
  canBeCut {_} {.k} s@(_ ←∂) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
  canBeCut s@(_ ←∂) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
  canBeCut (_ ←∂) (com {ll = ll} df lf) = (false , ∅)
  canBeCut (_ ←∂) (call x₁ lf) = (false , ∅)
  canBeCut (∂→ x) I = (false , ∅)
  canBeCut {j = .k} s@(∂→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
  canBeCut {_} {.k} s@(∂→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
  canBeCut {_} {.k} s@(∂→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
  canBeCut {_} {.k} (∂→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
  canBeCut {_} {.k} s@(∂→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
  canBeCut s@(∂→ x) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
  canBeCut (∂→ x) (com {ll = ll} df lf) = (false , ∅)
  canBeCut (∂→ x) (call x₁ lf) = (false , ∅)
  canBeCut (x ←∂→ x₁) I = (false , ∅)
  canBeCut {j = .k} s@(_ ←∂→ _) (_⊂_ {k = k} {ind = ind} lf lf₁) with (isExactHit (contruct s) ind)
  canBeCut {_} {.k} s@(_ ←∂→ _) (_⊂_ {_} {_} {k} {pll} {_} {_} {_} {ind} lf lf₁) | yes ex = canBeCut (truncExSetLL s ind {{prf = ex}}) lf
  canBeCut {_} {.k} s@(_ ←∂→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex with (doesItHitOnce s ind)
  canBeCut {_} {.k} (_ ←∂→ _) (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁) | no ¬ex | (yes ho) = (false , ∅)
  canBeCut {_} {.k} s@(_ ←∂→ _) (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁) | no ¬ex | (no ¬ho) = canBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁
  canBeCut s@(x ←∂→ x₁) (tr {{ltr = ltr}} lf) =  foldl (λ {(false , r) x → canBeCut x lf
                                              ; (true , r) x → (true , r)     }) (false , ∅) (sptran s ltr)
  canBeCut s@(x ←∂→ x₁) (com {ll = ll} df lf) with (contruct s)
  canBeCut (x ←∂→ x₁) (com {ll = ll} df lf) | ↓ = (true , ll)
  canBeCut (x ←∂→ x₁) (com {ll = ll} df lf) | r ←∂ = (false , ∅)
  canBeCut (x ←∂→ x₁) (com {ll = ll} df lf) | ∂→ r = (false , ∅)
  canBeCut (x ←∂→ x₁) (com {ll = ll} df lf) | r ←∂→ r₁ = (false , ∅)
  canBeCut (x ←∂→ x₁) (call x₂ lf) = (false , ∅)

--  posCom : {i : Size} → {j : Size< ↑ i} → ∀{u rll ll} → LFun {u} {i} {j} {rll} {ll} → MSetLL ll
--  posCom I = ∅
--  posCom (x ⊂ x₁) = let e = posCom x
--                    in {!!}
--  posCom (tr x) = {!!}
--  posCom (obs x) = {!!}
--  posCom (com df x) = {!!}
--  posCom (call x x₁) = {!!}
--
-- Remove all of the above.
--  data NextLFun : Set where
--    I    : NextLFun
--    com  : NextLFun
--    call : NextLFun
--  
--  nextLFun : {i : Size} → {j : Size< ↑ i} → ∀{u rll ll} → LFun {u} {i} {j} {rll} {ll} → NextLFun
--  nextLFun I = I
--  nextLFun (lf ⊂ lf₁) = nextLFun lf
--  nextLFun (tr lf) = nextLFun lf
--  nextLFun (obs x) = {!!}
--  nextLFun (com df lf) = com 
--  nextLFun (call x x₁) = call
--
--  notCall : NextLFun → Set
--  notCall I = ⊤
--  notCall com = ⊤
--  notCall call = ⊥
--
-- Is there a com with this specific Linear Logic?

--cutT : ∀{i u rll ll} → {j : Size< i} → LFun {i} {u} {rll} {ll} → LinLogic j {u} × LinLogic j {u}
--cutT {i} {u} {rll} {.rll} {.i} I = (rll , rll)
--cutT {i} {u} {rll} {ll} (_⊂_ {ind = ind} x x₁) = let (crll , cll) = cutT x
--                                   in (crll , replLL ll ind cll)
--cutT {i} {u} {rll} {ll} (tr {orll = orll} x) = (rll , orll)
--cutT {i} {u} {rll} {ll} (com {frll = frll} df x) = (rll , frll)
--cutT {i} {u} {(call ∞rll)} {(call ∞ll)} (call x) = ({!step ∞rll!} , {!!} )
--

module _ where

  open Level
-- cll is the linear logic that is introduced after the last Com.
-- The index points us to the last transformation of the LinLogic, the last place we received data.
-- We need to preserve the ∨(or) choices of the previous inputs.
  mutual
    data Spec :  {i : Size} → {j : Size< i} → ∀{u ll rll} → LinDepT ll → LFun {u} {i} {j} {rll} {ll} → Set where  


--  canBeCut : ∀{i} → {j : Size< ↑ i} → ∀{u rll ll} → SetLL ll → LFun {u} {i} {j} {rll} {ll} → Bool × LinLogic j {u}
    data Input {u} : {i : Size} {j : Size< ↑ i} → ∀{rll ll} →  LinDepT ll → LFun {u} {i} {j} {rll} {ll} → Set (suc u) where
--      I    : {i : Size} {j : Size< ↑ i} → ∀{rll ll ldt lf} → ⦃ prf : nextLFun {i} {j} {u} {rll} {ll} lf ≡ I ⦄ → Input {rll = rll} ldt lf
--      next : {i : Size} {j : Size< ↑ i} → ∀{rll ll ldt lf} → (s : SetLL ll) → let cbc = canBeCut s lf in LinT (proj₂ cbc) → ⦃ prf : nextLFun {i} {j} {u} {rll} {ll} lf ≡ com ⦄ → Input {u} {i} {j} {rll} {ll} ldt lf
--      next : in → Input → Input
--      call : ∞input → Input → Input

--    record ∞Input {i u ll ∞rll} ( ldt : LinDepT ll) ( ∞lf : ∞LFun {i} {u} {∞rll} {ll}) : Set (suc u) where
--      coinductive
--      field
--        step : {j : Size< i} → Input {u} {i = i} {j = j} {rll = step ∞rll} {ll} ldt ((step ∞lf) {j = j})
--


-- As soon as all the inputs of a specific LFun has been received and the resulst is ∅ for all except an embedding, we replace the linear function with that embedding.
