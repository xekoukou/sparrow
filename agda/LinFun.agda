{-# OPTIONS --exact-split #-}
--{-# OPTIONS --show-implicit #-}

module LinFun where

open import Common
open import LinLogic
open import LinDepT
open import LinT 
open import SetLL
open import SetLLProp

open import Size
open import Function
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit hiding (_≤_ ; _≤?_)
open import Relation.Nullary



-- We send to the receiver both the values the type depends and the value of the type. This way, we achieve locality in terms of finding the type of the incoming value.
-- We need to point that the receiver and the sender are the same node.

module _ where

  mutual
    data LFun {u} : {i : Size} → {j : Size< ↑ i} → {rll : LinLogic j {u}} → {ll : LinLogic i {u}} → Set (lsuc u) where
     I   : {i : Size} → ∀{rll} → LFun {u} {i} {_} {rll} {rll}
     _⊂_ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{pll ll ell rll} → {ind : IndexLL {i} pll ll} → (elf : LFun {_} {i} {j} {ell} {pll})
           → {{prf : usesInput elf}} → LFun {_} {j} {k} {rll} {(replLL ll ind ell)}
           → LFun {_} {i} {k} {rll} {ll}
     --Do we need to set ltr as an instance variable?
     tr  : {i : Size} → {j : Size< ↑ i} → ∀{ll orll rll} → {{ltr : LLTr orll ll}} → LFun {_} {i} {j} {rll} {orll} → LFun {_} {i} {j} {rll} {ll}
     obs : {i : Size} → {j : Size< i} → {k : Size< ↑ j} → ∀{∞ll rll} → LFun {_} {j} {k} {rll} {(step ∞ll)} → LFun {_} {i} {k} {rll} {call ∞ll}
     com : {i : Size} → {j : Size< ↑ i} → ∀{rll ll} → {frll : LinLogic i}
           → ⦃ prfi : onlyOneNilOrNoNilFinite ll ≡ true ⦄ → ⦃ prfo : onlyOneNilOrNoNilFinite frll ≡ true ⦄
           → (df : (ldt : LinDepT ll) → LinT ldt → LinDepT frll) → LFun {rll = rll} {ll = frll}
           → LFun {_} {i} {j} {rll = rll} {ll = ll}
     call : {i : Size} → {j : Size< i} → ∀{ll ∞rll rll} → ∞LFun {i} {_} {∞rll} {ll} → LFun {_} {i} {j} {rll} {call ∞rll} → LFun {_} {i} {j} {rll} {ll}
  
  
    record ∞LFun {i : Size} {u} {∞rll : ∞LinLogic i {u}} {ll : LinLogic i {u}} : Set (lsuc u) where
      coinductive
      field
        step : {j : Size< i} → LFun {_} {i} {j} {(step ∞rll)} {ll}


    usesInput : {i : Size} → {j : Size< ↑ i } → ∀{u rll ll} → LFun {u} {i} {j} {rll} {ll} → Set
    usesInput x = usesInput` x ∅ where
      usesInput` : {i : Size} → {j : Size< ↑ i} → ∀{u} → {rll : LinLogic j} → {ll : LinLogic i} → LFun {u} {_} {_} {rll} {ll} → MSetLL ll → Set
      usesInput` I s = ⊥
      usesInput` (_⊂_ {j = j} {k = k} {ell = ell} {ind = ind} elf lf) ∅ = usesInput` lf (¬∅ (∅-add ind ell))
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ↓} elf lf) (¬∅ s) with (contruct $ add {i = i} {j = j} s ↓ ell)
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ↓} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {.(_ LinLogic.∧ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∧ =  usesInput` lf (¬∅ (ns ←∧))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {.(_ LinLogic.∧ _)} {_} {↓} elf lf) (¬∅ s) | ∧→ ns =  usesInput` lf (¬∅ (∧→ ns))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {.(_ LinLogic.∧ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∧→ ns₁ =  usesInput` lf (¬∅ (ns ←∧→ ns₁))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {.(_ LinLogic.∨ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∨ =  usesInput` lf (¬∅ (ns ←∨))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {.(_ LinLogic.∨ _)} {_} {↓} elf lf) (¬∅ s) | ∨→ ns =  usesInput` lf (¬∅ (∨→ ns))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {.(_ LinLogic.∨ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∨→ ns₁ =  usesInput` lf (¬∅ (ns ←∨→ ns₁))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {.(_∂_ _ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∂ =  usesInput` lf (¬∅ (ns ←∂))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {.(_∂_ _ _)} {_} {↓} elf lf) (¬∅ s) | ∂→ ns =  usesInput` lf (¬∅ (∂→ ns))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {.(_∂_ _ _)} {_} {↓} elf lf) (¬∅ s) | ns ←∂→ ns₁ =  usesInput` lf (¬∅ (ns ←∂→ ns₁))
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∧} elf lf) (¬∅ s) with (contruct $ add s (ind ←∧) ell)
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∧} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∧} elf lf) (¬∅ s) | ns ←∧ = usesInput` lf (¬∅ (ns ←∧))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∧} elf lf) (¬∅ s) | ∧→ ns = usesInput` lf (¬∅ (∧→ ns))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∧} elf lf) (¬∅ s) | ns ←∧→ ns₁ = usesInput` lf (¬∅ (ns ←∧→ ns₁))
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∧→ ind} elf lf) (¬∅ s) with (contruct $ add s (∧→ ind) ell)
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∧→ ind} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∧→ ind} elf lf) (¬∅ s) | ns ←∧ = usesInput` lf (¬∅ (ns ←∧))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∧→ ind} elf lf) (¬∅ s) | ∧→ ns = usesInput` lf (¬∅ (∧→ ns))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∧→ ind} elf lf) (¬∅ s) | ns ←∧→ ns₁ = usesInput` lf (¬∅ (ns ←∧→ ns₁))
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∨} elf lf) (¬∅ s) with (contruct $ add s (ind ←∨) ell)
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∨} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∨} elf lf) (¬∅ s) | ns ←∨ = usesInput` lf (¬∅ (ns ←∨))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∨} elf lf) (¬∅ s) | ∨→ ns = usesInput` lf (¬∅ (∨→ ns))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∨} elf lf) (¬∅ s) | ns ←∨→ ns₁ = usesInput` lf (¬∅ (ns ←∨→ ns₁))
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∨→ ind} elf lf) (¬∅ s) with (contruct $ add s (∨→ ind) ell)
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∨→ ind} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∨→ ind} elf lf) (¬∅ s) | ns ←∨ = usesInput` lf (¬∅ (ns ←∨))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∨→ ind} elf lf) (¬∅ s) | ∨→ ns = usesInput` lf (¬∅ (∨→ ns))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∨→ ind} elf lf) (¬∅ s) | ns ←∨→ ns₁ = usesInput` lf (¬∅ (ns ←∨→ ns₁))
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ind ←∂} elf lf) (¬∅ s) with (contruct $ add s (ind ←∂) ell)
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∂} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∂} elf lf) (¬∅ s) | ns ←∂ = usesInput` lf (¬∅ (ns ←∂))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∂} elf lf) (¬∅ s) | ∂→ ns = usesInput` lf (¬∅ (∂→ ns))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {ind ←∂} elf lf) (¬∅ s) | ns ←∂→ ns₁ = usesInput` lf (¬∅ (ns ←∂→ ns₁))
      usesInput` {i = i} {j = .k} (_⊂_ {i = .i} {j = j} {k = k} {ell = ell} {rll = rll} {ind = ∂→ ind} elf lf) (¬∅ s) with (contruct $ add s (∂→ ind) ell)
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∂→ ind} elf lf) (¬∅ s) | ↓ = ⊤
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∂→ ind} elf lf) (¬∅ s) | ns ←∂ = usesInput` lf (¬∅ (ns ←∂))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∂→ ind} elf lf) (¬∅ s) | ∂→ ns = usesInput` lf (¬∅ (∂→ ns))
      usesInput` {i} {.k} (_⊂_ {.i} {j} {k} {_} {_} {ell} {_} {∂→ ind} elf lf) (¬∅ s) | ns ←∂→ ns₁ = usesInput` lf (¬∅ (ns ←∂→ ns₁))
      usesInput` (tr lf) ∅ = usesInput` lf ∅
      usesInput` (tr {{ltr = ltr}} lf) (¬∅ s) = usesInput` lf $ ¬∅ (SetLL.tran s ltr)
      usesInput` (obs {j = lj} {k = lk} {∞ll = ∞ll} x) s = usesInput` {i = lj} {j = lk} x (∅ {ll = (step ∞ll)})
      usesInput` (com df lf) s = ⊤
      usesInput` (call ∞x x) s = ⊥

open ∞LFun public



module _ where

  open import Data.List
  open import Data.Nat


  module _ where

    _≤un_ : {a : ℕ} → {b : ℕ} → (c : (a ≤ b)) → (d : (a ≤ b)) → c ≡ d  
    z≤n ≤un z≤n = refl
    s≤s c ≤un s≤s d with ( c ≤un d )
    s≤s c ≤un s≤s .c | refl = refl

    ≤rsuc : {a : ℕ} → {b : ℕ} → (a ≤ b) → a ≤ suc b
    ≤rsuc z≤n = z≤n
    ≤rsuc (s≤s x) = s≤s $ ≤rsuc x




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

  data cuttable {u} : ∀{i} → {j : Size< ↑ i} → ∀{rll ll} → SetLL ll → LFun {u} {i} {j} {rll} {ll} → Set (lsuc u) where
    cuttable-s-com : {i : Size} → {j : Size< ↑ i} → ∀{rll ll s frll prfi prfo  df lf}
                     → ⦃ prf : contruct s ≡ ↓ ⦄
                     → cuttable {u = u} {i = i} {j = j} s (com {rll = rll} {ll = ll} {frll = frll}  ⦃ prfi = prfi ⦄ ⦃ prfo = prfo ⦄ df lf)
    cuttable-s⊂-ex : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{ll rll ell pll s ind lf prf lf₁}
                     → ⦃ ex : onlyInside s ind ⦄
                     → cuttable {rll = ell} {ll = pll} (truncOISetLL {pll = pll} s ind {{prf = ex}}) lf
                     → cuttable {i = i} {j = k} {rll = rll} {ll = ll} s (_⊂_ {i = i} {j = j} {k = k} {pll = pll} {ll = ll} {ell = ell} {ind = ind} lf ⦃ prf = prf ⦄ lf₁)
    cuttable-s⊂-ho : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{ll rll pll ell s ind lf prf lf₁}
                     → ⦃ ¬ho : ¬ (hitsAtLeastOnce {ll = ll} {rll = pll} s ind) ⦄
                     → cuttable {rll = rll} (replSetLL s ind {{prf = ¬ho }} ell) lf₁
                     → cuttable {i = i} {j = k} {rll = rll} {ll = ll} s (_⊂_ {i = i} {j = j} {k = k} {pll = pll} {ll = ll} {ell = ell} {ind = ind} lf ⦃ prf = prf ⦄ lf₁)
    cuttable-s-tr-fst : {i : Size} → {j : Size< ↑ i} → ∀{ll orll rll lf s ltr prftr}
                        → cuttable {i = i} {j = j} {rll = rll} {ll = orll} (fstSp s ltr ⦃ prf = prftr ⦄) lf
                        → cuttable {i = i} {j = j} s (tr {ll = ll} {orll = orll} {rll = rll} ⦃ ltr = ltr ⦄ lf)
    cuttable-s-tr-snd : {i : Size} → {j : Size< ↑ i} → ∀{ll orll rll lf s ltr prftr}
                        → cuttable {i = i} {j = j} {rll = rll} {ll = orll} (sndSp s ltr ⦃ prf = prftr ⦄) lf
                        → cuttable {i = i} {j = j} s (tr {ll = ll} {orll = orll} {rll = rll} ⦃ ltr = ltr ⦄ lf)


  canItBeCut : ∀{i} → {j : Size< ↑ i} → ∀{u rll ll} → (s : SetLL ll) → (lf : LFun {u} {i} {j} {rll} {ll}) → Dec (cuttable {i = i} {j = j} {rll = rll} {ll = ll} s lf)
  canItBeCut s I = no (λ ())
  canItBeCut {.i} {.k} {u} {_} {_} s (_⊂_ {i} {j} {k} {pll} {ll} {ell} {_} {ind} lf lf₁) with (isOnlyInside {ll = ll} {rll = pll} s ind)
  canItBeCut {.i} {.k} {u} {_} {_} s (_⊂_ {i} {j} {k} {pll} {ll} {ell} {_} {ind} lf lf₁) | yes ex with (canItBeCut {rll = ell} {ll = pll} (truncOISetLL {pll = pll} s ind {{prf = ex}}) lf)
  canItBeCut {.i} {.k} {u} {_} {_} s (_⊂_ {i} {j} {k} {pll} {ll} {ell} {_} {ind} lf lf₁) | yes ex | (yes p) = yes (cuttable-s⊂-ex {i = i} {j = j} {k = k} ⦃ ex = ex ⦄ p)
  canItBeCut {.i} {.k} {u} {_} {_} s (_⊂_ {i} {j} {k} {pll} {ll} {ell} {_} {ind} lf lf₁) | yes ex | (no ¬p) = no (λ x → helpFunEx x ex ¬p) where
    helpFunEx : cuttable {u = u} s (_⊂_ {i = i} {j = j} {k = k} {pll = pll} {ll = ll} {ell = ell} {ind = ind} lf lf₁)
                → (ex : onlyInside {i} s ind)
                → ¬ (cuttable {u} {i} {j} {ell} {pll} (truncOISetLL {pll = pll} s ind {{prf = ex}})) lf
                → ⊥
    helpFunEx (cuttable-s⊂-ex {{ex = ex}} ct) ex₁ ¬p with (onlyInsideUnique s ind ex ex₁)
    helpFunEx (cuttable-s⊂-ex {{ex = .ex₁}} ct) ex₁ ¬p | refl = ¬p ct
    helpFunEx (cuttable-s⊂-ho {s = s} {ind = ind} {{¬ho = ¬ho}} ct) ex ¬p = onlyInside¬hitsAtLeastOnce→⊥ s ind ex ¬ho
  canItBeCut {_} {.k} s (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁)    | no ¬ex with (doesItHitAtLeastOnce s ind)
  canItBeCut {_} {.k} s (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁)    | no ¬ex | (yes ho) = no (λ { (cuttable-s⊂-ex {{ex = ex}}   ct) → ¬ex ex
                                                                                                      ; (cuttable-s⊂-ho {{¬ho = ¬ho}} ct) → ¬ho ho     })
  canItBeCut {_} {.k} s (_⊂_ {_} {_} {k} {_} {_} {ell} {_} {ind} lf lf₁)  | no ¬ex | (no ¬ho) with (canItBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁)
  canItBeCut {_} {.k} s (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁)    | no ¬ex | (no ¬ho) | (yes p) = yes (cuttable-s⊂-ho ⦃ ¬ho = ¬ho ⦄ p)
  canItBeCut {_} {.k} s (_⊂_ {_} {_} {k} {_} {_} {_} {_} {ind} lf lf₁)    | no ¬ex | (no ¬ho) | (no ¬p) = no (λ x → helpFunho x) where
    helpFunho : cuttable s (_⊂_ lf lf₁)
                → ⊥
    helpFunho (cuttable-s⊂-ex {{ex = ex}} x) = ¬ex ex
    helpFunho (cuttable-s⊂-ho {{¬ho = ¬ho₁}} x) = ¬p x
  canItBeCut s (tr {{ltr = ltr}} lf) with (( suc zero) ≤? length (sptran s ltr))
  canItBeCut s (tr {_} {_} {_} {_} {_} {{ltr}} lf) | yes p with (canItBeCut (fstSp s ltr ⦃ prf = p ⦄) lf)
  canItBeCut s (tr {_} {_} {_} {_} {_} {{ltr}} lf) | yes p | (yes p₁) = yes (cuttable-s-tr-fst {prftr = p} p₁)
  canItBeCut s (tr {_} {_} {_} {_} {_} {{ltr}} lf) | yes p | (no ¬p) with (( suc $ suc zero) ≤? length (sptran s ltr))
  canItBeCut s (tr {_} {_} {_} {_} {_} {{ltr}} lf) | yes p₁ | (no ¬p) | (yes p) with (canItBeCut (sndSp s ltr ⦃ prf = p ⦄) lf)
  canItBeCut s (tr {_} {_} {_} {_} {_} {{ltr}} lf) | yes p₂ | (no ¬p) | (yes p) | (yes p₁) = yes (cuttable-s-tr-snd p₁)
  canItBeCut s (tr {_} {_} {_} {_} {_} {{ltr}} lf) | yes p₁ | (no ¬p₁) | (yes p) | (no ¬p) = no hf where
    hf : cuttable s (tr {{ltr = ltr}} lf) → ⊥
    hf (cuttable-s-tr-fst x) = ¬p₁ x
    hf (cuttable-s-tr-snd {prftr = prftr} x) with (prftr ≤un p)
    hf (cuttable-s-tr-snd {_} {_} {_} {_} {_} {_} {_} {_} {_} x) | refl = ¬p x
  canItBeCut s (tr {_} {_} {_} {_} {_} {{ltr}} lf) | yes p | (no ¬p₁) | (no ¬p) = no hf where
    hf : cuttable s (tr {{ltr = ltr}} lf) → ⊥
    hf (cuttable-s-tr-fst x) = ¬p₁ x
    hf (cuttable-s-tr-snd {prftr = prftr} x) = ¬p prftr
  canItBeCut s (tr {_} {_} {_} {_} {_} {{ltr}} lf) | no ¬p = no hf where
    hf : cuttable s (tr {{ltr = ltr}} lf) → ⊥
    hf (cuttable-s-tr-fst {prftr = prftr} x) = ¬p prftr
    hf (cuttable-s-tr-snd {prftr = prftr} x) = ¬p ( ≤-pred $ ≤rsuc prftr)
  canItBeCut s (obs lf) = no (λ ())
  canItBeCut s (com df lf) with (isEq (contruct s) ↓)
  canItBeCut s (com df lf) | yes p = yes (cuttable-s-com {s = s} {{ prf = p }})
  canItBeCut s (com df lf) | no ¬p = no hf where
    hf : cuttable s (com df lf) → ⊥
    hf (cuttable-s-com {{prf = prf}}) = ¬p prf
  canItBeCut s (call x lf) = no (λ ())



module _ where

-- cll is the linear logic that is introduced after the last Com.
-- The index points us to the last transformation of the LinLogic, the last place we received data.
-- We need to preserve the ∨(or) choices of the previous inputs.
  mutual
    data Spec :  {i : Size} → {j : Size< i} → ∀{u ll rll} → LinDepT ll → LFun {u} {i} {j} {rll} {ll} → Set where  


--  canBeCut : ∀{i} → {j : Size< ↑ i} → ∀{u rll ll} → SetLL ll → LFun {u} {i} {j} {rll} {ll} → Bool × LinLogic j {u}
    data Input {u} : {i : Size} {j : Size< ↑ i} → ∀{rll ll} →  LinDepT ll → LFun {u} {i} {j} {rll} {ll} → Set (lsuc u) where
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
