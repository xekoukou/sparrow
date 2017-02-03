-- {-# OPTIONS --show-implicit #-}

module LinFun where

open import Common
open import LinLogic
open import LinDepT
open import LinT 
open import SetLL
open import SetLLProp

open import Data.Bool
open import Data.Unit hiding (_≤_ ; _≤?_)

open import Data.Product
--open import Data.Sum


-- We send to the receiver both the values the type depends and the value of the type. This way, we achieve locality in terms of finding the type of the incoming value.
-- We need to point that the receiver and the sender are the same node.


mutual
  data LFun {u} : {i : Size} → {j : Size< ↑ i} → {rll : LinLogic j {u}} → {ll : LinLogic i {u}} → Set (lsuc u) where
   I   : {i : Size} → ∀{rll} → LFun {u} {i} {_} {rll} {rll}
   _⊂_ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{pll ll ell rll} → {ind : IndexLL {i} pll ll} → (elf : LFun {_} {i} {j} {ell} {pll})
         → {{prf : usesInput elf}} → LFun {_} {j} {k} {rll} {(replLL ll ind ell)}
         → LFun {_} {i} {k} {rll} {ll}
   -- Do we need to set ltr as an instance variable?
   tr  : {i : Size} → {j : Size< ↑ i} → ∀{ll orll rll} → {{ltr : LLTr orll ll}} → LFun {_} {i} {j} {rll} {orll} → LFun {_} {i} {j} {rll} {ll}
   obs : {i : Size} → {j : Size< i} → {k : Size< ↑ j} → ∀{∞ll rll} → LFun {_} {j} {k} {rll} {(step ∞ll)} → LFun {_} {i} {k} {rll} {call ∞ll}
   com : {i : Size} → {j : Size< ↑ i} → ∀{rll ll} → {frll : LinLogic i}
         → ⦃ prfi : onlyOneNilOrNoNilFinite ll ≡ true ⦄ → ⦃ prfo : onlyOneNilOrNoNilFinite frll ≡ true ⦄
         → (df : (ldt : LinDepT ll) → LinT ldt → LinDepT frll) → LFun {rll = rll} {ll = frll}
         → LFun {_} {i} {j} {rll = rll} {ll = ll}
   -- prf guarantees that calls will always contain an input that is not a call. Thus when we remove calls based on previous input availability, only one per call will be removed.
   call : {i : Size} → {k : Size< ↑ i} → ∀{ll ∞rll rll prf} → ∞LFun {i} {_} {∞rll} {ll} {{prf}} → LFun {_} {i} {_} {rll} {call ∞rll} → LFun {_} {i} {k} {rll} {ll}

-- We need to create an observe function, that will unfold all first calls. Then when call is unfolded, the remaining calls generate obs.↑
  record ∞LFun {i : Size} {u} {∞rll : ∞LinLogic i {u}} {ll : LinLogic i {u}} {{prf : notCall ll}} : Set (lsuc u) where
    coinductive
    field
      step : {j : Size< i} → Σ (LFun {_} {j} {j} {(step ∞rll)} {unfold ll}) (λ x → usesInput x)
      
  data usesInputT {i : Size} {j : Size< ↑ i } {u rll ll} (lf : LFun {u} {i} {j} {rll} {ll}) : Set where
    usesInputC : usesInputT` {i} {j} {u} {rll} {ll} lf ∅ → usesInputT {i} {j} {u} {rll} {ll} lf

  data usesInputT` : {i : Size} → {j : Size< ↑ i } → ∀{u rll ll} → LFun {u} {i} {j} {rll} {ll} → MSetLL ll → Set where
    usesInputC`⊂∅ : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{u rll pll ell ll ind elf lf prf} → usesInputT` {j} {k} {u} {rll} {replLL ll ind ell} lf (¬∅ (∅-add ind ell)) → usesInputT` {i} {k} (_⊂_ {u} {i} {j} {k} {pll} {ll} {ell} {rll} {ind} elf {{prf}} lf) ∅
  
  

--  usesInput x = usesInput` x ∅ where
--    usesInput` : {i : Size} → {j : Size< ↑ i} → ∀{u} → {rll : LinLogic j} → {ll : LinLogic i} → LFun {u} {_} {_} {rll} {ll} → MSetLL ll → Set
--    usesInput` I s = ⊥
--    usesInput` (_⊂_ {ell = ell} {ind = ind} elf lf) ∅ = usesInput` lf (¬∅ (∅-add ind ell))
--    usesInput` (_⊂_ {ell = ell} {ind = ↓} elf lf) (¬∅ s) with (contruct $ add s ↓ ell)
--    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
--    usesInput` (elf ⊂ lf) (¬∅ s) | ns =  usesInput` lf (¬∅ ns)
--    usesInput` (_⊂_ {ell = ell} {ind = ind ←∧} elf lf) (¬∅ s) with (contruct $ add s (ind ←∧) ell)
--    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
--    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
--    usesInput` (_⊂_ {ell = ell} {ind = ∧→ ind} elf lf) (¬∅ s) with (contruct $ add s (∧→ ind) ell)
--    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
--    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
--    usesInput` (_⊂_ {ell = ell} {ind = ind ←∨} elf lf) (¬∅ s) with (contruct $ add s (ind ←∨) ell)
--    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
--    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
--    usesInput` (_⊂_ {ell = ell} {ind = ∨→ ind} elf lf) (¬∅ s) with (contruct $ add s (∨→ ind) ell)
--    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
--    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
--    usesInput` (_⊂_ {ell = ell} {ind = ind ←∂} elf lf) (¬∅ s) with (contruct $ add s (ind ←∂) ell)
--    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
--    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
--    usesInput` (_⊂_ {ell = ell} {ind = ∂→ ind} elf lf) (¬∅ s) with (contruct $ add s (∂→ ind) ell)
--    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
--    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
--    usesInput` (tr lf) ∅ = usesInput` lf ∅
--    usesInput` (tr {{ltr = ltr}} lf) (¬∅ s) = usesInput` lf $ ¬∅ (SetLL.tran s ltr)
--    usesInput` (com df lf) s = ⊤
--    usesInput` (call ∞x x) s = ⊥

-- TODO calls in LinLogic need to be excluded from this, thus we need to add-calls in SetLL.
  usesInput : {i : Size} → {j : Size< ↑ i } → ∀{u rll ll} → LFun {u} {i} {j} {rll} {ll} → Set
  usesInput {ll = ll} x = usesInput` x $ fillWithCalls ll where
    usesInput` : {i : Size} → {j : Size< ↑ i} → ∀{u} → {rll : LinLogic j} → {ll : LinLogic i} → LFun {u} {_} {_} {rll} {ll} → MSetLL ll → Set
    usesInput` I s = ⊥
    usesInput` (_⊂_ {ell = ell} {ind = ind} elf lf) ∅ = usesInput` lf (¬∅ (∅-add ind ell))
    usesInput` (_⊂_ {ell = ell} {ind = ↓} elf lf) (¬∅ s) with (contruct $ add s ↓ ell)
    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
    usesInput` (elf ⊂ lf) (¬∅ s) | ns =  usesInput` lf (¬∅ ns)
    usesInput` (_⊂_ {ell = ell} {ind = ind ←∧} elf lf) (¬∅ s) with (contruct $ add s (ind ←∧) ell)
    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
    usesInput` (_⊂_ {ell = ell} {ind = ∧→ ind} elf lf) (¬∅ s) with (contruct $ add s (∧→ ind) ell)
    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
    usesInput` (_⊂_ {ell = ell} {ind = ind ←∨} elf lf) (¬∅ s) with (contruct $ add s (ind ←∨) ell)
    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
    usesInput` (_⊂_ {ell = ell} {ind = ∨→ ind} elf lf) (¬∅ s) with (contruct $ add s (∨→ ind) ell)
    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
    usesInput` (_⊂_ {ell = ell} {ind = ind ←∂} elf lf) (¬∅ s) with (contruct $ add s (ind ←∂) ell)
    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
    usesInput` (_⊂_ {ell = ell} {ind = ∂→ ind} elf lf) (¬∅ s) with (contruct $ add s (∂→ ind) ell)
    usesInput` (elf ⊂ lf) (¬∅ s) | ↓ = ⊤
    usesInput` (elf ⊂ lf) (¬∅ s) | ns = usesInput` lf (¬∅ ns)
    usesInput` (tr lf) ∅ = usesInput` lf ∅
    usesInput` (tr {{ltr = ltr}} lf) (¬∅ s) = usesInput` lf $ ¬∅ (SetLL.tran s ltr)
    -- We should never reach at obs.
    usesInput` (obs x) s = ⊥
    usesInput` (com df lf) s = ⊤
    -- We remove all calls that do not have a dependency other than a call, thus an input derived from a previous com. This means that we should never reach at this position.
    usesInput` (call ∞x x) s = ⊥

open ∞LFun public



module _ where

  open import Data.List
  open import Data.Nat


-- Some simple properties of Natural numbers that are missing from agda-stdlib
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

  fstSp : ∀ {i u ll rll} → (s : SetLL ll) → (ltr : LLTr {i} {u} rll ll) → ⦃ prf : (zero < (length (sptran s ltr))) ⦄ 
          → SetLL rll
  fstSp s ltr {{prf = prf}} with (sptran s ltr)
  fstSp s ltr {{()}} | []
  fstSp s ltr {{prf}} | x ∷ r = x

  sndSp : ∀ {i u ll rll} → (s : SetLL ll) → (ltr : LLTr {i} {u} rll ll) → ⦃ prf : ((suc zero) < (length (sptran s ltr))) ⦄ 
          → SetLL rll
  sndSp s ltr {{prf = prf}} with (sptran s ltr)
  sndSp s ltr {{()}} | []
  sndSp s ltr {{s≤s ()}} | x ∷ []
  sndSp s ltr {{prf}} | x ∷ x₁ ∷ r = x₁

  data cuttable {u} : ∀{i} → {j : Size< ↑ i} → ∀{rll ll} → SetLL ll → LFun {u} {i} {j} {rll} {ll} → Set (lsuc u) where
    cuttable-s-com : {i : Size} → {j : Size< ↑ i} → ∀{rll ll s frll prfi prfo  df lf}
                     → ⦃ prf : res-contruct s ≡ ↓ ⦄
                     → cuttable s (com {u} {i} {j} {rll} {ll} {frll}  ⦃ prfi = prfi ⦄ ⦃ prfo = prfo ⦄ df lf)
    cuttable-s⊂-oi : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{ll rll ell pll s ind lf prf lf₁}
                     → ⦃ oi : onlyInside s ind ⦄
                     → cuttable (truncOISetLL s ind) lf
                     → cuttable s (_⊂_ {u} {i} {j} {k} {pll} {ll} {ell} {rll} {ind} lf ⦃ prf ⦄ lf₁)
    cuttable-s⊂-¬ho : {i : Size} → {j : Size< ↑ i} → {k : Size< ↑ j} → ∀{ll rll pll ell s ind lf prf lf₁}
                     → ⦃ ¬ho : ¬ (hitsAtLeastOnce s ind) ⦄
                     → cuttable (replSetLL s ind {{prf = ¬ho }} ell) lf₁
                     → cuttable s (_⊂_ {u} {i} {j} {k} {pll} {ll} {ell} {rll} {ind} lf ⦃ prf ⦄ lf₁)
    cuttable-s-tr-fst : {i : Size} → {j : Size< ↑ i} → ∀{ll orll rll lf s ltr prftr}
                        → cuttable (fstSp s ltr ⦃ prf = prftr ⦄) lf
                        → cuttable s (tr {u} {i} {j} {ll} {orll} {rll} ⦃ ltr ⦄ lf)
    cuttable-s-tr-snd : {i : Size} → {j : Size< ↑ i} → ∀{ll orll rll lf s ltr prftr}
                        → cuttable (sndSp s ltr ⦃ prf = prftr ⦄) lf
                        → cuttable s (tr {u} {i} {j} {ll} {orll} {rll} ⦃ ltr ⦄ lf)


-- TODO This requires that the SetLL is precise. We might need it to also be a superset of a solution.
  canItBeCut : ∀{i} → {j : Size< ↑ i} → ∀{u rll ll} → (s : SetLL ll) → (lf : LFun {u} {i} {j} {rll} {ll}) → Dec (cuttable s lf)
  canItBeCut s I = no (λ ())
  canItBeCut s (_⊂_ {ind = ind} lf lf₁) with (isOnlyInside s ind)
  canItBeCut s (_⊂_ {ind = ind} lf lf₁) | yes oi with (canItBeCut (truncOISetLL s ind {{prf = oi}}) lf)
  canItBeCut s (lf ⊂ lf₁) | yes oi | (yes p) = yes (cuttable-s⊂-oi p)
  canItBeCut s (_⊂_ {ind = ind} lf lf₁) | yes oi | (no ¬p) = no (λ x → helpFunOi x oi ¬p) where
    helpFunOi : cuttable s (_⊂_ {ind = ind} lf lf₁)
                → (oi : onlyInside s ind)
                → ¬ (cuttable (truncOISetLL s ind {{prf = oi}})) lf
                → ⊥
    helpFunOi (cuttable-s⊂-oi {{oi = oi}} ct) ex₁ ¬p with (onlyInsideUnique s ind oi ex₁)
    helpFunOi (cuttable-s⊂-oi {{oi = .ex₁}} ct) ex₁ ¬p | refl = ¬p ct
    helpFunOi (cuttable-s⊂-¬ho {s = s} {ind = ind} {{¬ho = ¬ho}} ct) oi ¬p = onlyInside¬hitsAtLeastOnce→⊥ s ind oi ¬ho
  canItBeCut s (_⊂_ {ind = ind} lf lf₁)    | no ¬oi with (doesItHitAtLeastOnce s ind)
  canItBeCut s (lf ⊂ lf₁)    | no ¬oi | (yes ho) = no (λ { (cuttable-s⊂-oi {{oi = oi}}   ct) → ¬oi oi 
                                                                                                      ; (cuttable-s⊂-¬ho {{¬ho = ¬ho}} ct) → ¬ho ho     })
  canItBeCut s (_⊂_ {ell = ell} {ind = ind} lf lf₁)  | no ¬oi | (no ¬ho) with (canItBeCut (replSetLL s ind {{prf = ¬ho }} ell) lf₁)
  canItBeCut s (lf ⊂ lf₁)    | no ¬oi | (no ¬ho) | (yes p) = yes (cuttable-s⊂-¬ho ⦃ ¬ho = ¬ho ⦄ p)
  canItBeCut s (lf ⊂ lf₁)    | no ¬oi | (no ¬ho) | (no ¬p) = no (λ x → helpFunho x) where
    helpFunho : cuttable s (lf ⊂ lf₁)
                → ⊥
    helpFunho (cuttable-s⊂-oi {{oi = oi}} x) = ¬oi oi
    helpFunho (cuttable-s⊂-¬ho {{¬ho = ¬ho₁}} x) = ¬p x
  canItBeCut s (tr {{ltr = ltr}} lf) with (( suc zero) ≤? length (sptran s ltr))
  canItBeCut s (tr {{ltr = ltr}} lf) | yes p with (canItBeCut (fstSp s ltr ⦃ prf = p ⦄) lf)
  canItBeCut s (tr {{ltr = ltr}} lf) | yes p | (yes p₁) = yes (cuttable-s-tr-fst {prftr = p} p₁)
  canItBeCut s (tr {{ltr = ltr}} lf) | yes p | (no ¬p) with (( suc $ suc zero) ≤? length (sptran s ltr))
  canItBeCut s (tr {{ltr = ltr}} lf) | yes p₁ | (no ¬p) | (yes p) with (canItBeCut (sndSp s ltr ⦃ prf = p ⦄) lf)
  canItBeCut s (tr {{ltr = ltr}} lf) | yes p₂ | (no ¬p) | (yes p) | (yes p₁) = yes (cuttable-s-tr-snd p₁)
  canItBeCut s (tr {{ltr = ltr}} lf) | yes p₁ | (no ¬p₁) | (yes p) | (no ¬p) = no hf where
    hf : cuttable s (tr {{ltr = ltr}} lf) → ⊥
    hf (cuttable-s-tr-fst x) = ¬p₁ x
    hf (cuttable-s-tr-snd {prftr = prftr} x) with (prftr ≤un p)
    hf (cuttable-s-tr-snd x) | refl = ¬p x
  canItBeCut s (tr {{ltr = ltr}} lf) | yes p | (no ¬p₁) | (no ¬p) = no hf where
    hf : cuttable s (tr {{ltr = ltr}} lf) → ⊥
    hf (cuttable-s-tr-fst x) = ¬p₁ x
    hf (cuttable-s-tr-snd {prftr = prftr} x) = ¬p prftr
  canItBeCut s (tr {{ltr = ltr}} lf) | no ¬p = no hf where
    hf : cuttable s (tr {{ltr = ltr}} lf) → ⊥
    hf (cuttable-s-tr-fst {prftr = prftr} x) = ¬p prftr
    hf (cuttable-s-tr-snd {prftr = prftr} x) = ¬p ( ≤-pred $ ≤rsuc prftr)
  canItBeCut s (obs lf) = no (λ ())
  canItBeCut s (com df lf) with (isEq (res-contruct s) ↓)
  canItBeCut s (com df lf) | yes p = yes (cuttable-s-com {s = s} {{ prf = p }})
  canItBeCut s (com df lf) | no ¬p = no hf where
    hf : cuttable s (com df lf) → ⊥
    hf (cuttable-s-com {{prf = prf}}) = ¬p prf
  canItBeCut s (call x lf) = no (λ ())

-- Important : We need to introduce a null data point like Unit, that serves to express the dependency between events. 
-- We prohibit LFun Calls that do not depend on a previous com.

-- We remove all the calls that do not have input dependencies and replace them with their respective LFun.
-- We add obs to all the other calls that did not trigger the unfolding and then an embedding of the LFun with ⊂. We use the "usesInput" that is created by step.

-- By removing the calls , the usesInput of the main function is preserved.
-- We also unfold all calls that depend on the call of this call. These are finite by definition of LFun (being inductive data type).

  mutual
    -- We use this when we compute the next LFun and the next output, thus the size is allowed to be lowered by one.
    removeCall : {i : Size} → {j : Size< i}  → {k : Size< ↑ i} → ∀{u rll ll} → LFun {u} {i} {k} {rll} {ll} → LFun {u} {i} {k} {rll} {ll}
    removeCall I = I
    removeCall (_⊂_ {ind = ind} lf {{prf = prf}} lf₁) = {!!} -- _⊂_ {ind = ind} (removeCall lf) {{prf = prf}} (removeCall lf₁)  -- We need to only remove call that do not depend on a previous com.
    removeCall (tr lf) = tr $ removeCall lf
    removeCall (obs lf) = {!!}
    removeCall (com df lf) = com df $ lf
    removeCall (call ∞lf lf₁) = {!!} -- let st = step ∞lf in
      {!!} -- _⊂_ {ind = ↓} (proj₁ st) {{prf = proj₂ st}} (removeCall lf₁) 

    usesInput→usesInput$removeCall : {i : Size} → {j : Size< i } → {k : Size< ↑ i} → ∀{u rll ll} → (lf : LFun {u} {i} {k} {rll} {ll}) → usesInput lf ≡ ⊤ → usesInput (removeCall lf) ≡ ⊤
    usesInput→usesInput$removeCall I prf = prf
    usesInput→usesInput$removeCall (lf ⊂ lf₁) prf = {!!}
    usesInput→usesInput$removeCall (tr lf) prf = {!!}
    usesInput→usesInput$removeCall (obs lf) prf = {!!}
    usesInput→usesInput$removeCall (com df lf) prf = {!!}
    usesInput→usesInput$removeCall (call x lf) prf = {!!}
    





--  cut : ∀{i u} → {j : Size< ↑ i} → ∀{rll ll} → {s : SetLL ll} → {lf : LFun} → cuttable {u} {i} {j} {rll} s lf
--  cut c = {!!}








module _ where

-- cll is the linear logic that is introduced after the last Com.
-- The indoi points us to the last transformation of the LinLogic, the last place we received data.
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
