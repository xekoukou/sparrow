{-# OPTIONS --exact-split #-}
module IndexLFCo where

open import Common
open import LinLogic
open import LinLogicProp
open import LinFun
open import IndexLLProp
open import Data.Maybe

module _ where

  open import Relation.Binary.PropositionalEquality
--  open  Relation.Binary.PropositionalEquality.Deprecated-inspect




  -- reverseTran returns nothing if during the reversion, it finds a com.
  -- or if the cll is transformed.
  


  mutual
    data ReverseTranT {i u} : ∀{ll cll rll} → LFun ll rll
                              → IndexLL {i} {u} cll rll → Set (lsuc u) where
      cr1 : ∀{cll rll} → {iind : IndexLL {i} {u} cll rll} → ReverseTranT I iind
      cr2 : ∀{ll cll rll ell pll ind lf₁ lf} → {iind : IndexLL {i} {u} cll rll}
            → (rvT₁ : ReverseTranT lf₁ iind)
            → let x = reverseTran lf₁ iind rvT₁ ; uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind) in
              (ltuindx : uind ≤ᵢ x)
            → let x₁ = ((x -ᵢ uind) ltuindx) in
              (rvT₂ : ReverseTranT lf (ind-rpl↓ ind x₁)) 
            → ReverseTranT (_⊂_ {pll = pll} {ll = ll} {ell = ell} {rll = rll} {ind = ind} lf lf₁) iind
      cr3 : ∀{ll cll rll ell pll ind lf₁ lf} → {iind : IndexLL {i} {u} cll rll}
            → (rvT₁ : ReverseTranT lf₁ iind)
            → let x = reverseTran lf₁ iind rvT₁ ; uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind) in
              (nord : ¬ Orderedᵢ x uind)
            → ReverseTranT (_⊂_ {pll = pll} {ll = ll} {ell = ell} {rll = rll} {ind = ind} lf lf₁) iind
      cr4 : ∀{ll cll orll rll lf} → {ltr : LLTr orll ll} → {iind : IndexLL {i} {u} cll rll}
            → (rvT₁ : ReverseTranT lf iind) → UpTran (reverseTran lf iind rvT₁) (revTr ltr)
            → ReverseTranT (tr ltr lf) iind



    -- reverseTran returns nothing if during the reversion, it finds a com.
    -- or if the cll is transformed.
  
    reverseTran : ∀{i u ll cll rll} → (lf : LFun ll rll) → (iind : IndexLL {i} {u} cll rll)
                  → ReverseTranT lf iind → IndexLL cll ll
    reverseTran .I iind cr1 = iind
    reverseTran (_⊂_ {pll = pll} {ell = ell} {ind = ind} lf lf₁) iind (cr2 rvT₁ ltuindx rvT₂)
      = ind +ᵢ reverseTran lf (ind-rpl↓ ind x₁) rvT₂ where
      uind = (a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind))
      x = reverseTran lf₁ iind rvT₁
      x₁ = ((x -ᵢ uind) ltuindx)
    reverseTran (_⊂_ {ell = ell} {ind = ind} _ lf₁) iind (cr3 rvT₁ nord)
      =  lemma₁-¬ord-a≤ᵢb ind ind ell (≤ᵢ-reflexive ind) (reverseTran lf₁ iind rvT₁) (flipNotOrdᵢ nord)
    reverseTran (tr ltr lf) iind (cr4 pr ut) = tran (reverseTran lf iind pr) (revTr ltr) ut




    rT-morph : ∀{i u ll cll rll} → ∀ frll → (lf : LFun ll rll) → (iind : IndexLL {i} {u} cll rll)
               → (rvT : ReverseTranT lf iind) → LFun (replLL ll (reverseTran lf iind rvT) frll) (replLL rll iind frll)
    rT-morph frll .I iind cr1 = I
    rT-morph {ll = ll} {rll = rll} frll (_⊂_ {pll = pll} {ell = ell} {ind = ind} lf lf₁) iind (cr2 rvT₁ ltuindx rvT₂) = res (w hf) where 
      t = (replLL pll ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) ell)
      eq = (replLL-↓ {ell = ell} ind)

      uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind)

      x = reverseTran lf₁ iind rvT₁

-- eq transforms x₁
      x₁ = ind-rpl↓ ind ((x -ᵢ uind) ltuindx)


      rtm₁ = rT-morph frll lf₁ iind rvT₁

      
-- eq is needed
      x₂ = reverseTran lf x₁ rvT₂
      t₂ = ((ind +ᵢ x₂) -ᵢ ind) (+ᵢ⇒l≤ᵢ+ᵢ ind x₂)
      eq₂ = [a+b]-a=b ind x₂
      rind = a≤ᵢb-morph ind (ind +ᵢ x₂) frll (+ᵢ⇒l≤ᵢ+ᵢ ind x₂)

-- eq2 changes rind
      urind = subst (λ x → IndexLL (replLL pll x frll) (replLL ll (ind +ᵢ x₂) frll)) eq₂ rind

-- Here we need the original rind
      t₃ = replLL (replLL ll (ind +ᵢ x₂) frll) rind (replLL ell x₁ frll)
      eq₃ = replLL-a≤b≡a ind (replLL ell x₁ frll) (ind +ᵢ x₂) frll (+ᵢ⇒l≤ᵢ+ᵢ ind x₂)
      hf : LFun
             (replLL
               (replLL ll (ind +ᵢ x₂) frll)
               rind (replLL ell x₁ frll))
             (replLL rll iind frll)
      hf = subst (λ x₃ → x₃)
             (sym
              (trans (cong (λ x₃ → LFun x₃ (replLL rll iind frll)) eq₃)
               (cong (λ x₃ → LFun x₃ (replLL rll iind frll))
                (repl-r=>l ell ind x ltuindx))))
             rtm₁
      rtm₂ = rT-morph frll lf x₁ rvT₂

      res : LFun
             (replLL
               (replLL ll (ind +ᵢ x₂) frll)
               urind (replLL ell x₁ frll))
             (replLL rll iind frll) → LFun (replLL ll (ind +ᵢ x₂) frll) (replLL rll iind frll) 
      res x = _⊂_ {ind = urind} rtm₂ x
      w : LFun
            (replLL
              (replLL ll (ind +ᵢ x₂) frll)
              rind (replLL ell x₁ frll))
            (replLL rll iind frll) → 
          LFun
            (replLL
              (replLL ll (ind +ᵢ x₂) frll)
              urind (replLL ell x₁ frll))
            (replLL rll iind frll) 
      w x with t₂ | eq₂ | rind where
      ... | t2 | refl | rind = x
    rT-morph {ll = ll} {rll = rll} frll (_⊂_ {ell = ell} {ind = ind} lf lf₁) iind (cr3 rvT₁ nord) = _⊂_ {ind = rind} lf nn where
      n = rT-morph frll lf₁ iind rvT₁
      x = reverseTran lf₁ iind rvT₁
      lind = lemma₁-¬ord-a≤ᵢb ind ind ell (≤ᵢ-reflexive ind) x (flipNotOrdᵢ nord)
      lnord = rlemma₁⇒¬ord ind ind ell (≤ᵢ-reflexive ind) x (flipNotOrdᵢ nord)
      rind = ¬ord-morph ind lind frll (flipNotOrdᵢ lnord)
      b = ¬ord-morph$lemma₁≡I ell ind ind (≤ᵢ-reflexive ind) x nord
      nn = subst (λ x → LFun x (replLL rll iind frll)) (trans (sym (cong (λ x → replLL (replLL ll ind ell) x frll) b )) (replLL-¬ordab≡ba lind frll ind ell lnord)) n
    rT-morph frll (tr ltr lf) iind (cr4 rvT x) = tr (revTr (tr-ltr-morph frll lind (revTr ltr) x)) n where
      lind = reverseTran lf iind rvT
      n = rT-morph frll lf iind rvT







  getReverseTranT : ∀{i u ll cll rll} → (lf : LFun ll rll) → (iind : IndexLL {i} {u} cll rll)
                    → Maybe (ReverseTranT lf iind)
  getReverseTranT I iind = just cr1
  getReverseTranT (_⊂_ {ell = ell} {ind = ind} lf lf₁) iind with (getReverseTranT lf₁ iind)
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind | just rvT₁ with (isLTi uind x) where
    x = (reverseTran lf₁ iind rvT₁)
    uind = (a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind))
  getReverseTranT {i} {u} {cll = cll} (_⊂_ {pll} {_} {ell} {_} {ind} lf lf₁) iind
    | just rvT₁ | (yes ltuindx) with (getReverseTranT lf (ind-rpl↓ ind ((x -ᵢ uind) ltuindx))) where
      x = (reverseTran lf₁ iind rvT₁)
      uind = (a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind))
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind
    | just rvT₁ | (yes ltuindx) | (just rvT₂) = just (cr2 rvT₁ ltuindx rvT₂)
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind
    | just rvT₁ | (yes ltuindx) | nothing = nothing
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind
    | just rvT₁ | (no ¬ltix) with (isLTi x uind) where
      x = (reverseTran lf₁ iind rvT₁)
      uind = (a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind))
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind
    | just rvT₁ | (no ¬ltix) | (yes ltxi) = nothing -- We do not accept transformations that change
                                                    -- the cll. The cll definitely changes here.
                                                    -- (unless lf only has I).
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind
    | just rvT₁ | (no ¬ltix) | (no ¬ltxi) = just (cr3 rvT₁ (¬lt¬gt⇒¬Ord ¬ltxi ¬ltix)) where
      x = (reverseTran lf₁ iind rvT₁)
      uind = (a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind))
  getReverseTranT (_⊂_ {_} {_} {ell} {_} {ind} lf lf₁) iind | nothing = nothing
  getReverseTranT (tr ltr lf) iind with (getReverseTranT lf iind)
  getReverseTranT (tr ltr lf) iind | just rvT₁ with (isUpTran (reverseTran lf iind rvT₁) (revTr ltr))
  getReverseTranT (tr ltr lf) iind | just rvT₁ | yes ut = just (cr4 rvT₁ ut)
  getReverseTranT (tr ltr lf) iind | just rvT₁ | no _ = nothing
  getReverseTranT (tr ltr lf) iind | nothing = nothing
  getReverseTranT (com df lf) iind = nothing
  getReverseTranT (call x) iind = nothing



  data IndRevNoComsT {i u ll pll ell cll} {ind : IndexLL {i} {u} pll ll}
                     {lind : IndexLL cll (replLL ll ind ell)} {lf : LFun pll ell} : Set (lsuc u) where
    c1 : let uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind) in (ltul : uind ≤ᵢ lind)
         → let x = (lind -ᵢ uind) ltul in (ReverseTranT lf (ind-rpl↓ ind x)) → IndRevNoComsT
    c2 : let uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind) in
         ¬ (Orderedᵢ lind uind) → IndRevNoComsT


  indRevNoComs : ∀{i u ll pll ell cll} → (ind : IndexLL {i} {u} pll ll)
                 → (lind : IndexLL cll (replLL ll ind ell)) → (lf : LFun pll ell)
                 → IndRevNoComsT {ind = ind} {lind = lind} {lf = lf} → IndexLL cll ll
  indRevNoComs {ell = ell} ind lind lf (c1 ltul rvT₁)
               = ind +ᵢ (reverseTran lf (ind-rpl↓ ind x) rvT₁) where
                 uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind)
                 x = (lind -ᵢ uind) ltul
  indRevNoComs {ell = ell} ind lind lf (c2 nord)
               = lemma₁-¬ord-a≤ᵢb ind ind ell (≤ᵢ-reflexive ind) lind (flipNotOrdᵢ nord)


-- This is almost the same code as above but it is required in IndexLFCo.
  getIndRevNoComsT : ∀{i u ll pll ell cll} → (ind : IndexLL {i} {u} pll ll)
                     → (lind : IndexLL cll (replLL ll ind ell)) → (lf : LFun pll ell)
                     → Maybe $ IndRevNoComsT {ind = ind} {lind = lind} {lf = lf}
  getIndRevNoComsT {ell = ell} ind lind lf with (isLTi uind lind) where
    uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind)
  getIndRevNoComsT {ell = ell} ind lind lf | yes ltul with (getReverseTranT lf (ind-rpl↓ ind x)) where
    uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind)
    x = (lind -ᵢ uind) ltul
  getIndRevNoComsT {ell = ell} ind lind lf | yes ltul | (just rvT) = just (c1 ltul rvT)
  getIndRevNoComsT {ell = ell} ind lind lf | yes ltul | nothing = nothing
  getIndRevNoComsT {ell = ell} ind lind lf | no ¬ltul with (isLTi lind uind) where
    uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind)
  getIndRevNoComsT {ell = ell} ind lind lf | no ¬ltul | (yes ltlu) = nothing
  getIndRevNoComsT {ell = ell} ind lind lf | no ¬ltul | (no ¬ltlu)
                   = just (c2 (¬lt¬gt⇒¬Ord ¬ltlu ¬ltul) )
  
  
data IndexLFCo {i u cll} (frll : LinLogic i {u}) : ∀{ll rll}
               → IndexLL cll ll → LFun {i} {u} ll rll → Set (lsuc u) where
  _←⊂ : ∀{rll pll ell ll ind elf lf lind}
         → IndexLFCo frll lind elf
         → IndexLFCo frll (ind +ᵢ lind) (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  ⊂→_ : ∀{rll pll ell ll ind elf lf lind}
         → IndexLFCo frll lind lf
         → (irnc : IndRevNoComsT {ind = ind} {lind = lind} {lf = elf})
         → let rs = indRevNoComs ind lind elf irnc in
           IndexLFCo frll rs (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  tr  : ∀{ll orll rll lind} → {ltr : LLTr orll ll} → {lf : LFun {i} {u} orll rll}
         → IndexLFCo frll lind lf
         → (ut : UpTran lind (revTr ltr))
         → let rs = tran lind (revTr ltr) ut in
           IndexLFCo frll rs (tr ltr lf) 
  ↓  : ∀{rll prfi prfo df lf}
         → IndexLFCo  frll ↓ (com {i} {u} {rll} {cll} {frll} {{prfi}} {{prfo}} df lf)


-- TODO We only use this when cll = ll in ↓, but it is difficult to transform SetLFCoRem.
-- The ind we save is the initial index at the beginning {oll}. During tranLFCoRem, we would have to
-- prove that cll does not change during this transformation. The information to prove that, exists in
-- IndexLFCo (tr) but we would need to show that the ltr is part of olf of IndexLFCo and then extract the information from IndexLFCo.
data SetLFCoRem {i u oll orll} (olf : LFun {i} {u} oll orll) : LinLogic i {u} → Set (lsuc u) where
  ↓    : ∀{ll cll frll} → {ind : IndexLL {i} {u} cll oll} → IndexLFCo frll ind olf → SetLFCoRem olf ll
  _←∧   : ∀{rs ls} → SetLFCoRem olf ls                   → SetLFCoRem olf (ls ∧ rs)
  ∧→_   : ∀{rs ls} → SetLFCoRem olf rs                   → SetLFCoRem olf (ls ∧ rs)
  _←∧→_ : ∀{rs ls} → SetLFCoRem olf ls → SetLFCoRem olf rs → SetLFCoRem olf (ls ∧ rs)
  _←∨   : ∀{rs ls} → SetLFCoRem olf ls                   → SetLFCoRem olf (ls ∨ rs)
  ∨→_   : ∀{rs ls} → SetLFCoRem olf rs                   → SetLFCoRem olf (ls ∨ rs)
  _←∨→_ : ∀{rs ls} → SetLFCoRem olf ls → SetLFCoRem olf rs → SetLFCoRem olf (ls ∨ rs)
  _←∂   : ∀{rs ls} → SetLFCoRem olf ls                   → SetLFCoRem olf (ls ∂ rs)
  ∂→_   : ∀{rs ls} → SetLFCoRem olf rs                   → SetLFCoRem olf (ls ∂ rs)
  _←∂→_ : ∀{rs ls} → SetLFCoRem olf ls → SetLFCoRem olf rs → SetLFCoRem olf (ls ∂ rs)

data MSetLFCoRem {i u oll orll} (olf : LFun {i} {u} oll orll) : LinLogic i {u} → Set (lsuc u) where
  ∅   : ∀{ll}            → MSetLFCoRem olf ll
  ¬∅  : ∀{ll} → SetLFCoRem olf ll → MSetLFCoRem olf ll

∅-addLFCoRem : ∀{i u ll pll oll orll frll cll} → {iind : IndexLL cll oll}
               → {olf : LFun {i} {u} oll orll} → (ind : IndexLL {i} {u} pll ll)
               → IndexLFCo frll iind olf → SetLFCoRem olf ll
∅-addLFCoRem ↓ m = ↓ m
∅-addLFCoRem (ind ←∧) m = (∅-addLFCoRem ind m) ←∧
∅-addLFCoRem (∧→ ind) m = ∧→ (∅-addLFCoRem ind m)
∅-addLFCoRem (ind ←∨) m = (∅-addLFCoRem ind m) ←∨
∅-addLFCoRem (∨→ ind) m = ∨→ (∅-addLFCoRem ind m)
∅-addLFCoRem (ind ←∂) m = (∅-addLFCoRem ind m) ←∂
∅-addLFCoRem (∂→ ind) m = ∂→ (∅-addLFCoRem ind m)

addLFCoRem : ∀{i u ll pll oll orll frll cll} → {iind : IndexLL cll oll}
             → {olf : LFun {i} {u} oll orll} → SetLFCoRem olf ll → (ind : IndexLL {i} {u} pll ll)
             → IndexLFCo frll iind olf → SetLFCoRem olf ll
addLFCoRem (↓ rm) ind m          = ↓ m
addLFCoRem (x ←∧) ↓ m            = ↓ m
addLFCoRem (∧→ x) ↓ m            = ↓ m --TODO Here we lose the information that is at lower levels.
addLFCoRem (x ←∧→ x₁) ↓ m        = ↓ m
addLFCoRem (x ←∨) ↓ m            = ↓ m
addLFCoRem (∨→ x) ↓ m            = ↓ m
addLFCoRem (x ←∨→ x₁) ↓ m        = ↓ m
addLFCoRem (x ←∂) ↓ m            = ↓ m
addLFCoRem (∂→ x) ↓ m            = ↓ m
addLFCoRem (x ←∂→ x₁) ↓ m        = ↓ m
addLFCoRem (s ←∧) (ind ←∧) m     = (addLFCoRem s ind m) ←∧
addLFCoRem (s ←∧) (∧→ ind) m     = s ←∧→ (∅-addLFCoRem ind m)
addLFCoRem (∧→ s) (ind ←∧) m     = (∅-addLFCoRem ind m) ←∧→ s
addLFCoRem (∧→ s) (∧→ ind) m     = ∧→ addLFCoRem s ind m
addLFCoRem (s ←∧→ s₁) (ind ←∧) m = (addLFCoRem s ind m) ←∧→ s₁
addLFCoRem (s ←∧→ s₁) (∧→ ind) m = s ←∧→ (addLFCoRem s₁ ind m)
addLFCoRem (s ←∨) (ind ←∨) m     = (addLFCoRem s ind m) ←∨
addLFCoRem (s ←∨) (∨→ ind) m     = s ←∨→ (∅-addLFCoRem ind m)
addLFCoRem (∨→ s) (ind ←∨) m     = (∅-addLFCoRem ind m) ←∨→ s
addLFCoRem (∨→ s) (∨→ ind) m     = ∨→ addLFCoRem s ind m
addLFCoRem (s ←∨→ s₁) (ind ←∨) m = (addLFCoRem s ind m) ←∨→ s₁
addLFCoRem (s ←∨→ s₁) (∨→ ind) m = s ←∨→ (addLFCoRem s₁ ind m)
addLFCoRem (s ←∂) (ind ←∂) m     = (addLFCoRem s ind m) ←∂
addLFCoRem (s ←∂) (∂→ ind) m     = s ←∂→ (∅-addLFCoRem ind m)
addLFCoRem (∂→ s) (ind ←∂) m     = (∅-addLFCoRem ind m) ←∂→ s
addLFCoRem (∂→ s) (∂→ ind) m     = ∂→ addLFCoRem s ind m
addLFCoRem (s ←∂→ s₁) (ind ←∂) m = (addLFCoRem s ind m) ←∂→ s₁
addLFCoRem (s ←∂→ s₁) (∂→ ind) m = s ←∂→ (addLFCoRem s₁ ind m)

maddLFCoRem : ∀{i u ll pll oll orll frll cll} → {iind : IndexLL cll oll}
              → {olf : LFun {i} {u} oll orll} → MSetLFCoRem olf ll
              → (ind : IndexLL {i} {u} pll ll) → IndexLFCo frll iind olf → MSetLFCoRem olf ll
maddLFCoRem ∅ ind m = ¬∅ (∅-addLFCoRem ind m)
maddLFCoRem (¬∅ x) ind m = ¬∅ (addLFCoRem x ind m)


truncSetLFCoRem : ∀{i} → ∀{u ll oll orll q} → {olf : LFun {i} {u} oll orll}
                  → MSetLFCoRem {i} {u} olf ll → (ind : IndexLL {i} {u} q ll) → MSetLFCoRem {i} olf q
truncSetLFCoRem ∅ ind = ∅
truncSetLFCoRem (¬∅ x) ↓ = ¬∅ x
truncSetLFCoRem (¬∅ (↓ x)) (ind ←∧) = ∅
truncSetLFCoRem (¬∅ (x ←∧)) (ind ←∧) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (∧→ x)) (ind ←∧) = ∅
truncSetLFCoRem (¬∅ (x ←∧→ x₁)) (ind ←∧) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (↓ x)) (∧→ ind) = ∅
truncSetLFCoRem (¬∅ (x ←∧)) (∧→ ind) = ∅
truncSetLFCoRem (¬∅ (∧→ x)) (∧→ ind) =  truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (x ←∧→ x₁)) (∧→ ind) =  truncSetLFCoRem (¬∅ x₁) ind
truncSetLFCoRem (¬∅ (↓ x)) (ind ←∨) = ∅
truncSetLFCoRem (¬∅ (x ←∨)) (ind ←∨) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (∨→ x)) (ind ←∨) = ∅
truncSetLFCoRem (¬∅ (x ←∨→ x₁)) (ind ←∨) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (↓ x)) (∨→ ind) = ∅
truncSetLFCoRem (¬∅ (x ←∨)) (∨→ ind) = ∅
truncSetLFCoRem (¬∅ (∨→ x)) (∨→ ind) =  truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (x ←∨→ x₁)) (∨→ ind) =  truncSetLFCoRem (¬∅ x₁) ind
truncSetLFCoRem (¬∅ (↓ x)) (ind ←∂) = ∅
truncSetLFCoRem (¬∅ (x ←∂)) (ind ←∂) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (∂→ x)) (ind ←∂) = ∅
truncSetLFCoRem (¬∅ (x ←∂→ x₁)) (ind ←∂) = truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (↓ x)) (∂→ ind) = ∅
truncSetLFCoRem (¬∅ (x ←∂)) (∂→ ind) = ∅
truncSetLFCoRem (¬∅ (∂→ x)) (∂→ ind) =  truncSetLFCoRem (¬∅ x) ind
truncSetLFCoRem (¬∅ (x ←∂→ x₁)) (∂→ ind) =  truncSetLFCoRem (¬∅ x₁) ind

delLFCoRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → SetLFCoRem {i} olf ll
             → (ind : IndexLL {i} {u} pll ll) → (rll : LinLogic i)
             → MSetLFCoRem {i} olf (replLL ll ind rll)
delLFCoRem s ↓ rll = ∅
delLFCoRem (↓ x) (ind ←∧) rll = ∅ -- We loose Information.
delLFCoRem (s ←∧) (ind ←∧) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∧) (ind ←∧) rll | ∅ = ∅
delLFCoRem (s ←∧) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧)
delLFCoRem (∧→ s) (ind ←∧) rll = ¬∅ (∧→ (s))
delLFCoRem (s ←∧→ s₁) (ind ←∧) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∧→ s₁) (ind ←∧) rll | ∅ = ¬∅ (∧→ (s₁))
delLFCoRem (s ←∧→ s₁) (ind ←∧) rll | ¬∅ x = ¬∅ (x ←∧→ (s₁))
delLFCoRem (↓ x) (∧→ ind) rll = ∅ --
delLFCoRem (s ←∧) (∧→ ind) rll = ¬∅ ((s) ←∧)
delLFCoRem (∧→ s) (∧→ ind) rll with (delLFCoRem s ind rll)
delLFCoRem (∧→ s) (∧→ ind) rll | ∅ = ∅
delLFCoRem (∧→ s) (∧→ ind) rll | ¬∅ x = ¬∅ (∧→ x)
delLFCoRem (s ←∧→ s₁) (∧→ ind) rll with (delLFCoRem s₁ ind rll)
delLFCoRem (s ←∧→ s₁) (∧→ ind) rll | ∅ = ¬∅ ((s) ←∧)
delLFCoRem (s ←∧→ s₁) (∧→ ind) rll | ¬∅ x = ¬∅ ((s) ←∧→ x)
delLFCoRem (↓ x) (ind ←∨) rll = ∅
delLFCoRem (s ←∨) (ind ←∨) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∨) (ind ←∨) rll | ∅ = ∅
delLFCoRem (s ←∨) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨)
delLFCoRem (∨→ s) (ind ←∨) rll = ¬∅ (∨→ (s))
delLFCoRem (s ←∨→ s₁) (ind ←∨) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∨→ s₁) (ind ←∨) rll | ∅ = ¬∅ (∨→ (s₁))
delLFCoRem (s ←∨→ s₁) (ind ←∨) rll | ¬∅ x = ¬∅ (x ←∨→ (s₁))
delLFCoRem (↓ x) (∨→ ind) rll = ∅
delLFCoRem (s ←∨) (∨→ ind) rll = ¬∅ ((s) ←∨)
delLFCoRem (∨→ s) (∨→ ind) rll with (delLFCoRem s ind rll)
delLFCoRem (∨→ s) (∨→ ind) rll | ∅ = ∅
delLFCoRem (∨→ s) (∨→ ind) rll | ¬∅ x = ¬∅ (∨→ x)
delLFCoRem (s ←∨→ s₁) (∨→ ind) rll with (delLFCoRem s₁ ind rll)
delLFCoRem (s ←∨→ s₁) (∨→ ind) rll | ∅ = ¬∅ ((s) ←∨)
delLFCoRem (s ←∨→ s₁) (∨→ ind) rll | ¬∅ x = ¬∅ ((s) ←∨→ x)
delLFCoRem (↓ x) (ind ←∂) rll = ∅
delLFCoRem (s ←∂) (ind ←∂) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∂) (ind ←∂) rll | ∅ = ∅
delLFCoRem (s ←∂) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂)
delLFCoRem (∂→ s) (ind ←∂) rll = ¬∅ (∂→ (s))
delLFCoRem (s ←∂→ s₁) (ind ←∂) rll with (delLFCoRem s ind rll)
delLFCoRem (s ←∂→ s₁) (ind ←∂) rll | ∅ = ¬∅ (∂→ (s₁))
delLFCoRem (s ←∂→ s₁) (ind ←∂) rll | ¬∅ x = ¬∅ (x ←∂→ (s₁))
delLFCoRem (↓ x) (∂→ ind) rll = ∅
delLFCoRem (s ←∂) (∂→ ind) rll = ¬∅ ((s) ←∂)
delLFCoRem (∂→ s) (∂→ ind) rll with (delLFCoRem s ind rll)
delLFCoRem (∂→ s) (∂→ ind) rll | ∅ = ∅
delLFCoRem (∂→ s) (∂→ ind) rll | ¬∅ x = ¬∅ (∂→ x)
delLFCoRem (s ←∂→ s₁) (∂→ ind) rll with (delLFCoRem s₁ ind rll)
delLFCoRem (s ←∂→ s₁) (∂→ ind) rll | ∅ = ¬∅ ((s) ←∂)
delLFCoRem (s ←∂→ s₁) (∂→ ind) rll | ¬∅ x = ¬∅ ((s) ←∂→ x)

mdelLFCoRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → MSetLFCoRem {i} olf ll
              → (ind : IndexLL {i} {u} pll ll) → (rll : LinLogic i)
              → MSetLFCoRem {i} olf (replLL ll ind rll)
mdelLFCoRem ∅ ind rll = ∅
mdelLFCoRem (¬∅ x) ind rll = delLFCoRem x ind rll

tranLFCoRem : ∀{i u oll orll ll rll} → {olf : LFun {i} {u} oll orll} → SetLFCoRem {i} olf ll
              → (tr : LLTr {i} {u} rll ll) → SetLFCoRem olf rll
tranLFCoRem s I                           = s
tranLFCoRem (s ←∂) (∂c ltr)                = tranLFCoRem (∂→ s) ltr
tranLFCoRem (↓ x) (∂c ltr)                = ↓ x
tranLFCoRem (∂→ s) (∂c ltr)                = tranLFCoRem (s ←∂) ltr
tranLFCoRem (s ←∂→ s₁) (∂c ltr)            = tranLFCoRem (s₁ ←∂→ s) ltr
tranLFCoRem (s ←∨) (∨c ltr)                = tranLFCoRem (∨→ s) ltr
tranLFCoRem (↓ x) (∨c ltr)                = ↓ x
tranLFCoRem (∨→ s) (∨c ltr)                = tranLFCoRem (s ←∨) ltr
tranLFCoRem (s ←∨→ s₁) (∨c ltr)            = tranLFCoRem (s₁ ←∨→ s) ltr
tranLFCoRem (s ←∧) (∧c ltr)                = tranLFCoRem (∧→ s) ltr
tranLFCoRem (↓ x) (∧c ltr)                = ↓ x
tranLFCoRem (∧→ s) (∧c ltr)                = tranLFCoRem (s ←∧) ltr
tranLFCoRem (s ←∧→ s₁) (∧c ltr)            = tranLFCoRem (s₁ ←∧→ s) ltr
tranLFCoRem ((s ←∧) ←∧) (∧∧d ltr)          = tranLFCoRem (s ←∧) ltr
tranLFCoRem (↓ x) (∧∧d ltr)          = ↓ x
tranLFCoRem ((↓ x) ←∧) (∧∧d ltr)          = tranLFCoRem ((↓ x) ←∧→ ((↓ x) ←∧)) ltr
tranLFCoRem ((∧→ s) ←∧) (∧∧d ltr)          = tranLFCoRem (∧→ (s ←∧)) ltr
tranLFCoRem ((s ←∧→ s₁) ←∧) (∧∧d ltr)      = tranLFCoRem (s ←∧→ (s₁ ←∧)) ltr
tranLFCoRem (∧→ s) (∧∧d ltr)               = tranLFCoRem (∧→ (∧→ s)) ltr
tranLFCoRem ((↓ x) ←∧→ s₁) (∧∧d ltr)      = tranLFCoRem ((↓ x) ←∧→ ((↓ x) ←∧→ s₁)) ltr
tranLFCoRem ((s ←∧) ←∧→ s₁) (∧∧d ltr)      = tranLFCoRem (s ←∧→ (∧→ s₁)) ltr
tranLFCoRem ((∧→ s) ←∧→ s₁) (∧∧d ltr)      = tranLFCoRem (∧→ (s ←∧→ s₁)) ltr
tranLFCoRem ((s ←∧→ s₁) ←∧→ s₂) (∧∧d ltr)  = tranLFCoRem (s ←∧→ (s₁ ←∧→ s₂)) ltr
tranLFCoRem (s ←∧) (¬∧∧d ltr)              = tranLFCoRem ((s ←∧) ←∧) ltr
tranLFCoRem (↓ x) (¬∧∧d ltr)              = ↓ x
tranLFCoRem (∧→ (↓ x)) (¬∧∧d ltr)         = tranLFCoRem ((∧→ (↓ x)) ←∧→ (↓ x)) ltr
tranLFCoRem (∧→ (s ←∧)) (¬∧∧d ltr)         = tranLFCoRem ((∧→ s) ←∧) ltr
tranLFCoRem (∧→ (∧→ s)) (¬∧∧d ltr)         = tranLFCoRem (∧→ s) ltr
tranLFCoRem (∧→ (s ←∧→ s₁)) (¬∧∧d ltr)     = tranLFCoRem ((∧→ s) ←∧→ s₁) ltr
tranLFCoRem (s ←∧→ (↓ x)) (¬∧∧d ltr)     = tranLFCoRem ((s ←∧→ (↓ x)) ←∧→ (↓ x)) ltr
tranLFCoRem (s ←∧→ (s₁ ←∧)) (¬∧∧d ltr)     = tranLFCoRem ((s ←∧→ s₁) ←∧) ltr
tranLFCoRem (s ←∧→ (∧→ s₁)) (¬∧∧d ltr)     = tranLFCoRem ((s ←∧) ←∧→ s₁) ltr
tranLFCoRem (s ←∧→ (s₁ ←∧→ s₂)) (¬∧∧d ltr) = tranLFCoRem ((s ←∧→ s₁) ←∧→ s₂) ltr
tranLFCoRem ((s ←∨) ←∨) (∨∨d ltr)          = tranLFCoRem (s ←∨) ltr
tranLFCoRem (↓ x) (∨∨d ltr)          = ↓ x
tranLFCoRem ((↓ x) ←∨) (∨∨d ltr)          = tranLFCoRem ((↓ x) ←∨→ ((↓ x) ←∨)) ltr
tranLFCoRem ((∨→ s) ←∨) (∨∨d ltr)          = tranLFCoRem (∨→ (s ←∨)) ltr
tranLFCoRem ((s ←∨→ s₁) ←∨) (∨∨d ltr)      = tranLFCoRem (s ←∨→ (s₁ ←∨)) ltr
tranLFCoRem (∨→ s) (∨∨d ltr)               = tranLFCoRem (∨→ (∨→ s)) ltr
tranLFCoRem ((↓ x) ←∨→ s₁) (∨∨d ltr)      = tranLFCoRem ((↓ x) ←∨→ ((↓ x) ←∨→ s₁)) ltr
tranLFCoRem ((s ←∨) ←∨→ s₁) (∨∨d ltr)      = tranLFCoRem (s ←∨→ (∨→ s₁)) ltr
tranLFCoRem ((∨→ s) ←∨→ s₁) (∨∨d ltr)      = tranLFCoRem (∨→ (s ←∨→ s₁)) ltr
tranLFCoRem ((s ←∨→ s₁) ←∨→ s₂) (∨∨d ltr)  = tranLFCoRem (s ←∨→ (s₁ ←∨→ s₂)) ltr
tranLFCoRem (s ←∨) (¬∨∨d ltr)              = tranLFCoRem ((s ←∨) ←∨) ltr
tranLFCoRem (↓ x) (¬∨∨d ltr)              = ↓ x
tranLFCoRem (∨→ (↓ x)) (¬∨∨d ltr)         = tranLFCoRem ((∨→ (↓ x)) ←∨→ (↓ x)) ltr
tranLFCoRem (∨→ (s ←∨)) (¬∨∨d ltr)         = tranLFCoRem ((∨→ s) ←∨) ltr
tranLFCoRem (∨→ (∨→ s)) (¬∨∨d ltr)         = tranLFCoRem (∨→ s) ltr
tranLFCoRem (∨→ (s ←∨→ s₁)) (¬∨∨d ltr)     = tranLFCoRem ((∨→ s) ←∨→ s₁) ltr
tranLFCoRem (s ←∨→ (↓ x)) (¬∨∨d ltr)     = tranLFCoRem ((s ←∨→ (↓ x)) ←∨→ (↓ x)) ltr
tranLFCoRem (s ←∨→ (s₁ ←∨)) (¬∨∨d ltr)     = tranLFCoRem ((s ←∨→ s₁) ←∨) ltr
tranLFCoRem (s ←∨→ (∨→ s₁)) (¬∨∨d ltr)     = tranLFCoRem ((s ←∨) ←∨→ s₁) ltr
tranLFCoRem (s ←∨→ (s₁ ←∨→ s₂)) (¬∨∨d ltr) = tranLFCoRem ((s ←∨→ s₁) ←∨→ s₂) ltr
tranLFCoRem ((s ←∂) ←∂) (∂∂d ltr)          = tranLFCoRem (s ←∂) ltr
tranLFCoRem (↓ x) (∂∂d ltr)          = ↓ x
tranLFCoRem ((↓ x) ←∂) (∂∂d ltr)          = tranLFCoRem ((↓ x) ←∂→ ((↓ x) ←∂)) ltr
tranLFCoRem ((∂→ s) ←∂) (∂∂d ltr)          = tranLFCoRem (∂→ (s ←∂)) ltr
tranLFCoRem ((s ←∂→ s₁) ←∂) (∂∂d ltr)      = tranLFCoRem (s ←∂→ (s₁ ←∂)) ltr
tranLFCoRem (∂→ s) (∂∂d ltr)               = tranLFCoRem (∂→ (∂→ s)) ltr
tranLFCoRem ((↓ x) ←∂→ s₁) (∂∂d ltr)      = tranLFCoRem ((↓ x) ←∂→ ((↓ x) ←∂→ s₁)) ltr
tranLFCoRem ((s ←∂) ←∂→ s₁) (∂∂d ltr)      = tranLFCoRem (s ←∂→ (∂→ s₁)) ltr
tranLFCoRem ((∂→ s) ←∂→ s₁) (∂∂d ltr)      = tranLFCoRem (∂→ (s ←∂→ s₁)) ltr
tranLFCoRem ((s ←∂→ s₁) ←∂→ s₂) (∂∂d ltr)  = tranLFCoRem (s ←∂→ (s₁ ←∂→ s₂)) ltr
tranLFCoRem (s ←∂) (¬∂∂d ltr)              = tranLFCoRem ((s ←∂) ←∂) ltr
tranLFCoRem (∂→ (s ←∂)) (¬∂∂d ltr)         = tranLFCoRem ((∂→ s) ←∂) ltr
tranLFCoRem (↓ x) (¬∂∂d ltr)         = ↓ x
tranLFCoRem (∂→ (↓ x)) (¬∂∂d ltr)         = tranLFCoRem ((∂→ (↓ x)) ←∂→ (↓ x)) ltr
tranLFCoRem (∂→ (∂→ s)) (¬∂∂d ltr)         = tranLFCoRem (∂→ s) ltr
tranLFCoRem (∂→ (s ←∂→ s₁)) (¬∂∂d ltr)     = tranLFCoRem ((∂→ s) ←∂→ s₁) ltr
tranLFCoRem (s ←∂→ (↓ x)) (¬∂∂d ltr)     = tranLFCoRem ((s ←∂→ (↓ x)) ←∂→ (↓ x)) ltr
tranLFCoRem (s ←∂→ (s₁ ←∂)) (¬∂∂d ltr)     = tranLFCoRem ((s ←∂→ s₁) ←∂) ltr
tranLFCoRem (s ←∂→ (∂→ s₁)) (¬∂∂d ltr)     = tranLFCoRem ((s ←∂) ←∂→ s₁) ltr
tranLFCoRem (s ←∂→ (s₁ ←∂→ s₂)) (¬∂∂d ltr) = tranLFCoRem ((s ←∂→ s₁) ←∂→ s₂) ltr


extendLFCoRem : ∀{i u oll orll ll pll} → {olf : LFun {i} {u} oll orll} → IndexLL {i} {u} pll ll
                → SetLFCoRem {i} olf pll → SetLFCoRem olf ll
extendLFCoRem ↓ sr = sr
extendLFCoRem (ind ←∧) sr = (extendLFCoRem ind sr) ←∧
extendLFCoRem (∧→ ind) sr = ∧→ (extendLFCoRem ind sr)
extendLFCoRem (ind ←∨) sr = (extendLFCoRem ind sr) ←∨
extendLFCoRem (∨→ ind) sr = ∨→ (extendLFCoRem ind sr)
extendLFCoRem (ind ←∂) sr = (extendLFCoRem ind sr) ←∂
extendLFCoRem (∂→ ind) sr = ∂→ (extendLFCoRem ind sr)

replaceLFCoRem : ∀{i u oll orll ll pll rll} → {olf : LFun {i} {u} oll orll}
                 → (ind : IndexLL {i} {u} pll ll) → SetLFCoRem {i} olf rll → SetLFCoRem olf ll
                 → SetLFCoRem olf (replLL ll ind rll)
replaceLFCoRem ↓ esr sr = esr
replaceLFCoRem {rll = rll} (ind ←∧) esr (↓ x) = (extendLFCoRem (updInd rll ind) esr) ←∧
replaceLFCoRem {rll = rll} (ind ←∧) esr (sr ←∧) = replaceLFCoRem ind esr sr ←∧
replaceLFCoRem {rll = rll} (ind ←∧) esr (∧→ sr) = (extendLFCoRem (updInd rll ind) esr) ←∧→ sr
replaceLFCoRem {rll = rll} (ind ←∧) esr (sr ←∧→ sr₁) = (replaceLFCoRem ind esr sr) ←∧→ sr₁
replaceLFCoRem {rll = rll} (∧→ ind) esr (↓ x) = ∧→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∧→ ind) esr (sr ←∧) = sr ←∧→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∧→ ind) esr (∧→ sr) = ∧→ replaceLFCoRem ind esr sr
replaceLFCoRem {rll = rll} (∧→ ind) esr (sr ←∧→ sr₁) = sr ←∧→ replaceLFCoRem ind esr sr₁
replaceLFCoRem {rll = rll} (ind ←∨) esr (↓ x) = (extendLFCoRem (updInd rll ind) esr) ←∨
replaceLFCoRem {rll = rll} (ind ←∨) esr (sr ←∨) = replaceLFCoRem ind esr sr ←∨
replaceLFCoRem {rll = rll} (ind ←∨) esr (∨→ sr) = (extendLFCoRem (updInd rll ind) esr) ←∨→ sr
replaceLFCoRem {rll = rll} (ind ←∨) esr (sr ←∨→ sr₁) = (replaceLFCoRem ind esr sr) ←∨→ sr₁
replaceLFCoRem {rll = rll} (∨→ ind) esr (↓ x) = ∨→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∨→ ind) esr (sr ←∨) = sr ←∨→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∨→ ind) esr (∨→ sr) = ∨→ replaceLFCoRem ind esr sr
replaceLFCoRem {rll = rll} (∨→ ind) esr (sr ←∨→ sr₁) = sr ←∨→ replaceLFCoRem ind esr sr₁
replaceLFCoRem {rll = rll} (ind ←∂) esr (↓ x) = (extendLFCoRem (updInd rll ind) esr) ←∂
replaceLFCoRem {rll = rll} (ind ←∂) esr (sr ←∂) = replaceLFCoRem ind esr sr ←∂
replaceLFCoRem {rll = rll} (ind ←∂) esr (∂→ sr) = (extendLFCoRem (updInd rll ind) esr) ←∂→ sr
replaceLFCoRem {rll = rll} (ind ←∂) esr (sr ←∂→ sr₁) = (replaceLFCoRem ind esr sr) ←∂→ sr₁
replaceLFCoRem {rll = rll} (∂→ ind) esr (↓ x) = ∂→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∂→ ind) esr (sr ←∂) = sr ←∂→ (extendLFCoRem (updInd rll ind) esr)
replaceLFCoRem {rll = rll} (∂→ ind) esr (∂→ sr) = ∂→ replaceLFCoRem ind esr sr
replaceLFCoRem {rll = rll} (∂→ ind) esr (sr ←∂→ sr₁) = sr ←∂→ replaceLFCoRem ind esr sr₁


mreplaceLFCoRem :  ∀{i u oll orll ll pll rll} → {olf : LFun {i} {u} oll orll}
                   → (ind : IndexLL {i} {u} pll ll) → MSetLFCoRem {i} olf rll → MSetLFCoRem olf ll
                   → MSetLFCoRem olf (replLL ll ind rll)
mreplaceLFCoRem ind ∅ ∅ = ∅
mreplaceLFCoRem {rll = rll} ind ∅ (¬∅ x) = delLFCoRem x ind rll
mreplaceLFCoRem {rll = rll} ind (¬∅ x) ∅ = ¬∅ (extendLFCoRem (updInd rll ind) x)
mreplaceLFCoRem ind (¬∅ x) (¬∅ x₁) = ¬∅ (replaceLFCoRem ind x x₁)


--------------------------------------

-- TODO I need better names and to try to understand whether some of those data types can be merged.

data IndexLFCof {i u} : ∀{ll rll} → LFun {i} {u} ll rll → Set where
  ↓  : ∀{cll frll rll prfi prfo df lf}
         → IndexLFCof (com {i} {u} {rll} {cll} {frll} {{prfi}} {{prfo}} df lf)
  _←⊂ : ∀{rll pll ell ll ind elf lf}
         → IndexLFCof elf
         → IndexLFCof (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  ⊂→_ : ∀{rll pll ell ll ind elf lf}
         → IndexLFCof lf
         → IndexLFCof (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  tr   : ∀{ll orll rll} → {ltr : LLTr orll ll} → {lf : LFun {i} {u} orll rll}
         → IndexLFCof lf → IndexLFCof (tr ltr lf) 



data SetLFCof {i u} : ∀{ll rll} → LFun {i} {u} ll rll → Set (lsuc u) where
  ↓  : ∀{cll frll rll prfi prfo df lf}
         → SetLFCof (com {i} {u} {rll} {cll} {frll} {{prfi}} {{prfo}} df lf)
  _←⊂ : ∀{rll pll ell ll ind elf lf}
         → SetLFCof elf
         → SetLFCof (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  ⊂→_ : ∀{rll pll ell ll ind elf lf}
         → SetLFCof lf
         → SetLFCof (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  _←⊂→_ : ∀{rll pll ell ll ind elf lf}
         → SetLFCof elf
         → SetLFCof lf
         → SetLFCof (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  tr   : ∀{ll orll rll} → {ltr : LLTr orll ll} → {lf : LFun {i} {u} orll rll}
         → SetLFCof lf
         → SetLFCof (tr ltr lf) 

data MSetLFCof {i u} : ∀{ll rll} → LFun {i} {u} ll rll → Set (lsuc u) where
  ∅   : ∀{ll rll} → {lf : LFun {i} {u} ll rll}            → MSetLFCof lf
  ¬∅  : ∀{ll rll} → {lf : LFun {i} {u} ll rll} → SetLFCof lf → MSetLFCof lf

∅-addLFCof : ∀{i u ll rll} → {lf : LFun {i} {u} ll rll} → IndexLFCof lf → SetLFCof lf 
∅-addLFCof ↓ = ↓
∅-addLFCof (ic ←⊂) = (∅-addLFCof ic) ←⊂
∅-addLFCof (⊂→ ic) = ⊂→ (∅-addLFCof ic)
∅-addLFCof (tr ic) = tr (∅-addLFCof ic)

addLFCof : ∀{i u ll rll} → {lf : LFun {i} {u} ll rll} → SetLFCof lf → IndexLFCof lf → SetLFCof lf 
addLFCof ↓ ↓            = ↓ -- We replace the previous info
addLFCof (s ←⊂) (ic ←⊂)     = (addLFCof s ic) ←⊂
addLFCof (⊂→ s) (ic ←⊂)     = (∅-addLFCof ic) ←⊂→ s
addLFCof (s ←⊂→ s₁) (ic ←⊂) =  (addLFCof s ic) ←⊂→ s₁
addLFCof (s ←⊂) (⊂→ ic)     = s ←⊂→ (∅-addLFCof ic)
addLFCof (⊂→ s) (⊂→ ic)     = ⊂→ (addLFCof s ic)
addLFCof (s ←⊂→ s₁) (⊂→ ic) = s ←⊂→ (addLFCof s₁ ic)
addLFCof (tr s) (tr ic)     = tr (addLFCof s ic)


maddLFCof : ∀{i u ll rll} → {lf : LFun {i} {u} ll rll} → MSetLFCof lf → IndexLFCof lf → MSetLFCof lf
maddLFCof ∅ ic = ¬∅ (∅-addLFCof ic)
maddLFCof (¬∅ x) ic = ¬∅ (addLFCof x ic)



delLFCof : ∀{i u ll rll} → {lf : LFun {i} {u} ll rll} → SetLFCof lf → IndexLFCof lf → MSetLFCof lf
delLFCof x ↓                = ∅
delLFCof (x ←⊂) (ic ←⊂) with (delLFCof x ic)
delLFCof (x ←⊂) (ic ←⊂) | ∅ = ∅
delLFCof (x ←⊂) (ic ←⊂) | ¬∅ x₁ = ¬∅ (x₁ ←⊂)
delLFCof (⊂→ x) (ic ←⊂)     = ¬∅ (⊂→ x) 
delLFCof (x ←⊂→ x₁) (ic ←⊂) with (delLFCof x ic)
delLFCof (x ←⊂→ x₁) (ic ←⊂) | ∅ = ¬∅ (⊂→ x₁)
delLFCof (x ←⊂→ x₂) (ic ←⊂) | ¬∅ x₁ = ¬∅ (x₁ ←⊂→ x₂)
delLFCof (x ←⊂) (⊂→ ic) = ¬∅ (x ←⊂)
delLFCof (⊂→ x) (⊂→ ic) with (delLFCof x ic)
delLFCof (⊂→ x) (⊂→ ic) | ∅ = ∅
delLFCof (⊂→ x) (⊂→ ic) | ¬∅ x₁ = ¬∅ (⊂→ x₁)
delLFCof (x ←⊂→ x₁) (⊂→ ic) with (delLFCof x₁ ic)
delLFCof (x ←⊂→ x₁) (⊂→ ic) | ∅ = ¬∅ (⊂→ x₁)
delLFCof (x ←⊂→ x₁) (⊂→ ic) | ¬∅ x₂ = ¬∅ (x ←⊂→ x₂)
delLFCof (tr x) (tr ic) with (delLFCof x ic)
delLFCof (tr x) (tr ic) | ∅ = ∅
delLFCof (tr x) (tr ic) | ¬∅ x₁ = ¬∅ (tr x₁)


mdelLFCof : ∀{i u ll rll} → {lf : LFun {i} {u} ll rll} → MSetLFCof lf → IndexLFCof lf → MSetLFCof lf
mdelLFCof ∅ ic = ∅
mdelLFCof (¬∅ x) ic = delLFCof x ic

_+ₛₗ_ : ∀{i u ll rll} → {lf : LFun {i} {u} ll rll} → SetLFCof lf → SetLFCof lf → SetLFCof lf
↓ +ₛₗ b = ↓
(a ←⊂) +ₛₗ (b ←⊂) = (a +ₛₗ b) ←⊂
(a ←⊂) +ₛₗ (⊂→ b) = a ←⊂→ b
(a ←⊂) +ₛₗ (b ←⊂→ b₁) = (a +ₛₗ b) ←⊂→ b₁
(⊂→ a) +ₛₗ (b ←⊂) = b ←⊂→ a
(⊂→ a) +ₛₗ (⊂→ b) = ⊂→ (a +ₛₗ b)
(⊂→ a) +ₛₗ (b ←⊂→ b₁) = b ←⊂→ (a +ₛₗ b₁)
(a ←⊂→ a₁) +ₛₗ (b ←⊂) = (a +ₛₗ b) ←⊂→ a₁
(a ←⊂→ a₁) +ₛₗ (⊂→ b) = a ←⊂→ (a₁ +ₛₗ b)
(a ←⊂→ a₁) +ₛₗ (b ←⊂→ b₁) = (a +ₛₗ b) ←⊂→ (a₁ +ₛₗ b₁)
tr a +ₛₗ tr b = tr (a +ₛₗ b)

_+ₘₛₗ_ : ∀{i u ll rll} → {lf : LFun {i} {u} ll rll} → MSetLFCof lf → MSetLFCof lf → MSetLFCof lf
∅ +ₘₛₗ b = b
¬∅ x +ₘₛₗ ∅ = ¬∅ x
¬∅ x +ₘₛₗ ¬∅ x₁ = ¬∅ (x +ₛₗ x₁)
