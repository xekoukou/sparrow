module IndexLFCo where

open import Common
open import LinLogic
open import LinFun
-- open import SetLL
open import Data.Maybe


data IndexLFCo {i u cll} (frll : LinLogic i {u}) : ∀{ll rll} → IndexLL cll ll → LFun {i} {u} ll rll → Set (u) where
  _←⊂ : ∀{rll pll ell ll ind elf lf s}
         → IndexLFCo cll frll s elf
         → IndexLFCo cll frll (extend ind s) (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  ⊂→_ : ∀{rll pll ell ll ind elf lf s rs}
         → IndexLFCo cll frll s lf
         → {prf : just rs ≡ setRevNoComs ind s elf}
         → IndexLFCo cll frll rs (_⊂_ {i} {u} {pll} {ll} {ell} {rll} {ind} elf lf)
  tr   : ∀{ll orll rll s rs} → {ltr : LLTr orll ll} → {lf : LFun {i} {u} orll rll}
         → IndexLFCo cll frll s lf
         → {prf : rs ≡ tran s (revTr ltr) }
         → IndexLFCo cll frll rs (tr ltr lf) 
  ↓  : ∀{rll prfi prfo df lf}
         → IndexLFCo cll frll ↓ (com {i} {u} {rll} {cll} {frll} {{prfi}} {{prfo}} df lf)
