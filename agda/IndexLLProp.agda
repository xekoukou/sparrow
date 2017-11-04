-- {-# OPTIONS --show-implicit #-}

module IndexLLProp where

open import Common
open import LinLogic
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Sum

data _≅ᵢ_ {i u gll} : ∀{fll ll} → IndexLL {i} {u} gll ll → IndexLL {i} {u} fll ll → Set (lsuc u) where
  instance 
    ≅ᵢ↓ :  ↓ ≅ᵢ ↓
    ≅ᵢic : ∀{fll ict ll tll il eq} → {sind : IndexLL gll ll} → {bind : IndexLL fll ll} → {{ieq : sind ≅ᵢ bind}}
           → _≅ᵢ_ {ll = il[ il ]} (ic {tll = tll} ict eq sind) (ic ict eq bind)



≅ᵢ-spec : ∀{i u ll ict tll il gll fll eq} → {sind : IndexLL {i} {u} gll ll}
          → {bind : IndexLL fll ll} → _≅ᵢ_ {ll = il[ il ]} (ic {tll = tll} ict eq sind) (ic ict eq bind)
          → (sind ≅ᵢ bind)
≅ᵢ-spec (≅ᵢic {{ieq = a}}) = a


instance
  ≅ᵢ-reflexive : ∀{i u rll ll} → {a : IndexLL {i} {u} rll ll} → a ≅ᵢ a
  ≅ᵢ-reflexive {a = ↓} = ≅ᵢ↓
  ≅ᵢ-reflexive {a = (ic _ _ _)} = ≅ᵢic 

-- Possibly it needs to be removed.
instance
  ≡-to-≅ᵢ : ∀{i u rll ll} → {a b : IndexLL {i} {u} rll ll} → a ≡ b → a ≅ᵢ b
  ≡-to-≅ᵢ refl = ≅ᵢ-reflexive



data _≤ᵢ_ {i u gll fll} : ∀{ll} → IndexLL {i} {u} gll ll → IndexLL {i} {u} fll ll → Set (lsuc u) where
  instance
    ≤ᵢ↓ : {ind : IndexLL fll gll} → ↓ ≤ᵢ ind
    ≤ᵢic : ∀{ll ict tll il eq} → {sind : IndexLL gll ll} → {bind : IndexLL fll ll} → {{ieq : sind ≤ᵢ bind}}
           → _≤ᵢ_ {ll = il[ il ]} (ic {tll = tll} ict eq sind) (ic ict eq bind)


≤ᵢ-spec : ∀{i u ll ict tll il gll fll eq} → {sind : IndexLL {i} {u} gll ll}
          → {bind : IndexLL fll ll} → _≤ᵢ_ {ll = il[ il ]} (ic {tll = tll} ict eq sind) (ic ict eq bind)
          → (sind ≤ᵢ bind)
≤ᵢ-spec (≤ᵢic {{ieq = rl}}) = rl


instance
  ≤ᵢ-reflexive : ∀{i u gll ll} → {ind : IndexLL {i} {u} gll ll} → ind ≤ᵢ ind
  ≤ᵢ-reflexive {ind = ↓} = ≤ᵢ↓
  ≤ᵢ-reflexive {ind = (ic _ _ _)} = ≤ᵢic

≤ᵢ-transitive : ∀{i u gll fll mll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL fll ll} → {c : IndexLL mll ll} → (a ≤ᵢ b) → (b ≤ᵢ c) → (a ≤ᵢ c)
≤ᵢ-transitive ≤ᵢ↓ b = ≤ᵢ↓
≤ᵢ-transitive (≤ᵢic {{ieq = x}}) (≤ᵢic {{ieq = y}}) = ≤ᵢic {{ieq = (≤ᵢ-transitive x y)}}


module _ where

  mutual
  
    isLTi-abs1 : ∀{u i ll tll ict il rll gll ica icb a b eq}
                 → ica ≡ ic {i} {u} {rll} {ll = ll} {tll} {il} ict eq a
                 → icb ≡ ic {_} {_} {gll} {ll = ll} ict eq b
                 → Dec (a ≤ᵢ b)
                 → Dec (ica ≤ᵢ icb)
    isLTi-abs1 refl refl (yes p) = p asInst (yes it)
    isLTi-abs1 refl refl (no ¬p) = no (λ p → ¬p (≤ᵢ-spec p))


    isLTi-abs : ∀{u i lla tlla icta il llb tllb ictb rll gll ica icb} → ∀{{eqa eqb}} → ∀ a b
                → ica ≡ ic {i} {u} {rll} {ll = lla} {tlla} {il} icta eqa a
                → icb ≡ ic {_} {_} {gll} {ll = llb} {tllb} ictb eqb b
               → IndU icta ictb eqa eqb
                → Dec (ica ≤ᵢ icb)
    isLTi-abs a b iceqa iceqb (ictEq _ _ _ refl) = isLTi-abs1 iceqa iceqb (isLTi a b)
    isLTi-abs a b refl refl (ict¬Eq ¬icteq reqa reqb) = no λ { (≤ᵢic) → ¬icteq refl}
    
    isLTi : ∀{i u gll ll fll} → (a : IndexLL {i} {u} gll ll) → (b : IndexLL fll ll) → Dec (a ≤ᵢ b)
    isLTi ↓ b = yes it
    isLTi (ic _ _ a) ↓ = no λ ()
    isLTi (ic _ _ a) (ic _ _ b) = isLTi-abs a b refl refl (compIndU _ _ _ _)




module _ where
  mutual 
    isEqᵢ-abs1 : ∀{u i ll tll ict il rll eq} → {a : IndexLL {i} {u} rll ll} → {b : IndexLL rll ll} → Dec (a ≡ b) → Dec (ic {tll = tll} {il} ict eq a ≡ ic ict eq b)
    isEqᵢ-abs1 (yes refl) = yes refl
    isEqᵢ-abs1 (no ¬p) = no λ { refl → ¬p refl}

    isEqᵢ-abs : ∀{u i lla tlla icta il llb tllb ictb rll ica icb eqa eqb} → ∀ a b
            → ica ≡ ic {i} {u} {rll} {ll = lla} {tlla} {il} icta eqa a
            → icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} ictb eqb b
            → IndU icta ictb eqa eqb
            → Dec (ica ≡ icb)
    isEqᵢ-abs a b refl refl (ictEq _ _ _ refl) = isEqᵢ-abs1 (isEqᵢ a b)
    isEqᵢ-abs a b refl refl (ict¬Eq ¬icteq reqa reqb) = no λ { refl → ¬icteq refl}
    
    isEqᵢ : ∀{u i ll rll} → (a : IndexLL {i} {u} rll ll) → (b : IndexLL rll ll) → Dec (a ≡ b)
    isEqᵢ ↓ ↓ = yes refl
    isEqᵢ ↓ (ic _ _ _) = no λ ()
    isEqᵢ (ic _ _ _) ↓ = no λ ()
    isEqᵢ (ic _ _ a) (ic _ _ b) = isEqᵢ-abs a b refl refl (compIndU _ _ _ _)
   


module _ where

  open import Data.Vec

  mutual

    indτ-le⇒ieq-abs : ∀{u i lla tlla icta il llb tllb ictb rll n dt df ica icb eqa eqb} → ∀ a b
            → ica ≡ ic {i} {u} {τ {n = n} {dt} df} {ll = lla} {tlla} {il} icta eqa a
            → icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} ictb eqb b
            → {{ rl : ica ≤ᵢ icb }} 
            → IndU icta ictb eqa eqb
            → icb ≅ᵢ ica
    indτ-le⇒ieq-abs a b refl refl {{≤ᵢic}} (ictEq _ _ _ refl) = ≅ᵢic
    indτ-le⇒ieq-abs a b refl refl {{≤ᵢic}} (ict¬Eq ¬icteq reqa reqb) = ⊥-elim (¬icteq refl)

    instance
      indτ-le⇒ieq : ∀{i u rll ll n dt df} → {ind : IndexLL {i} {u} (τ {i} {u} {n} {dt} df) ll} → {ind2 : IndexLL rll ll} → {{rl : ind ≤ᵢ ind2}} → (ind2 ≅ᵢ ind)
      indτ-le⇒ieq {ind = ↓} {↓} = ≅ᵢ↓
      indτ-le⇒ieq {ind = ic _ _ _} {↓} {{()}}
      indτ-le⇒ieq {ind = (ic _ _ ind1)} {(ic _ _ ind2)} = indτ-le⇒ieq-abs ind1 ind2 refl refl (compIndU _ _ _ _)



data Orderedᵢ {i u gll fll ll} (a : IndexLL {i} {u} gll ll) (b : IndexLL {i} {u} fll ll) : Set (lsuc u) where
  instance
    a≤ᵢb : {{rl : a ≤ᵢ b}} → Orderedᵢ a b
    b≤ᵢa : {{rl : b ≤ᵢ a}} → Orderedᵢ a b



ord-spec : ∀{i u rll ll ict tll il fll eq} → {emi : IndexLL {i} {u} fll ll}
           → {ind : IndexLL rll ll} → Orderedᵢ (ic {tll = tll} {il} ict eq ind) (ic ict eq emi) → Orderedᵢ ind emi
ord-spec (a≤ᵢb {{rl = x}}) = a≤ᵢb {{rl = (≤ᵢ-spec x)}}
ord-spec (b≤ᵢa {{rl = x}}) = b≤ᵢa {{rl = (≤ᵢ-spec x)}}


instance
  ord-ext : ∀{i u rll ll ict tll il fll eq} → {emi : IndexLL {i} {u} fll ll}
             → {ind : IndexLL rll ll} → Orderedᵢ ind emi → Orderedᵢ (ic {tll = tll} {il} ict eq ind) (ic ict eq emi)
  ord-ext a≤ᵢb = a≤ᵢb
  ord-ext b≤ᵢa = b≤ᵢa



ord-spec∘ord-ext≡id : ∀{i u ll ict tll il fll rll eq} → (ind : IndexLL {i} {u} fll ll) → (lind : IndexLL rll ll) → {{ ord : Orderedᵢ ind lind }} → ord-spec {ict = ict} {tll = tll} {il} {eq = eq} (ord-ext {ict = ict} {tll = tll} ord) ≡ ord
ord-spec∘ord-ext≡id _ _ {{ord = a≤ᵢb}} = refl
ord-spec∘ord-ext≡id _ _ {{ord = b≤ᵢa}} = refl


≅⇒bord : ∀{i u rll pll ll}
              → {ind : IndexLL {i} {u} pll ll} {lind : IndexLL rll ll}
              → {{eq : lind ≅ᵢ ind}} → (ind ≤ᵢ lind) × (lind ≤ᵢ ind)
≅⇒bord {{eq = ≅ᵢ↓}} = ≤ᵢ↓ , ≤ᵢ↓
≅⇒bord {{eq = ≅ᵢic}} = ≤ᵢic {{ieq = (proj₁ r)}} , ≤ᵢic {{ieq = (proj₂ r)}} where
  r = ≅⇒bord


module _ where

  isOrdᵢ-abs : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
               → Dec (a ≤ᵢ b) → Dec (b ≤ᵢ a)
               → Dec (Orderedᵢ a b)
  isOrdᵢ-abs (yes p) r = p asInst (yes it)
  isOrdᵢ-abs (no ¬p) (yes p) = p asInst (yes it)
  isOrdᵢ-abs (no ¬p) (no ¬p₁) = no (λ { a≤ᵢb → ¬p it ; b≤ᵢa → ¬p₁ it})
  
  isOrdᵢ : ∀{i u gll fll ll} → (a : IndexLL {i} {u} gll ll) → (b : IndexLL {i} {u} fll ll)
           → Dec (Orderedᵢ a b)
  isOrdᵢ a b = isOrdᵢ-abs (isLTi a b) (isLTi b a) 




flipOrdᵢ : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
           → Orderedᵢ a b → Orderedᵢ b a
flipOrdᵢ a≤ᵢb = b≤ᵢa
flipOrdᵢ b≤ᵢa = a≤ᵢb


¬lt¬gt⇒¬Ord : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
              → ¬ (a ≤ᵢ b) → ¬ (b ≤ᵢ a) → ¬ (Orderedᵢ a b)
¬lt¬gt⇒¬Ord nlt ngt a≤ᵢb = nlt it
¬lt¬gt⇒¬Ord nlt ngt b≤ᵢa = ngt it



ord⇒icteq : ∀{u i lla tlla icta il llb tllb ictb fll rll a b ica icb eqa eqb}
       → (iceqa : ica ≡ ic {i} {u} {fll} {ll = lla} {tlla} {il} icta eqa a)
       → (iceqb : icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} ictb eqb b)
       → Orderedᵢ icb ica
       → icta ≡ ictb
ord⇒icteq refl refl (a≤ᵢb {{≤ᵢic}}) = refl
ord⇒icteq refl refl (b≤ᵢa {{≤ᵢic}}) = refl

instance
  indτ&Ord⇒ge : ∀{i u rll ll n dt df} → {ind : IndexLL (τ {i} {u} {n} {dt} df) ll}
                            {lind : IndexLL rll ll} → {{ord : Orderedᵢ ind lind}} → lind ≤ᵢ ind
  indτ&Ord⇒ge {ind = ind} {lind} {{a≤ᵢb}} = proj₂ ≅⇒bord
  indτ&Ord⇒ge {ind = ind} {lind} {{b≤ᵢa {{rl = rl}}}} = rl



a,c≤ᵢb⇒ordac : ∀{i u gll fll mll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL fll ll} → {c : IndexLL mll ll} → (a ≤ᵢ b) → (c ≤ᵢ b) → Orderedᵢ a c
a,c≤ᵢb⇒ordac ≤ᵢ↓ ltbc = a≤ᵢb
a,c≤ᵢb⇒ordac ≤ᵢic ≤ᵢ↓ = b≤ᵢa
a,c≤ᵢb⇒ordac (≤ᵢic {{ieq = ltab}}) (≤ᵢic {{ieq = ltcb}}) = ord-ext (a,c≤ᵢb⇒ordac ltab ltcb)


a≤ᵢb&¬ordac⇒¬ordbc : ∀{i u gll fll mll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL fll ll} → {c : IndexLL mll ll} → (a ≤ᵢ b) → ¬ Orderedᵢ a c → ¬ Orderedᵢ b c
a≤ᵢb&¬ordac⇒¬ordbc lt nord (a≤ᵢb {{rl = x}}) = ⊥-elim (nord (a≤ᵢb {{rl = (≤ᵢ-transitive lt x)}}))
a≤ᵢb&¬ordac⇒¬ordbc lt nord (b≤ᵢa {{rl = x}}) = ⊥-elim (nord (a,c≤ᵢb⇒ordac lt x))



_-ᵢ_ : ∀ {i u pll cll ll} → (bind : IndexLL {i} {u} cll ll) → (sind : IndexLL pll ll) → {{rl : sind ≤ᵢ bind}}
       → IndexLL cll pll
(bind -ᵢ .↓) {{rl = ≤ᵢ↓}} = bind
((ic _ _ bind) -ᵢ (ic _ _ sind)) {{rl = ≤ᵢic}} = bind -ᵢ sind


-- TODO Why do I need to specify rl?
ind-ᵢind≡↓ : ∀ {i u pll ll} → (ind : IndexLL {i} {u} pll ll) → {{rl : ind ≤ᵢ ind}}
       → (ind -ᵢ ind) {{rl = rl}} ≡ ↓
ind-ᵢind≡↓ _ {{rl = ≤ᵢ↓}} = refl
ind-ᵢind≡↓ (ic _ _ ind) {{rl = ≤ᵢic {{ieq = rl}}}} = ind-ᵢind≡↓ ind



rpl↓ : ∀{i u ll pll ell} → (ind : IndexLL {i} {u} pll ll)
        → (replLL (ind -ᵢ ind) ell) ≡ ell
rpl↓ {ell = ell} ind = cong (λ z → replLL z ell) (ind-ᵢind≡↓ ind)

ind-rpl↓ : ∀{i u ll pll cll ell} → (ind : IndexLL {i} {u} pll ll)
        → IndexLL cll (replLL (ind -ᵢ ind) ell) → IndexLL cll ell
ind-rpl↓ {_} {_} {_} {pll} {cll} {ell} ind y
  =  subst (λ x → x) (cong (λ x → IndexLL cll x) (rpl↓ ind)) y 



a≤ᵢb-morph : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll)
             → (ind : IndexLL rll ll) → ∀ {frll} → {{lt : emi ≤ᵢ ind}}
             → IndexLL (replLL (ind -ᵢ emi) frll) (replLL ind frll) 
a≤ᵢb-morph .↓ ind {{lt = ≤ᵢ↓}} = ↓
a≤ᵢb-morph (ic ict eq emi) (ic _ _ ind) {{lt = ≤ᵢic}} = ic ict refl (a≤ᵢb-morph emi ind)




module _ where

  a≤ᵢb-morph-id-abs : ∀{i u ll tll ict rll eq}
               → {ind : IndexLL {i} {u} rll ll}
               → ∀ {w₁T} → (w₁ : w₁T ≡ rll)  -- w₁T : replLL ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll
               → ∀ {w₂T} → (w₂ : w₂T ≡ ll) -- w₂T : replLL li ind rl
               → (w₃ : IndexLL w₁T w₂T) -- w₃ : (a≤ᵢb-morph ind ind (≤ᵢ-reflexive ind))
               → (w₄ : subst₂ (λ x y → IndexLL x y) w₁ w₂ w₃ ≡ ind) -- recursive step
               → ∀{eqw}
               →  subst₂ IndexLL w₁ (cong (λ x → il[ expLLT x ict tll ]) w₂) (ic {tll = tll} ict eqw w₃)
                 ≡
                  ic {tll = tll} ict eq ind
  a≤ᵢb-morph-id-abs {eq = refl} refl refl _ refl {eqw = refl} = refl


  a≤ᵢb-morph-id : ∀{i u ll rll}
               → (ind : IndexLL {i} {u} rll ll)
               → subst₂ (λ x y → IndexLL x y) (rpl↓ ind) (replLL-id ind) (a≤ᵢb-morph ind ind) ≡ ind
  a≤ᵢb-morph-id ↓ = refl
  a≤ᵢb-morph-id {rll = rll} (ic _ refl ind) = a≤ᵢb-morph-id-abs (rpl↓ ind) (replLL-id ind) (a≤ᵢb-morph ind ind) (a≤ᵢb-morph-id ind)



replLL-a≤b≡a : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll) → ∀ {gll}
               → (ind : IndexLL rll ll) → ∀ frll → {{lt : emi ≤ᵢ ind}}
               → replLL (a≤ᵢb-morph emi ind {frll = frll}) gll ≡ replLL emi gll
replLL-a≤b≡a .↓ ind _ {{lt = ≤ᵢ↓}} = refl
replLL-a≤b≡a (ic {tll = tll} ict _ emi) (ic _ _ ind) _ {{lt = ≤ᵢic}} = cong (λ x → il[ expLLT x ict tll ]) (replLL-a≤b≡a emi ind _)



module _ where

  mutual
  
    ¬ord-morph-abs : ∀{u i lla tlla icta il eqa llb tllb ictb eqb fll rll frll a b ica icb}
              → ica ≡ ic {i} {u} {fll} {ll = lla} {tlla} {il} icta eqa a
              → icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} ictb eqb b
              → ¬ Orderedᵢ icb ica
              → IndU icta ictb eqa eqb
              → IndexLL fll il[ expLLT (replLL b frll) ictb tllb ]
    ¬ord-morph-abs {tllb = tllb} {ictb} {frll = frll} {a} refl refl nord (ictEq _ _ _ refl)
        = ic ictb refl (¬ord-morph a {frll = frll} (λ p → nord (ord-ext p)))
    ¬ord-morph-abs {icta = icta} {eqa = eqa} {eqb = eqb} {frll = frll} {a} {b} refl refl nord (ict¬Eq ¬icteq refl refl)
        = ic {tll = replLL b frll} icta (indOp⇒rexpLLT {{iop = rexpLLT⇒IndOp ¬icteq eqa eqb}}) a


    ¬ord-morph : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll)
                 → {ind : IndexLL rll ll} → ∀ {frll} → (nord : ¬ Orderedᵢ ind emi)
                 → IndexLL fll (replLL ind frll)
    ¬ord-morph emi {ind = ↓} nord = ⊥-elim (nord it)
    ¬ord-morph ↓ {ind = (ic _ _ _)} nord = ⊥-elim (nord it)
    ¬ord-morph (ic _ _ emi) {ind = (ic _ _ ind)} {frll} nord
        = ¬ord-morph-abs refl refl nord (compIndU _ _ _ _)


module _ where

mutual

    ¬ord-morph-¬ord-ir-abs : ∀{u i lla tlla icta il eqa llb tllb ictb eqb fll rll ica icb a b} → ∀ frll
      → (iceqa : ica ≡ ic {i} {u} {fll} {ll = lla} {tlla} {il} icta eqa a)
      → (iceqb : icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} ictb eqb b)
      → (nord1 nord2 : ¬ Orderedᵢ icb ica)
      → (w : IndU icta ictb eqa eqb)
      →  ¬ord-morph-abs {frll = frll} iceqa iceqb nord1 w ≡ ¬ord-morph-abs iceqa iceqb nord2 w
    ¬ord-morph-¬ord-ir-abs {tllb = tllb} {ictb} frll refl refl nord1 nord2 (ictEq _ _ _ refl)
        = cong (λ z → ic ictb refl z) (¬ord-morph-¬ord-ir frll (λ p → nord1 (ord-ext p)) (λ p → nord2 (ord-ext p)))
    ¬ord-morph-¬ord-ir-abs _ refl refl nord1 nord2 (ict¬Eq ¬icteq refl refl) = refl


    ¬ord-morph-¬ord-ir : ∀{i u rll ll fll} → {emi : IndexLL {i} {u} fll ll}
                         → {ind : IndexLL rll ll} → ∀ frll → (nord nord2 : ¬ Orderedᵢ ind emi)
                         → ¬ord-morph emi {ind = ind} {frll} nord ≡ ¬ord-morph emi nord2
    ¬ord-morph-¬ord-ir {emi = ↓} _ nord nord2 = ⊥-elim (nord it)
    ¬ord-morph-¬ord-ir {emi = (ic _ _ emi)} {ind = ↓} _ nord nord2 = ⊥-elim (nord it)
    ¬ord-morph-¬ord-ir {emi = ice@(ic _ _ emi)} {ind = ici@(ic _ _ ind)} _ nord nord2 = ¬ord-morph-¬ord-ir-abs _ refl refl nord nord2 (compIndU _ _ _ _)



module _ where

  mutual

    replLL-¬ordab≡ba-abs : ∀{u i lla tlla icta il eqa llb tllb ictb eqb fll rll ica icb a b} → ∀ frll gll
      → (iceqa : ica ≡ ic {i} {u} {fll} {ll = lla} {tlla} {il} icta eqa a)
      → (iceqb : icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} ictb eqb b)
      → (nord : ¬ Orderedᵢ icb ica)
      → (fnord : ¬ Orderedᵢ ica icb)
      → ∀ w1 w2
      → replLL
          (¬ord-morph-abs {frll = frll} iceqa iceqb nord w1) gll
        ≡
        replLL
          (¬ord-morph-abs {frll = gll} iceqb iceqa fnord w2) frll
    replLL-¬ordab≡ba-abs {tllb = tllb} {ictb} {eqb} frll gll refl refl nord fnord (ictEq _ _ _ refl) (ictEq _ _ _ refl)
      =  cong (λ z → il[ expLLT z ictb tllb ])
              (replLL-¬ordab≡ba _ _ (λ p → nord (ord-ext p)) (λ p → fnord (ord-ext p)))
    replLL-¬ordab≡ba-abs _ _ iceqa iceqb nord fnord (ictEq icteq lleq tlleq eqeq) (ict¬Eq ¬icteq reqa reqb) = ⊥-elim (¬icteq (sym icteq))
    replLL-¬ordab≡ba-abs _ _ iceqa iceqb nord fnord (ict¬Eq ¬icteq reqa reqb) (ictEq icteq lleq tlleq eqeq) = ⊥-elim (¬icteq (sym icteq))
    replLL-¬ordab≡ba-abs {eqa = eqa} {eqb = eqb} _ _ refl refl nord fnord (ict¬Eq _ refl refl) (ict¬Eq ¬icteq refl refl) = cong il[_] (indOp⇒rexpLLT {{iop = rexpLLT⇒IndOp ¬icteq eqb eqa}})


    replLL-¬ordab≡ba : ∀{i u rll ll fll}
      → {emi : IndexLL {i} {u} fll ll} → ∀ gll
      → {ind : IndexLL rll ll} → ∀ frll
      → (nord : ¬ Orderedᵢ ind emi)
      → (fnord : ¬ Orderedᵢ emi ind)
      → replLL (¬ord-morph emi {ind = ind} {frll} nord) gll ≡ replLL (¬ord-morph ind {ind = emi} {gll} fnord) frll
    replLL-¬ordab≡ba {emi = ↓} _ _ nord = ⊥-elim (nord it)
    replLL-¬ordab≡ba {emi = (ic _ _ emi)} _ {ind = ↓} _ nord fnord = ⊥-elim (nord it)
    replLL-¬ordab≡ba {emi = ice@(ic _ _ emi)} _ {ind = ici@(ic _ _ ind)} _ nord fnord = replLL-¬ordab≡ba-abs _ _ refl refl nord fnord (compIndU _ _ _ _) (compIndU _ _ _ _)




module _ where

  mutual

    lemma₁-¬ord-a≤ᵢb-abs : ∀{u i ll tll ict il llc tllc ictc fll rll pll ica icb a b c ell eq eqc}
               → ∀ {icc}
               → ica ≡ ic {i} {u} {fll} {ll = ll} {tll} {il} ict eq a
               → icb ≡ ic {i} {u} {rll} {ll = ll} {tll} ict eq b
               → icc ≡ ic {i} {u} {pll} {ll = llc} {tllc} {expLLT (replLL b ell) ict tll} ictc eqc c
               → ∀ {{lt}}
               → ¬ Orderedᵢ (ic ict refl (a≤ᵢb-morph a b {ell} {{lt = lt}})) icc
               → IndU ict ictc refl eqc
               → IndexLL pll il[ il ]
    lemma₁-¬ord-a≤ᵢb-abs {tll = tll} {ict} {ell = ell} {eq = eq} iceqa iceqb refl nord (ictEq _ _ _ refl) = ic ict eq (lemma₁-¬ord-a≤ᵢb (λ p → nord (ord-ext p)))
    lemma₁-¬ord-a≤ᵢb-abs {ll = ll} {ictc = ictc} {c = c} {eq = eq} {eqc} iceqa iceqb iceqc nord (ict¬Eq ¬icteq refl refl) = ic {tll = ll} ictc (trans eq (sym (indOp⇒rexpLLT {{iop = rexpLLT⇒IndOp ¬icteq refl eqc}}))) c



-- This is the reverse of ¬ord-morph
    lemma₁-¬ord-a≤ᵢb : ∀{i u ll pll rll fll}
          → {emi : IndexLL {i} {u} fll ll}
          → {ind : IndexLL rll ll} → ∀ {ell} → {{lt : emi ≤ᵢ ind}}
          → {omi : IndexLL pll (replLL ind ell)}
          → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind {ell}) omi)
          → IndexLL pll ll
    lemma₁-¬ord-a≤ᵢb {ind = ind} {{≤ᵢ↓}} nord = ⊥-elim (nord it)
    lemma₁-¬ord-a≤ᵢb {{≤ᵢic}} {omi = ↓} nord = ⊥-elim (nord it)
    lemma₁-¬ord-a≤ᵢb {emi = ica@(ic _ _ a)} {ind = icb@(ic _ eq b)} {{≤ᵢic}} {omi = icc@(ic _ _ c)} nord = lemma₁-¬ord-a≤ᵢb-abs {eq = eq} refl refl refl nord (compIndU _ _ _ _)



module _ where

mutual

    ¬ord-morph⇒¬ord-abs : ∀{u i lla tlla icta il eqa llb tllb ictb eqb fll rll frll ica icb a b}
           → (iceqa : ica ≡ ic {i} {u} {fll} {ll = lla} {tlla} {il} icta eqa a)
           → (iceqb : icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} ictb eqb b)
           → (nord : ¬ Orderedᵢ icb ica)
           → (w : IndU icta ictb eqa eqb)
           →  ¬ Orderedᵢ (ic ictb refl (a≤ᵢb-morph b b {frll = frll}))
                         (¬ord-morph-abs {frll = frll} iceqa iceqb nord w)
    ¬ord-morph⇒¬ord-abs {frll = frll} refl refl nord (ictEq icteq lleq tlleq refl) = λ p → r (ord-spec p) where 
      r = ¬ord-morph⇒¬ord {frll = frll} (λ p → nord (ord-ext p))
    ¬ord-morph⇒¬ord-abs {tllb = tllb} {ictb} {frll = frll} refl refl nord (ict¬Eq ¬icteq refl refl) = λ p → ¬icteq (ord⇒icteq refl refl p)
  
  
    ¬ord-morph⇒¬ord : ∀{i u rll ll fll} → {emi : IndexLL {i} {u} fll ll}
          → {ind : IndexLL rll ll} → ∀ {frll} → (nord : ¬ Orderedᵢ ind emi)
          → ¬ Orderedᵢ (a≤ᵢb-morph ind ind {frll}) (¬ord-morph emi nord)
    ¬ord-morph⇒¬ord {emi = ↓} nord = ⊥-elim (nord it)
    ¬ord-morph⇒¬ord {emi = (ic _ _ emi)} {ind = ↓} nord = ⊥-elim (nord it)
    ¬ord-morph⇒¬ord {emi = (ic _ _ emi)} {ind = (ic _ _ ind)} {frll} nord = ¬ord-morph⇒¬ord-abs {frll = frll} refl refl nord (compIndU _ _ _ _)



module _ where

  mutual

    rlemma₁⇒¬ord-abs : ∀{u i ll tll ict il eq llc tllc ictc fll rll pll ica icb a b c ell}
           → ∀{eqc icc}
           → (iceqa : ica ≡ ic {i} {u} {fll} {ll = ll} {tll} {il} ict eq a)
           → (iceqb : icb ≡ ic {i} {u} {rll} {ll = ll} {tll} ict eq b)
           → (iceqc : icc ≡ ic {i} {u} {pll} {ll = llc} {tllc} {expLLT (replLL b ell) ict tll} ictc eqc c)
           → ∀ {{lt}}
           → (nord : ¬ Orderedᵢ (ic ict refl (a≤ᵢb-morph a b {ell})) icc)
           → (w : IndU ict ictc refl eqc)
           → ¬ Orderedᵢ ica
                        (lemma₁-¬ord-a≤ᵢb-abs iceqa iceqb iceqc {{lt}} nord w)
    rlemma₁⇒¬ord-abs {ell = ell} refl refl refl nord (ictEq icteq lleq tlleq refl) = λ x → r (ord-spec x) where
      r = rlemma₁⇒¬ord (λ p → nord (ord-ext p))
    rlemma₁⇒¬ord-abs refl refl refl nord (ict¬Eq ¬icteq refl refl) = λ p → (¬icteq (sym (ord⇒icteq refl refl p)))


    rlemma₁⇒¬ord : ∀{i u ll pll rll fll}
       → {emi : IndexLL {i} {u} fll ll}
       → {ind : IndexLL rll ll} → ∀ {ell} → {{lt : emi ≤ᵢ ind}}
       → {omi : IndexLL pll (replLL ind ell)}
       → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind {ell}) omi)
       → ¬ Orderedᵢ emi (lemma₁-¬ord-a≤ᵢb nord)
    rlemma₁⇒¬ord {{lt = ≤ᵢ↓}} {omi} nord = ⊥-elim (nord it)
    rlemma₁⇒¬ord {{lt = ≤ᵢic}} {↓} nord = ⊥-elim (nord it)
    rlemma₁⇒¬ord {emi = (ic _ _ emi)} {ind = (ic _ _ ind)} {{lt = ≤ᵢic}} {omi = (ic _ _ omi)} nord = rlemma₁⇒¬ord-abs refl refl refl nord (compIndU _ _ _ _)



module _ where

  ¬ord-morph$lemma₁≡I : ∀{i u pll ll cll fll ell} → {emi : IndexLL {i} {u} fll ll} → {ind : IndexLL {i} {u} pll ll} → {{lt : emi ≤ᵢ ind}} → {lind : IndexLL cll (replLL ind ell)} → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind {ell}) lind) → (lnord : ¬ Orderedᵢ ind (lemma₁-¬ord-a≤ᵢb nord))
        → (¬ord-morph (lemma₁-¬ord-a≤ᵢb nord) lnord ≡ lind)
  ¬ord-morph$lemma₁≡I {emi = .↓} {ind} {{≤ᵢ↓}} {lind} nord lnord = ⊥-elim (nord it)
  ¬ord-morph$lemma₁≡I {emi = .(ic _ _ _)} {.(ic _ _ _)} {{≤ᵢic}} {↓} nord lnord = ⊥-elim (nord it)
  ¬ord-morph$lemma₁≡I {emi = (ic ict eq _)} {.(ic _ _ _)} {{≤ᵢic}} {ic ictc eqc lind} nord lnord with compIndU ict ictc refl eqc 
  ¬ord-morph$lemma₁≡I {ell = _} {ic ict eq _} {.(ic ict eq _)} {{≤ᵢic}} {ic ictc eqc lind} nord lnord | ict¬Eq ¬icteq refl refl with (compIndU ictc ict (trans eq (sym (indOp⇒rexpLLT {{iop = rexpLLT⇒IndOp ¬icteq refl eqc}}))) eq)
  ... | ict¬Eq ¬icteq₁ refl refl = cong (λ z → ic ictc z lind) (eqEq _ _)
  ... | ictEq icteq _ _ eqeq = ⊥-elim (¬icteq (sym icteq)) 
  ¬ord-morph$lemma₁≡I {ell = _} {ic ict eq _} {.(ic ict eq _)} {{≤ᵢic}} {ic .ict .refl lind} nord lnord | ictEq icteq lleq tlleq refl with compIndU ict ict eq eq
  ... | ictEq _ _ _ refl = cong (λ z → ic ict refl z) (¬ord-morph$lemma₁≡I  (λ p → nord (ord-ext p)) (λ p → lnord (ord-ext p)))
  ... | ict¬Eq ¬icteq refl refl = ⊥-elim (¬icteq icteq)


    
--   ¬ord-morph$lemma₁≡I : ∀{i u pll ll cll fll} → ∀ ell → (emi : IndexLL {i} {u} fll ll) → (ind : IndexLL {i} {u} pll ll) → (lt : emi ≤ᵢ ind) → (lind : IndexLL cll (replLL ll ind ell)) → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind ell lt) lind)
--        → (¬ord-morph (lemma₁-¬ord-a≤ᵢb emi ind ell lt lind nord) ind ell (a≤ᵢb&¬ordac⇒¬ordbc lt (rlemma₁⇒¬ord emi ind ell lt lind nord)) ≡ lind)
--   ¬ord-morph$lemma₁≡I ell emi ind lt lind nord = ¬ord-morph$lemma₁≡I' ell emi ind lt lind nord (a≤ᵢb&¬ordac⇒¬ordbc lt (rlemma₁⇒¬ord emi ind ell lt lind nord))



_+ᵢ_ : ∀{i u pll cll ll} → IndexLL {i} {u} pll ll → IndexLL cll pll → IndexLL cll ll
↓ +ᵢ b = b
ic ict eq a +ᵢ b = ic ict eq (a +ᵢ b)


instance
  +ᵢ⇒l≤ᵢ+ᵢ : ∀{i u pll cll ll} → {ind : IndexLL {i} {u} pll ll} → {lind : IndexLL cll pll}
             → ind ≤ᵢ (ind +ᵢ lind)
  +ᵢ⇒l≤ᵢ+ᵢ {ind = ↓} = ≤ᵢ↓
  +ᵢ⇒l≤ᵢ+ᵢ {ind = ic _ _ _} = ≤ᵢic


a+↓≡a : ∀{i u pll ll} → {a : IndexLL {i} {u} pll ll} → a +ᵢ ↓ ≡ a
a+↓≡a {a = ↓} = refl
a+↓≡a {a = ic ict eq a} = cong (λ z → ic ict eq z) a+↓≡a


[a+b]-a=b : ∀{i u rll ll fll} → (a : IndexLL {i} {u} fll ll)
          → (b : IndexLL rll fll)
          → ((a +ᵢ b) -ᵢ a) ≡ b
[a+b]-a=b ↓ b = refl
[a+b]-a=b (ic ict eq a) b = [a+b]-a=b a b


a+[b-a]=b : ∀{i u rll ll fll} → (a : IndexLL {i} {u} fll ll)
            → (b : IndexLL rll ll)
            → {{lt : a ≤ᵢ b}}
            → (a +ᵢ (b -ᵢ a))  ≡ b
a+[b-a]=b .↓ b {{≤ᵢ↓}} = refl
a+[b-a]=b (ic _ _ a) (ic _ _ b) {{≤ᵢic}} = cong (λ z → ic _ _ z) (a+[b-a]=b a b)




drepl=>repl+ : ∀{i u pll ll cll frll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll)
               → (replLL ind (replLL lind frll)) ≡ replLL (ind +ᵢ lind) frll
drepl=>repl+ ↓ lind = refl
drepl=>repl+ (ic ict eq ind) lind = cong (λ z → il[ expLLT z ict _ ]) (drepl=>repl+ ind lind)



-- repl-r=>l : ∀{i u pll ll cll frll} → ∀ ell → (ind : IndexLL {i} {u} pll ll) → (x : IndexLL cll (replLL ll ind ell)) → let uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind)
--        in (ltuindx : uind ≤ᵢ x)
--        → (replLL ll ind (replLL ell (ind-rpl↓ ind ((x -ᵢ uind) ltuindx)) frll) ≡ replLL (replLL ll ind ell) x frll)
-- repl-r=>l ell ↓ x ≤ᵢ↓ = refl
-- repl-r=>l {ll = li ∧ ri} ell (ind ←∧) (x ←∧) (≤ᵢ←∧ ltuindx) = cong (λ x → x ∧ ri) (repl-r=>l ell ind x ltuindx)
-- repl-r=>l {ll = li ∧ ri} ell (∧→ ind) (∧→ x) (≤ᵢ∧→ ltuindx) = cong (λ x → li ∧ x) (repl-r=>l ell ind x ltuindx)
-- repl-r=>l {ll = li ∨ ri} ell (ind ←∨) (x ←∨) (≤ᵢ←∨ ltuindx) = cong (λ x → x ∨ ri) (repl-r=>l ell ind x ltuindx)
-- repl-r=>l {ll = li ∨ ri} ell (∨→ ind) (∨→ x) (≤ᵢ∨→ ltuindx) = cong (λ x → li ∨ x) (repl-r=>l ell ind x ltuindx)
-- repl-r=>l {ll = li ∂ ri} ell (ind ←∂) (x ←∂) (≤ᵢ←∂ ltuindx) = cong (λ x → x ∂ ri) (repl-r=>l ell ind x ltuindx)
-- repl-r=>l {ll = li ∂ ri} ell (∂→ ind) (∂→ x) (≤ᵢ∂→ ltuindx) = cong (λ x → li ∂ x) (repl-r=>l ell ind x ltuindx)




-- -- A predicate that is true if pll is not transformed by ltr.

-- data UpTran {i u} : ∀ {ll pll rll} → IndexLL pll ll → LLTr {i} {u} rll ll → Set (lsuc u) where
--   indI : ∀{pll ll} → {ind : IndexLL pll ll} → UpTran ind I
--   ←∂∂c : ∀{pll li ri rll ltr} → {ind : IndexLL pll ri} → UpTran {ll = li ∂ ri} {rll = rll} (∂→ ind) ltr
--          → UpTran (ind ←∂) (∂c ltr)
--   ∂→∂c : ∀{pll li ri rll ltr} → {ind : IndexLL pll li} → UpTran {ll = li ∂ ri} {rll = rll} (ind ←∂) ltr
--          → UpTran (∂→ ind) (∂c ltr)
--   ←∨∨c : ∀{pll li ri rll ltr} → {ind : IndexLL pll ri} → UpTran {ll = li ∨ ri} {rll = rll} (∨→ ind) ltr
--          → UpTran (ind ←∨) (∨c ltr)
--   ∨→∨c : ∀{pll li ri rll ltr} → {ind : IndexLL pll li} → UpTran {ll = li ∨ ri} {rll = rll} (ind ←∨) ltr
--          → UpTran (∨→ ind) (∨c ltr)
--   ←∧∧c : ∀{pll li ri rll ltr} → {ind : IndexLL pll ri} → UpTran {ll = li ∧ ri} {rll = rll} (∧→ ind) ltr
--          → UpTran (ind ←∧) (∧c ltr)
--   ∧→∧c : ∀{pll li ri rll ltr} → {ind : IndexLL pll li} → UpTran {ll = li ∧ ri} {rll = rll} (ind ←∧) ltr
--          → UpTran (∧→ ind) (∧c ltr)
--   ←∧]←∧∧∧d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lli}
--             → UpTran {rll = rll} (ind ←∧) ltr → UpTran {ll = (lli ∧ lri) ∧ ri} ((ind ←∧) ←∧) (∧∧d ltr)
--   ∧→]←∧∧∧d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lri}
--             → UpTran {rll = rll} (∧→ (ind ←∧)) ltr
--             → UpTran {ll = (lli ∧ lri) ∧ ri} ((∧→ ind) ←∧) (∧∧d ltr)
--   ∧→∧∧d    : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll ri}
--             → UpTran {rll = rll} (∧→ (∧→ ind)) ltr
--             → UpTran {ll = ((lli ∧ lri) ∧ ri)} (∧→ ind) (∧∧d ltr)
--   ←∧¬∧∧d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll li}
--             → UpTran {rll = rll} ((ind ←∧) ←∧) ltr
--             → UpTran {ll = li ∧ (rli ∧ rri)} (ind ←∧) (¬∧∧d ltr)
--   ∧→[←∧¬∧∧d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rli}
--             → UpTran {rll = rll} ((∧→ ind) ←∧) ltr
--             → UpTran {ll = li ∧ (rli ∧ rri)} (∧→ (ind ←∧)) (¬∧∧d ltr)
--   ∧→[∧→¬∧∧d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rri}
--             → UpTran {rll = rll} (∧→ ind) ltr
--             → UpTran {ll = li ∧ (rli ∧ rri)} (∧→ (∧→ ind)) (¬∧∧d ltr)
--   ←∨]←∨∨∨d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lli}
--             → UpTran {rll = rll} (ind ←∨) ltr → UpTran {ll = (lli ∨ lri) ∨ ri} ((ind ←∨) ←∨) (∨∨d ltr)
--   ∨→]←∨∨∨d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lri}
--             → UpTran {rll = rll} (∨→ (ind ←∨)) ltr
--             → UpTran {ll = (lli ∨ lri) ∨ ri} ((∨→ ind) ←∨) (∨∨d ltr)
--   ∨→∨∨d    : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll ri}
--             → UpTran {rll = rll} (∨→ (∨→ ind)) ltr
--             → UpTran {ll = (lli ∨ lri) ∨ ri} (∨→ ind) (∨∨d ltr)
--   ←∨¬∨∨d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll li}
--             → UpTran {rll = rll} ((ind ←∨) ←∨) ltr
--             → UpTran {ll = li ∨ (rli ∨ rri)} (ind ←∨) (¬∨∨d ltr)
--   ∨→[←∨¬∨∨d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rli}
--             → UpTran {rll = rll} ((∨→ ind) ←∨) ltr
--             → UpTran {ll = li ∨ (rli ∨ rri)} (∨→ (ind ←∨)) (¬∨∨d ltr)
--   ∨→[∨→¬∨∨d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rri}
--             → UpTran {rll = rll} (∨→ ind) ltr
--             → UpTran {ll = li ∨ (rli ∨ rri)} (∨→ (∨→ ind)) (¬∨∨d ltr)
--   ←∂]←∂∂∂d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lli}
--             → UpTran {rll = rll} (ind ←∂) ltr → UpTran {ll = (lli ∂ lri) ∂ ri} ((ind ←∂) ←∂) (∂∂d ltr)
--   ∂→]←∂∂∂d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lri}
--             → UpTran {rll = rll} (∂→ (ind ←∂)) ltr
--             → UpTran {ll = (lli ∂ lri) ∂ ri} ((∂→ ind) ←∂) (∂∂d ltr)
--   ∂→∂∂d    : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll ri}
--             → UpTran {rll = rll} (∂→ (∂→ ind)) ltr
--             → UpTran {ll = (lli ∂ lri) ∂ ri} (∂→ ind) (∂∂d ltr)
--   ←∂¬∂∂d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll li}
--             → UpTran {rll = rll} ((ind ←∂) ←∂) ltr
--             → UpTran {ll = li ∂ (rli ∂ rri)} (ind ←∂) (¬∂∂d ltr)
--   ∂→[←∂¬∂∂d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rli}
--             → UpTran {rll = rll} ((∂→ ind) ←∂) ltr
--             → UpTran {ll = li ∂ (rli ∂ rri)} (∂→ (ind ←∂)) (¬∂∂d ltr)
--   ∂→[∂→¬∂∂d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rri}
--             → UpTran {rll = rll} (∂→ ind) ltr
--             → UpTran {ll = li ∂ (rli ∂ rri)} (∂→ (∂→ ind)) (¬∂∂d ltr)

-- isUpTran : ∀ {i u ll pll rll} → (ind : IndexLL pll ll) → (ltr : LLTr {i} {u} rll ll) → Dec (UpTran ind ltr)
-- isUpTran ind I = yes indI
-- isUpTran ↓ (∂c ltr) = no (λ ())
-- isUpTran (ind ←∂) (∂c ltr) with (isUpTran (∂→ ind) ltr)
-- isUpTran (ind ←∂) (∂c ltr) | yes ut = yes (←∂∂c ut)
-- isUpTran (ind ←∂) (∂c ltr) | no ¬ut = no (λ {(←∂∂c ut) → ¬ut ut})
-- isUpTran (∂→ ind) (∂c ltr)  with (isUpTran (ind ←∂) ltr)
-- isUpTran (∂→ ind) (∂c ltr) | yes ut = yes (∂→∂c ut)
-- isUpTran (∂→ ind) (∂c ltr) | no ¬ut = no (λ {(∂→∂c ut) → ¬ut ut})
-- isUpTran ↓ (∨c ltr) = no (λ ())
-- isUpTran (ind ←∨) (∨c ltr) with (isUpTran (∨→ ind) ltr)
-- isUpTran (ind ←∨) (∨c ltr) | yes p = yes (←∨∨c p)
-- isUpTran (ind ←∨) (∨c ltr) | no ¬p = no (λ {(←∨∨c p) → ¬p p}) 
-- isUpTran (∨→ ind) (∨c ltr) with (isUpTran (ind ←∨) ltr)
-- isUpTran (∨→ ind) (∨c ltr) | yes p = yes (∨→∨c p)
-- isUpTran (∨→ ind) (∨c ltr) | no ¬p = no (λ {(∨→∨c ut) → ¬p ut})
-- isUpTran ↓ (∧c ltr) = no (λ ())
-- isUpTran (ind ←∧) (∧c ltr) with (isUpTran (∧→ ind) ltr)
-- isUpTran (ind ←∧) (∧c ltr) | yes p = yes (←∧∧c p)
-- isUpTran (ind ←∧) (∧c ltr) | no ¬p = no (λ {(←∧∧c ut) → ¬p ut}) 
-- isUpTran (∧→ ind) (∧c ltr) with (isUpTran (ind ←∧) ltr)
-- isUpTran (∧→ ind) (∧c ltr) | yes p = yes (∧→∧c p)
-- isUpTran (∧→ ind) (∧c ltr) | no ¬p = no (λ {(∧→∧c ut) → ¬p ut})
-- isUpTran ↓ (∧∧d ltr) = no (λ ())
-- isUpTran (↓ ←∧) (∧∧d ltr) = no (λ ())
-- isUpTran ((ind ←∧) ←∧) (∧∧d ltr) with (isUpTran (ind ←∧) ltr)
-- isUpTran ((ind ←∧) ←∧) (∧∧d ltr) | yes p = yes (←∧]←∧∧∧d p)
-- isUpTran ((ind ←∧) ←∧) (∧∧d ltr) | no ¬p = no (λ {(←∧]←∧∧∧d ut) → ¬p ut}) 
-- isUpTran ((∧→ ind) ←∧) (∧∧d ltr) with (isUpTran (∧→ (ind ←∧)) ltr)
-- isUpTran ((∧→ ind) ←∧) (∧∧d ltr) | yes p = yes (∧→]←∧∧∧d p)
-- isUpTran ((∧→ ind) ←∧) (∧∧d ltr) | no ¬p = no (λ {(∧→]←∧∧∧d ut) → ¬p ut}) 
-- isUpTran (∧→ ind) (∧∧d ltr) with (isUpTran (∧→ (∧→ ind)) ltr)
-- isUpTran (∧→ ind) (∧∧d ltr) | yes p = yes (∧→∧∧d p)
-- isUpTran (∧→ ind) (∧∧d ltr) | no ¬p = no (λ {(∧→∧∧d ut) → ¬p ut})
-- isUpTran ↓ (¬∧∧d ltr) = no (λ ())
-- isUpTran (ind ←∧) (¬∧∧d ltr) with (isUpTran ((ind ←∧) ←∧) ltr)
-- isUpTran (ind ←∧) (¬∧∧d ltr) | yes p = yes (←∧¬∧∧d p)
-- isUpTran (ind ←∧) (¬∧∧d ltr) | no ¬p = no (λ {(←∧¬∧∧d ut) → ¬p ut})
-- isUpTran (∧→ ↓) (¬∧∧d ltr) = no (λ ())
-- isUpTran (∧→ (ind ←∧)) (¬∧∧d ltr) with (isUpTran ((∧→ ind) ←∧) ltr)
-- isUpTran (∧→ (ind ←∧)) (¬∧∧d ltr) | yes p = yes (∧→[←∧¬∧∧d p)
-- isUpTran (∧→ (ind ←∧)) (¬∧∧d ltr) | no ¬p = no (λ {(∧→[←∧¬∧∧d ut) → ¬p ut})
-- isUpTran (∧→ (∧→ ind)) (¬∧∧d ltr) with (isUpTran (∧→ ind) ltr)
-- isUpTran (∧→ (∧→ ind)) (¬∧∧d ltr) | yes p = yes (∧→[∧→¬∧∧d p)
-- isUpTran (∧→ (∧→ ind)) (¬∧∧d ltr) | no ¬p = no (λ {(∧→[∧→¬∧∧d ut) → ¬p ut})
-- isUpTran ↓ (∨∨d ltr) = no (λ ())
-- isUpTran (↓ ←∨) (∨∨d ltr) = no (λ ())
-- isUpTran ((ind ←∨) ←∨) (∨∨d ltr) with (isUpTran (ind ←∨) ltr)
-- isUpTran ((ind ←∨) ←∨) (∨∨d ltr) | yes p = yes (←∨]←∨∨∨d p)
-- isUpTran ((ind ←∨) ←∨) (∨∨d ltr) | no ¬p = no (λ {(←∨]←∨∨∨d ut) → ¬p ut}) 
-- isUpTran ((∨→ ind) ←∨) (∨∨d ltr) with (isUpTran (∨→ (ind ←∨)) ltr)
-- isUpTran ((∨→ ind) ←∨) (∨∨d ltr) | yes p = yes (∨→]←∨∨∨d p)
-- isUpTran ((∨→ ind) ←∨) (∨∨d ltr) | no ¬p = no (λ {(∨→]←∨∨∨d ut) → ¬p ut}) 
-- isUpTran (∨→ ind) (∨∨d ltr) with (isUpTran (∨→ (∨→ ind)) ltr)
-- isUpTran (∨→ ind) (∨∨d ltr) | yes p = yes (∨→∨∨d p)
-- isUpTran (∨→ ind) (∨∨d ltr) | no ¬p = no (λ {(∨→∨∨d ut) → ¬p ut})
-- isUpTran ↓ (¬∨∨d ltr) = no (λ ())
-- isUpTran (ind ←∨) (¬∨∨d ltr) with (isUpTran ((ind ←∨) ←∨) ltr)
-- isUpTran (ind ←∨) (¬∨∨d ltr) | yes p = yes (←∨¬∨∨d p)
-- isUpTran (ind ←∨) (¬∨∨d ltr) | no ¬p = no (λ {(←∨¬∨∨d ut) → ¬p ut})
-- isUpTran (∨→ ↓) (¬∨∨d ltr) = no (λ ())
-- isUpTran (∨→ (ind ←∨)) (¬∨∨d ltr) with (isUpTran ((∨→ ind) ←∨) ltr)
-- isUpTran (∨→ (ind ←∨)) (¬∨∨d ltr) | yes p = yes (∨→[←∨¬∨∨d p)
-- isUpTran (∨→ (ind ←∨)) (¬∨∨d ltr) | no ¬p = no (λ {(∨→[←∨¬∨∨d ut) → ¬p ut})
-- isUpTran (∨→ (∨→ ind)) (¬∨∨d ltr) with (isUpTran (∨→ ind) ltr)
-- isUpTran (∨→ (∨→ ind)) (¬∨∨d ltr) | yes p = yes (∨→[∨→¬∨∨d p)
-- isUpTran (∨→ (∨→ ind)) (¬∨∨d ltr) | no ¬p = no (λ {(∨→[∨→¬∨∨d ut) → ¬p ut})
-- isUpTran ↓ (∂∂d ltr) = no (λ ())
-- isUpTran (↓ ←∂) (∂∂d ltr) = no (λ ())
-- isUpTran ((ind ←∂) ←∂) (∂∂d ltr) with (isUpTran (ind ←∂) ltr)
-- isUpTran ((ind ←∂) ←∂) (∂∂d ltr) | yes p = yes (←∂]←∂∂∂d p)
-- isUpTran ((ind ←∂) ←∂) (∂∂d ltr) | no ¬p = no (λ {(←∂]←∂∂∂d ut) → ¬p ut})
-- isUpTran ((∂→ ind) ←∂) (∂∂d ltr) with (isUpTran (∂→ (ind ←∂)) ltr)
-- isUpTran ((∂→ ind) ←∂) (∂∂d ltr) | yes p = yes (∂→]←∂∂∂d p)
-- isUpTran ((∂→ ind) ←∂) (∂∂d ltr) | no ¬p = no (λ {(∂→]←∂∂∂d ut) → ¬p ut})
-- isUpTran (∂→ ind) (∂∂d ltr) with (isUpTran (∂→ (∂→ ind)) ltr)
-- isUpTran (∂→ ind) (∂∂d ltr) | yes p = yes (∂→∂∂d p)
-- isUpTran (∂→ ind) (∂∂d ltr) | no ¬p = no (λ {(∂→∂∂d ut) → ¬p ut})
-- isUpTran ↓ (¬∂∂d ltr) = no (λ ())
-- isUpTran (ind ←∂) (¬∂∂d ltr) with (isUpTran ((ind ←∂) ←∂) ltr)
-- isUpTran (ind ←∂) (¬∂∂d ltr) | yes p = yes (←∂¬∂∂d p)
-- isUpTran (ind ←∂) (¬∂∂d ltr) | no ¬p = no (λ {(←∂¬∂∂d ut) → ¬p ut})
-- isUpTran (∂→ ↓) (¬∂∂d ltr) = no (λ ())
-- isUpTran (∂→ (ind ←∂)) (¬∂∂d ltr) with (isUpTran ((∂→ ind) ←∂) ltr)
-- isUpTran (∂→ (ind ←∂)) (¬∂∂d ltr) | yes p = yes (∂→[←∂¬∂∂d p)
-- isUpTran (∂→ (ind ←∂)) (¬∂∂d ltr) | no ¬p = no (λ {(∂→[←∂¬∂∂d ut) → ¬p ut})
-- isUpTran (∂→ (∂→ ind)) (¬∂∂d ltr) with (isUpTran (∂→ ind) ltr)
-- isUpTran (∂→ (∂→ ind)) (¬∂∂d ltr) | yes p = yes (∂→[∂→¬∂∂d p)
-- isUpTran (∂→ (∂→ ind)) (¬∂∂d ltr) | no ¬p = no (λ {(∂→[∂→¬∂∂d ut) → ¬p ut})


-- indLow⇒UpTran : ∀ {i u rll ll n dt df} → (ind : IndexLL (τ {i} {u} {n} {dt} df) ll)
--                 → (ltr : LLTr {i} {u} rll ll) → UpTran ind ltr
-- indLow⇒UpTran ↓ I = indI
-- indLow⇒UpTran (ind ←∧) I = indI
-- indLow⇒UpTran (ind ←∧) (∧c ltr) = ←∧∧c r where
--   r = indLow⇒UpTran (∧→ ind) ltr
-- indLow⇒UpTran ((ind ←∧) ←∧) (∧∧d ltr) = ←∧]←∧∧∧d r where
--   r = indLow⇒UpTran (ind ←∧) ltr
-- indLow⇒UpTran ((∧→ ind) ←∧) (∧∧d ltr) = ∧→]←∧∧∧d r where
--   r = indLow⇒UpTran (∧→ (ind ←∧)) ltr
-- indLow⇒UpTran (ind ←∧) (¬∧∧d ltr) = ←∧¬∧∧d r where
--   r = indLow⇒UpTran ((ind ←∧) ←∧) ltr
-- indLow⇒UpTran (∧→ ind) I = indI
-- indLow⇒UpTran (∧→ ind) (∧c ltr) = ∧→∧c r where
--   r = indLow⇒UpTran (ind ←∧) ltr
-- indLow⇒UpTran (∧→ ind) (∧∧d ltr) = ∧→∧∧d r where
--   r = indLow⇒UpTran (∧→ (∧→ ind)) ltr
-- indLow⇒UpTran (∧→ (ind ←∧)) (¬∧∧d ltr) = ∧→[←∧¬∧∧d r where
--   r = indLow⇒UpTran ((∧→ ind) ←∧) ltr
-- indLow⇒UpTran (∧→ (∧→ ind)) (¬∧∧d ltr) = ∧→[∧→¬∧∧d r where
--   r = indLow⇒UpTran (∧→ ind) ltr
-- indLow⇒UpTran (ind ←∨) I = indI
-- indLow⇒UpTran (ind ←∨) (∨c ltr) = ←∨∨c r where
--   r = indLow⇒UpTran (∨→ ind) ltr
-- indLow⇒UpTran ((ind ←∨) ←∨) (∨∨d ltr) = ←∨]←∨∨∨d r where
--   r = indLow⇒UpTran (ind ←∨) ltr
-- indLow⇒UpTran ((∨→ ind) ←∨) (∨∨d ltr) = ∨→]←∨∨∨d r where
--   r = indLow⇒UpTran (∨→ (ind ←∨)) ltr
-- indLow⇒UpTran (ind ←∨) (¬∨∨d ltr) = ←∨¬∨∨d r where
--   r = indLow⇒UpTran ((ind ←∨) ←∨) ltr
-- indLow⇒UpTran (∨→ ind) I = indI
-- indLow⇒UpTran (∨→ ind) (∨c ltr) = ∨→∨c r where
--   r = indLow⇒UpTran (ind ←∨) ltr
-- indLow⇒UpTran (∨→ ind) (∨∨d ltr) = ∨→∨∨d r where
--   r = indLow⇒UpTran (∨→ (∨→ ind)) ltr
-- indLow⇒UpTran (∨→ (ind ←∨)) (¬∨∨d ltr) = ∨→[←∨¬∨∨d r where
--   r = indLow⇒UpTran ((∨→ ind) ←∨) ltr
-- indLow⇒UpTran (∨→ (∨→ ind)) (¬∨∨d ltr) = ∨→[∨→¬∨∨d r where
--   r = indLow⇒UpTran (∨→ ind) ltr
-- indLow⇒UpTran (ind ←∂) I = indI
-- indLow⇒UpTran (ind ←∂) (∂c ltr) = ←∂∂c r where
--   r = indLow⇒UpTran (∂→ ind) ltr
-- indLow⇒UpTran ((ind ←∂) ←∂) (∂∂d ltr) = ←∂]←∂∂∂d r where
--   r = indLow⇒UpTran (ind ←∂) ltr
-- indLow⇒UpTran ((∂→ ind) ←∂) (∂∂d ltr) = ∂→]←∂∂∂d r where
--   r = indLow⇒UpTran (∂→ (ind ←∂)) ltr
-- indLow⇒UpTran (ind ←∂) (¬∂∂d ltr) = ←∂¬∂∂d r where
--   r = indLow⇒UpTran ((ind ←∂) ←∂) ltr
-- indLow⇒UpTran (∂→ ind) I = indI
-- indLow⇒UpTran (∂→ ind) (∂c ltr) = ∂→∂c r where
--   r = indLow⇒UpTran (ind ←∂) ltr
-- indLow⇒UpTran (∂→ ind) (∂∂d ltr) = ∂→∂∂d r where
--   r = indLow⇒UpTran (∂→ (∂→ ind)) ltr
-- indLow⇒UpTran (∂→ (ind ←∂)) (¬∂∂d ltr) = ∂→[←∂¬∂∂d r where
--   r = indLow⇒UpTran ((∂→ ind) ←∂) ltr
-- indLow⇒UpTran (∂→ (∂→ ind)) (¬∂∂d ltr) = ∂→[∂→¬∂∂d r where
--   r = indLow⇒UpTran (∂→ ind) ltr



-- tran : ∀ {i u ll pll rll} → (ind : IndexLL pll ll) → (ltr : LLTr {i} {u} rll ll) → UpTran ind ltr
--        → IndexLL pll rll
-- tran ind I indI = ind 
-- tran ↓ (∂c ltr) () 
-- tran (ind ←∂) (∂c ltr) (←∂∂c ut) = tran (∂→ ind) ltr ut
-- tran (∂→ ind) (∂c ltr) (∂→∂c ut) =  tran (ind ←∂) ltr ut
-- tran ↓ (∨c ltr) () 
-- tran (ind ←∨) (∨c ltr) (←∨∨c ut) = tran (∨→ ind) ltr ut
-- tran (∨→ ind) (∨c ltr) (∨→∨c ut) = tran (ind ←∨) ltr ut
-- tran ↓ (∧c ltr) () 
-- tran (ind ←∧) (∧c ltr) (←∧∧c ut) = tran (∧→ ind) ltr ut
-- tran (∧→ ind) (∧c ltr) (∧→∧c ut) = tran (ind ←∧) ltr ut
-- tran ↓ (∧∧d ltr) () 
-- tran (↓ ←∧) (∧∧d ltr) () 
-- tran ((ind ←∧) ←∧) (∧∧d ltr) (←∧]←∧∧∧d ut) = tran (ind ←∧) ltr ut
-- tran ((∧→ ind) ←∧) (∧∧d ltr) (∧→]←∧∧∧d ut) = tran (∧→ (ind ←∧)) ltr ut
-- tran (∧→ ind) (∧∧d ltr) (∧→∧∧d ut) = tran (∧→ (∧→ ind)) ltr ut
-- tran ↓ (¬∧∧d ltr) () 
-- tran (ind ←∧) (¬∧∧d ltr) (←∧¬∧∧d ut) = tran ((ind ←∧) ←∧) ltr ut
-- tran (∧→ ↓) (¬∧∧d ltr) () 
-- tran (∧→ (ind ←∧)) (¬∧∧d ltr) (∧→[←∧¬∧∧d ut) = tran ((∧→ ind) ←∧) ltr ut
-- tran (∧→ (∧→ ind)) (¬∧∧d ltr) (∧→[∧→¬∧∧d ut) = tran (∧→ ind) ltr ut
-- tran ↓ (∨∨d ltr) () 
-- tran (↓ ←∨) (∨∨d ltr) () 
-- tran ((ind ←∨) ←∨) (∨∨d ltr) (←∨]←∨∨∨d ut) = tran (ind ←∨) ltr ut
-- tran ((∨→ ind) ←∨) (∨∨d ltr) (∨→]←∨∨∨d ut) = tran (∨→ (ind ←∨)) ltr ut
-- tran (∨→ ind) (∨∨d ltr) (∨→∨∨d ut) = tran (∨→ (∨→ ind)) ltr ut
-- tran ↓ (¬∨∨d ltr) () 
-- tran (ind ←∨) (¬∨∨d ltr) (←∨¬∨∨d ut) = tran ((ind ←∨) ←∨) ltr ut
-- tran (∨→ ↓) (¬∨∨d ltr) () 
-- tran (∨→ (ind ←∨)) (¬∨∨d ltr) (∨→[←∨¬∨∨d ut) = tran ((∨→ ind) ←∨) ltr ut
-- tran (∨→ (∨→ ind)) (¬∨∨d ltr) (∨→[∨→¬∨∨d ut) = tran (∨→ ind) ltr ut
-- tran ↓ (∂∂d ltr) () 
-- tran (↓ ←∂) (∂∂d ltr) () 
-- tran ((ind ←∂) ←∂) (∂∂d ltr) (←∂]←∂∂∂d ut) = tran (ind ←∂) ltr ut
-- tran ((∂→ ind) ←∂) (∂∂d ltr) (∂→]←∂∂∂d ut) = tran (∂→ (ind ←∂)) ltr ut
-- tran (∂→ ind) (∂∂d ltr) (∂→∂∂d ut) = tran (∂→ (∂→ ind)) ltr ut
-- tran ↓ (¬∂∂d ltr) () 
-- tran (ind ←∂) (¬∂∂d ltr) (←∂¬∂∂d ut) = tran ((ind ←∂) ←∂) ltr ut
-- tran (∂→ ↓) (¬∂∂d ltr) () 
-- tran (∂→ (ind ←∂)) (¬∂∂d ltr) (∂→[←∂¬∂∂d ut) = tran ((∂→ ind) ←∂) ltr ut
-- tran (∂→ (∂→ ind)) (¬∂∂d ltr) (∂→[∂→¬∂∂d ut) = tran (∂→ ind) ltr ut


-- tr-ltr-morph : ∀ {i u ll pll orll} → ∀ frll → (ind : IndexLL pll ll) → (ltr : LLTr {i} {u} orll ll) → (rvT : UpTran ind ltr) → LLTr (replLL orll (tran ind ltr rvT) frll) (replLL ll ind frll)
-- tr-ltr-morph frll ↓ .I indI = I
-- tr-ltr-morph frll (ind ←∧) I indI = I
-- tr-ltr-morph frll (ind ←∧) (∧c ltr) (←∧∧c rvT) with tr-ltr-morph frll (∧→ ind) ltr rvT
-- ... | r = ∧c r
-- tr-ltr-morph frll ((ind ←∧) ←∧) (∧∧d ltr) (←∧]←∧∧∧d rvT) with tr-ltr-morph frll (ind ←∧) ltr rvT
-- ... | r = ∧∧d r
-- tr-ltr-morph frll ((∧→ ind) ←∧) (∧∧d ltr) (∧→]←∧∧∧d rvT) with tr-ltr-morph frll (∧→ (ind ←∧)) ltr rvT
-- ... | r = ∧∧d r
-- tr-ltr-morph frll (ind ←∧) (¬∧∧d ltr) (←∧¬∧∧d rvT) with tr-ltr-morph frll ((ind ←∧) ←∧) ltr rvT
-- ... | r = ¬∧∧d r
-- tr-ltr-morph frll (∧→ ind) I indI = I
-- tr-ltr-morph frll (∧→ ind) (∧c ltr) (∧→∧c rvT) with tr-ltr-morph frll (ind ←∧) ltr rvT
-- ... | r = ∧c r
-- tr-ltr-morph frll (∧→ ind) (∧∧d ltr) (∧→∧∧d rvT) with tr-ltr-morph frll (∧→ (∧→ ind)) ltr rvT
-- ... | r = ∧∧d r
-- tr-ltr-morph frll (∧→ (ind ←∧)) (¬∧∧d ltr) (∧→[←∧¬∧∧d rvT) with tr-ltr-morph frll ((∧→ ind) ←∧) ltr rvT
-- ... | r = ¬∧∧d r
-- tr-ltr-morph frll (∧→ (∧→ ind)) (¬∧∧d ltr) (∧→[∧→¬∧∧d rvT)  with tr-ltr-morph frll (∧→ ind) ltr rvT
-- ... | r = ¬∧∧d r
-- tr-ltr-morph frll (ind ←∨) I indI = I
-- tr-ltr-morph frll (ind ←∨) (∨c ltr) (←∨∨c rvT) with tr-ltr-morph frll (∨→ ind) ltr rvT
-- ... | r = ∨c r
-- tr-ltr-morph frll ((ind ←∨) ←∨) (∨∨d ltr) (←∨]←∨∨∨d rvT) with tr-ltr-morph frll (ind ←∨) ltr rvT
-- ... | r = ∨∨d r
-- tr-ltr-morph frll ((∨→ ind) ←∨) (∨∨d ltr) (∨→]←∨∨∨d rvT) with tr-ltr-morph frll (∨→ (ind ←∨)) ltr rvT
-- ... | r = ∨∨d r
-- tr-ltr-morph frll (ind ←∨) (¬∨∨d ltr) (←∨¬∨∨d rvT) with tr-ltr-morph frll ((ind ←∨) ←∨) ltr rvT
-- ... | r = ¬∨∨d r
-- tr-ltr-morph frll (∨→ ind) I indI = I
-- tr-ltr-morph frll (∨→ ind) (∨c ltr) (∨→∨c rvT) with tr-ltr-morph frll (ind ←∨) ltr rvT
-- ... | r = ∨c r
-- tr-ltr-morph frll (∨→ ind) (∨∨d ltr) (∨→∨∨d rvT) with tr-ltr-morph frll (∨→ (∨→ ind)) ltr rvT
-- ... | r = ∨∨d r
-- tr-ltr-morph frll (∨→ (ind ←∨)) (¬∨∨d ltr) (∨→[←∨¬∨∨d rvT) with tr-ltr-morph frll ((∨→ ind) ←∨) ltr rvT
-- ... | r = ¬∨∨d r
-- tr-ltr-morph frll (∨→ (∨→ ind)) (¬∨∨d ltr) (∨→[∨→¬∨∨d rvT)  with tr-ltr-morph frll (∨→ ind) ltr rvT
-- ... | r = ¬∨∨d r
-- tr-ltr-morph frll (ind ←∂) I indI = I
-- tr-ltr-morph frll (ind ←∂) (∂c ltr) (←∂∂c rvT) with tr-ltr-morph frll (∂→ ind) ltr rvT
-- ... | r = ∂c r
-- tr-ltr-morph frll ((ind ←∂) ←∂) (∂∂d ltr) (←∂]←∂∂∂d rvT) with tr-ltr-morph frll (ind ←∂) ltr rvT
-- ... | r = ∂∂d r
-- tr-ltr-morph frll ((∂→ ind) ←∂) (∂∂d ltr) (∂→]←∂∂∂d rvT) with tr-ltr-morph frll (∂→ (ind ←∂)) ltr rvT
-- ... | r = ∂∂d r
-- tr-ltr-morph frll (ind ←∂) (¬∂∂d ltr) (←∂¬∂∂d rvT) with tr-ltr-morph frll ((ind ←∂) ←∂) ltr rvT
-- ... | r = ¬∂∂d r
-- tr-ltr-morph frll (∂→ ind) I indI = I
-- tr-ltr-morph frll (∂→ ind) (∂c ltr) (∂→∂c rvT) with tr-ltr-morph frll (ind ←∂) ltr rvT
-- ... | r = ∂c r
-- tr-ltr-morph frll (∂→ ind) (∂∂d ltr) (∂→∂∂d rvT) with tr-ltr-morph frll (∂→ (∂→ ind)) ltr rvT
-- ... | r = ∂∂d r
-- tr-ltr-morph frll (∂→ (ind ←∂)) (¬∂∂d ltr) (∂→[←∂¬∂∂d rvT) with tr-ltr-morph frll ((∂→ ind) ←∂) ltr rvT
-- ... | r = ¬∂∂d r
-- tr-ltr-morph frll (∂→ (∂→ ind)) (¬∂∂d ltr) (∂→[∂→¬∂∂d rvT)  with tr-ltr-morph frll (∂→ ind) ltr rvT
-- ... | r = ¬∂∂d r




