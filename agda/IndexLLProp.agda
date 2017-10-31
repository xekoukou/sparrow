-- {-# OPTIONS --show-implicit #-}

module IndexLLProp where

open import Common
open import LinLogic
open import Data.Maybe
import Relation.Binary.HeterogeneousEquality
open import Relation.Binary.PropositionalEquality using (trans ; sym ; subst ; cong ; subst₂)
open import Data.Sum

data _≅ᵢ_ {i u gll} : ∀{fll ll} → IndexLL {i} {u} gll ll → IndexLL {i} {u} fll ll → Set (lsuc u) where
  instance 
    ≅ᵢ↓ :  ↓ ≅ᵢ ↓
    ≅ᵢic : ∀{fll ict ll tll il} → ∀{{eq}} → {sind : IndexLL gll ll} → {bind : IndexLL fll ll} → {{ieq : sind ≅ᵢ bind}}
           → _≅ᵢ_ {ll = il[ il ]} (ic tll ict sind {{eq}}) (ic tll ict bind)



≅ᵢ-spec : ∀{i u ll ict tll il gll fll} → ∀{{eq}} → {sind : IndexLL {i} {u} gll ll}
          → {bind : IndexLL fll ll} → _≅ᵢ_ {ll = il[ il ]} (ic tll ict sind {{eq}}) (ic tll ict bind)
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
    ≤ᵢic : ∀{ll ict tll il} → ∀{{eq}} → {sind : IndexLL gll ll} → {bind : IndexLL fll ll} → {{ieq : sind ≤ᵢ bind}}
           → _≤ᵢ_ {ll = il[ il ]} (ic tll ict sind {{eq}}) (ic tll ict bind)

module _ where

  open import Relation.Binary.PropositionalEquality

  ≤ᵢ-spec : ∀{i u ll ict tll il gll fll} → ∀{{eq}} → {sind : IndexLL {i} {u} gll ll}
            → {bind : IndexLL fll ll} → _≤ᵢ_ {ll = il[ il ]} (ic tll ict sind {{eq}}) (ic tll ict bind)
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
  
    isLTi-abs1 : ∀{u i ll tll ict il rll gll ica icb} → ∀{{eq}} → ∀ a b
                 → ica ≡ ic {i} {u} {rll} {ll = ll} {il} tll ict a {{eq}}
                 → icb ≡ ic {_} {_} {gll} {ll = ll} tll ict b
                 → Dec (a ≤ᵢ b)
                 → Dec (ica ≤ᵢ icb)
    isLTi-abs1 a b refl refl (yes p) = yes (≤ᵢic {{ieq = p}})
    isLTi-abs1 a b refl refl (no ¬p) = no (λ p → ¬p (≤ᵢ-spec p))


    isLTi-abs : ∀{u i lla tlla icta il llb tllb ictb rll gll ica icb} → ∀{{eqa eqb}} → ∀ a b
                → ica ≡ ic {i} {u} {rll} {ll = lla} {il} tlla icta a {{eqa}}
                → icb ≡ ic {_} {_} {gll} {ll = llb} tllb ictb b {{eqb}}
               → IndU icta ictb eqa eqb
                → Dec (ica ≤ᵢ icb)
    isLTi-abs a b iceqa iceqb (ictEq _ _ _ refl) = isLTi-abs1 a b iceqa iceqb (isLTi a b)
    isLTi-abs a b refl refl (ict¬Eq ¬icteq reqa reqb) = no λ { ≤ᵢic → ¬icteq refl}
    
    isLTi : ∀{i u gll ll fll} → (a : IndexLL {i} {u} gll ll) → (b : IndexLL fll ll) → Dec (a ≤ᵢ b)
    isLTi ↓ b = yes ≤ᵢ↓
    isLTi (ic _ _ a) ↓ = no (λ ())
    isLTi (ic _ _ a) (ic _ _ b) = isLTi-abs a b refl refl compIndU




module _ where
  mutual 
    isEqᵢ-abs1 : ∀{u i ll tll ict il rll} → ∀{{eq}} → {a : IndexLL {i} {u} rll ll} → {b : IndexLL rll ll} → Dec (a ≡ b) → Dec (ic {ll = ll} {il} tll ict a {{eq}} ≡ ic {ll = ll} tll ict b)
    isEqᵢ-abs1 (yes refl) = yes refl
    isEqᵢ-abs1 (no ¬p) = no λ { refl → ¬p refl}

    isEqᵢ-abs : ∀{u i lla tlla icta il llb tllb ictb rll ica icb} → ∀{{eqa eqb}} → ∀ a b
            → ica ≡ ic {i} {u} {rll} {ll = lla} {il} tlla icta a {{eqa}}
            → icb ≡ ic {i} {u} {rll} {ll = llb} tllb ictb b {{eqb}}
            → IndU icta ictb eqa eqb
            → Dec (ica ≡ icb)
    isEqᵢ-abs a b refl refl (ictEq _ _ _ refl) = isEqᵢ-abs1 (isEqᵢ a b)
    isEqᵢ-abs a b refl refl (ict¬Eq ¬icteq reqa reqb) = no λ { refl → ¬icteq refl}
    
    isEqᵢ : ∀{u i ll rll} → (a : IndexLL {i} {u} rll ll) → (b : IndexLL rll ll) → Dec (a ≡ b)
    isEqᵢ ↓ ↓ = yes refl
    isEqᵢ ↓ (ic _ _ _) = no λ ()
    isEqᵢ (ic _ _ _) ↓ = no λ ()
    isEqᵢ (ic _ _ a) (ic _ _ b) = isEqᵢ-abs a b refl refl compIndU
   


module _ where

  open import Data.Vec

  mutual

    indτ-le⇒ieq-abs : ∀{u i lla tlla icta il llb tllb ictb rll n dt df ica icb} → ∀{{eqa eqb}} → ∀ a b
            → ica ≡ ic {i} {u} {τ {n = n} {dt} df} {ll = lla} {il} tlla icta a {{eqa}}
            → icb ≡ ic {i} {u} {rll} {ll = llb} tllb ictb b {{eqb}}
            → {{ rl : ica ≤ᵢ icb }} 
            → IndU icta ictb eqa eqb
            → icb ≅ᵢ ica
    indτ-le⇒ieq-abs a b refl refl {{≤ᵢic}} (ictEq _ _ _ refl) = ≅ᵢic
    indτ-le⇒ieq-abs a b refl refl {{≤ᵢic}} (ict¬Eq ¬icteq reqa reqb) = ⊥-elim (¬icteq refl)

    instance
      indτ-le⇒ieq : ∀{i u rll ll n dt df} → {ind : IndexLL {i} {u} (τ {i} {u} {n} {dt} df) ll} → {ind2 : IndexLL rll ll} → {{rl : ind ≤ᵢ ind2}} → (ind2 ≅ᵢ ind)
      indτ-le⇒ieq {ind = ↓} {↓} = ≅ᵢ↓
      indτ-le⇒ieq {ind = ic _ _ _} {↓} {{()}}
      indτ-le⇒ieq {ind = (ic _ _ ind1)} {(ic _ _ ind2)} = indτ-le⇒ieq-abs ind1 ind2 refl refl compIndU



data Orderedᵢ {i u gll fll ll} (a : IndexLL {i} {u} gll ll) (b : IndexLL {i} {u} fll ll) : Set (lsuc u) where
  instance
    a≤ᵢb : {{rl : a ≤ᵢ b}} → Orderedᵢ a b
    b≤ᵢa : {{rl : b ≤ᵢ a}} → Orderedᵢ a b



ord-spec : ∀{i u rll ll ict tll il fll} → ∀{{eq}} → {emi : IndexLL {i} {u} fll ll}
           → {ind : IndexLL rll ll} → Orderedᵢ (ic {il = il} tll ict ind {{eq}}) (ic tll ict emi) → Orderedᵢ ind emi
ord-spec (a≤ᵢb {{rl = x}}) = a≤ᵢb {{rl = (≤ᵢ-spec x)}}
ord-spec (b≤ᵢa {{rl = x}}) = b≤ᵢa {{rl = (≤ᵢ-spec x)}}



ord-ext : ∀{i u rll ll ict tll il fll} → ∀{{eq}} → {emi : IndexLL {i} {u} fll ll}
           → {ind : IndexLL rll ll} → Orderedᵢ ind emi → Orderedᵢ (ic {il = il} tll ict ind {{eq}}) (ic tll ict emi)
ord-ext a≤ᵢb = a≤ᵢb
ord-ext b≤ᵢa = b≤ᵢa



ord-spec∘ord-ext≡id : ∀{i u ll ict tll il fll rll} → ∀{{eq}} → {ind : IndexLL {i} {u} fll ll} → {lind : IndexLL rll ll} → {{ ord : Orderedᵢ ind lind }} → ord-spec {ict = ict} {tll = tll} {il} {{eq}} (ord-ext {ict = ict} {tll = tll} ord) ≡ ord
ord-spec∘ord-ext≡id {{ord = a≤ᵢb}} = refl
ord-spec∘ord-ext≡id {{ord = b≤ᵢa}} = refl


≅⇒bord : ∀{i u rll pll ll}
              → {ind : IndexLL {i} {u} pll ll} {lind : IndexLL rll ll}
              → {{eq : lind ≅ᵢ ind}} → (ind ≤ᵢ lind) × (lind ≤ᵢ ind)
≅⇒bord {{eq = ≅ᵢ↓}} = ≤ᵢ↓ , ≤ᵢ↓
≅⇒bord {{eq = ≅ᵢic}} = ≤ᵢic {{ieq = (proj₁ r)}} , ≤ᵢic {{ieq = (proj₂ r)}} where
  r = ≅⇒bord


module _ where

  isOrdᵢ-abs : ∀{i u gll fll ll} → (a : IndexLL {i} {u} gll ll) → (b : IndexLL {i} {u} fll ll)
               → Dec (a ≤ᵢ b) → Dec (b ≤ᵢ a)
               → Dec (Orderedᵢ a b)
  isOrdᵢ-abs a b (yes p) r = yes (a≤ᵢb {{rl = p}})
  isOrdᵢ-abs a b (no ¬p) (yes p) = yes (b≤ᵢa {{rl = p}})
  isOrdᵢ-abs a b (no ¬p) (no ¬p₁) = no (λ { (a≤ᵢb {{rl = x}}) → ¬p x ; (b≤ᵢa {{rl = x}}) → ¬p₁ x})
  
  isOrdᵢ : ∀{i u gll fll ll} → (a : IndexLL {i} {u} gll ll) → (b : IndexLL {i} {u} fll ll)
           → Dec (Orderedᵢ a b)
  isOrdᵢ a b = isOrdᵢ-abs a b (isLTi a b) (isLTi b a) 




flipOrdᵢ : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
           → Orderedᵢ a b → Orderedᵢ b a
flipOrdᵢ a≤ᵢb = b≤ᵢa
flipOrdᵢ b≤ᵢa = a≤ᵢb


-- TODO Remove this ?
-- ¬lt¬gt⇒¬Ord : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
--               → ¬ (a ≤ᵢ b) → ¬ (b ≤ᵢ a) → ¬(Orderedᵢ a b)
-- ¬lt¬gt⇒¬Ord nlt ngt (a≤ᵢb {{rl = x}}) = nlt x
-- ¬lt¬gt⇒¬Ord nlt ngt (b≤ᵢa {{rl = x}}) = ngt x



ord⇒icteq : ∀{u i lla tlla icta il llb tllb ictb fll rll ica icb} → ∀{{eqa eqb}} → ∀ a b
       → (iceqa : ica ≡ ic {i} {u} {fll} {ll = lla} {il} tlla icta a {{eqa}})
       → (iceqb : icb ≡ ic {i} {u} {rll} {ll = llb} tllb ictb b {{eqb}})
       → {{ord : Orderedᵢ icb ica}}
       → icta ≡ ictb
ord⇒icteq a b refl refl {{a≤ᵢb {{≤ᵢic}}}} = refl
ord⇒icteq a b refl refl {{b≤ᵢa {{≤ᵢic}}}} = refl

instance
  indτ&Ord⇒ge : ∀{i u rll ll n dt df} → {ind : IndexLL (τ {i} {u} {n} {dt} df) ll}
                            {lind : IndexLL rll ll} → {{ord : Orderedᵢ ind lind}} → lind ≤ᵢ ind
  indτ&Ord⇒ge {ind = ind} {lind} {{a≤ᵢb}} = proj₂ ≅⇒bord
  indτ&Ord⇒ge {ind = ind} {lind} {{b≤ᵢa {{rl = rl}}}} = rl



-- a,c≤ᵢb⇒ordac : ∀{i u gll fll mll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL fll ll} → {c : IndexLL mll ll} → (a ≤ᵢ b) → (c ≤ᵢ b) → Orderedᵢ a c
-- a,c≤ᵢb⇒ordac ≤ᵢ↓ ltbc = a≤ᵢb ≤ᵢ↓
-- a,c≤ᵢb⇒ordac (≤ᵢic ltab) ≤ᵢ↓ = b≤ᵢa ≤ᵢ↓
-- a,c≤ᵢb⇒ordac (≤ᵢic ltab) (≤ᵢic ltcb) = ord-ext (a,c≤ᵢb⇒ordac ltab ltcb)


-- a≤ᵢb&¬ordac⇒¬ordbc : ∀{i u gll fll mll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL fll ll} → {c : IndexLL mll ll} → (a ≤ᵢ b) → ¬ Orderedᵢ a c → ¬ Orderedᵢ b c
-- a≤ᵢb&¬ordac⇒¬ordbc lt nord (a≤ᵢb x) = ⊥-elim (nord (a≤ᵢb (≤ᵢ-transitive lt x)))
-- a≤ᵢb&¬ordac⇒¬ordbc lt nord (b≤ᵢa x) = ⊥-elim (nord (a,c≤ᵢb⇒ordac lt x))



-- _-ᵢ_ : ∀ {i u pll cll ll} → (bind : IndexLL {i} {u} cll ll) → (sind : IndexLL pll ll) → (sind ≤ᵢ bind)
--        → IndexLL cll pll
-- (bind -ᵢ .↓) ≤ᵢ↓ = bind
-- ((ic _ _ bind) -ᵢ (ic _ _ sind)) (≤ᵢic lt) = (bind -ᵢ sind) lt


-- ind-ᵢind≡↓ : ∀ {i u pll ll} → {ind : IndexLL {i} {u} pll ll} → (rl : ind ≤ᵢ ind)
--        → (ind -ᵢ ind) rl ≡ ↓
-- ind-ᵢind≡↓ ≤ᵢ↓ = refl
-- ind-ᵢind≡↓ (≤ᵢic rl) = ind-ᵢind≡↓ rl





-- ind-rpl↓ : ∀{i u ll pll cll ell} → (ind : IndexLL {i} {u} pll ll)
--         → IndexLL cll (replLL ((ind -ᵢ ind) ≤ᵢ-reflexive) ell) → IndexLL cll ell
-- ind-rpl↓ {_} {_} {_} {pll} {cll} {ell} ind y
--   =  subst (λ x → x) (cong (λ x → IndexLL cll (replLL x ell)) (ind-ᵢind≡↓ {ind = ind} ≤ᵢ-reflexive)) y 



-- -- a≤ᵢb-morph : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll)
-- --              → (ind : IndexLL rll ll) → ∀ {frll} → (lt : emi ≤ᵢ ind)
-- --              → IndexLL (replLL ((ind -ᵢ emi) lt) frll) (replLL ind frll) 
-- -- a≤ᵢb-morph .↓ ind ≤ᵢ↓ = ↓
-- -- a≤ᵢb-morph (ic {tll = tll} {ict = ict} emi) (ic ind) (≤ᵢic lt) = ic {tll = tll} {ict = ict} (a≤ᵢb-morph emi ind lt)




-- -- module _ where

-- --   a≤ᵢb-morph-id-abs : ∀{i u ll tll ict rll}
-- --                → {ind : IndexLL {i} {u} rll ll}
-- --                → ∀ {w₁T} → (w₁ : w₁T ≡ rll)  -- w₁T : replLL ((ind -ᵢ ind) (≤ᵢ-reflexive ind)) rll
-- --                → ∀ {w₂T} → (w₂ : w₂T ≡ ll) -- w₂T : replLL li ind rl
-- --                → (w₃ : IndexLL w₁T w₂T) -- w₃ : (a≤ᵢb-morph ind ind (≤ᵢ-reflexive ind))
-- --                → (w₄ : subst₂ (λ x y → IndexLL x y) w₁ w₂ w₃ ≡ ind) -- recursive step
-- --                → subst₂ IndexLL w₁ 
-- --                    (cong (λ x → il[ expLLT x ict tll ]) w₂)
-- --                      (ic {tll = tll} {ict} w₃) ≡ ic {tll = tll} {ict} ind
-- --   a≤ᵢb-morph-id-abs refl refl _ refl = refl


-- --   a≤ᵢb-morph-id : ∀{i u ll rll}
-- --                → (ind : IndexLL {i} {u} rll ll)
-- --                → subst₂ (λ x y → IndexLL x y) (replLL-↓ {ell = rll} ind) (replLL-id ind) (a≤ᵢb-morph ind ind (≤ᵢ-reflexive ind)) ≡ ind
-- --   a≤ᵢb-morph-id ↓ = refl
-- --   a≤ᵢb-morph-id {rll = rll} (ic ind {{refl}}) = a≤ᵢb-morph-id-abs (replLL-↓ {ell = rll} ind) (replLL-id ind) (a≤ᵢb-morph ind ind (≤ᵢ-reflexive ind)) (a≤ᵢb-morph-id ind)



-- -- replLL-a≤b≡a : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll) → ∀ {gll}
-- --                → (ind : IndexLL rll ll) → ∀ {frll} → (lt : emi ≤ᵢ ind)
-- --                → replLL (a≤ᵢb-morph emi ind {frll = frll} lt) gll ≡ replLL emi gll
-- -- replLL-a≤b≡a .↓ ind ≤ᵢ↓ = refl
-- -- replLL-a≤b≡a (ic {tll = tll} {ict} emi) (ic ind) (≤ᵢic lt) = cong (λ x → il[ expLLT x ict tll ]) (replLL-a≤b≡a emi ind lt)



-- -- -- module _ where

-- -- --   mutual
  
-- -- --     ¬ord-morph-abs : ∀{u i lla tlla icta il eqa llb tllb ictb eqb fll rll frll ica icb} → ∀ a b
-- -- --               → ica ≡ ic {i} {u} {fll} {ll = lla} {tlla} {icta} {il} a {{eqa}}
-- -- --               → icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} {ictb} {il} b {{eqb}}
-- -- --               → ¬ Orderedᵢ icb ica
-- -- --               → IndU icta ictb eqa eqb
-- -- --               → IndexLL fll il[ expLLT (replLL b frll) ictb tllb ]
-- -- --     ¬ord-morph-abs {tllb = tllb} {ictb} {frll = frll} a b refl refl nord (ictEq _ _ _ refl)
-- -- --         = ic {ll = _} {tllb} {ictb} (¬ord-morph a b {frll = frll} (¬ord-spec nord))
-- -- --     ¬ord-morph-abs {icta = icta} {eqa = eqa} {eqb = eqb} {frll = frll} a b refl refl nord (ict¬Eq ¬icteq refl refl) = ic {tll
-- -- --         = replLL b frll} {ict = icta} a {{rexpLLT⇒req ¬icteq eqa eqb}}


-- -- --     ¬ord-morph : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll)
-- -- --                  → (ind : IndexLL rll ll) → ∀ {frll} → (nord : ¬ Orderedᵢ ind emi)
-- -- --                  → IndexLL fll (replLL ind frll)
-- -- --     ¬ord-morph emi ↓ nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
-- -- --     ¬ord-morph ↓ (ic ind) nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- --     ¬ord-morph (ic {ll = lle} {tlle} {icte} {il} emi {{eqe}}) (ic {ll = lli} {tlli} {icti} ind {{eqi}}) {frll} nord
-- -- --         = ¬ord-morph-abs emi ind refl refl nord compIndU


-- -- -- module _ where

-- -- -- mutual

-- -- --     ¬ord-morph-¬ord-ir-abs : ∀{u i lla tlla icta il eqa llb tllb ictb eqb fll rll ica icb frll} → ∀ a b
-- -- --       → (iceqa : ica ≡ ic {i} {u} {fll} {ll = lla} {tlla} {icta} {il} a {{eqa}})
-- -- --       → (iceqb : icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} {ictb} {il} b {{eqb}})
-- -- --       → (nord1 nord2 : ¬ Orderedᵢ icb ica)
-- -- --       → (w : IndU icta ictb eqa eqb)
-- -- --       →  ¬ord-morph-abs {frll = frll} a b iceqa iceqb nord1 w ≡ ¬ord-morph-abs a b iceqa iceqb nord2 w
-- -- --     ¬ord-morph-¬ord-ir-abs {tllb = tllb} {ictb} {frll = frll} a b refl refl nord1 nord2 (ictEq _ _ _ refl)
-- -- --         = cong (λ z → ic {ll = _} {tllb} {ictb} z) (¬ord-morph-¬ord-ir a b {frll} (¬ord-spec nord1) (¬ord-spec nord2))
-- -- --     ¬ord-morph-¬ord-ir-abs ica icb refl refl nord1 nord2 (ict¬Eq ¬icteq refl refl) = refl


-- -- --     ¬ord-morph-¬ord-ir : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll)
-- -- --                          → (ind : IndexLL rll ll) → ∀ {frll} → (nord nord2 : ¬ Orderedᵢ ind emi)
-- -- --                          → ¬ord-morph emi ind {frll} nord ≡ ¬ord-morph emi ind {frll} nord2
-- -- --     ¬ord-morph-¬ord-ir ↓ ind {frll} nord nord2 = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- --     ¬ord-morph-¬ord-ir (ic emi) ↓ {frll} nord nord2 = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
-- -- --     ¬ord-morph-¬ord-ir ice@(ic emi) ici@(ic ind) {frll} nord nord2 = ¬ord-morph-¬ord-ir-abs emi ind refl refl nord nord2 compIndU 



-- -- -- module _ where

-- -- --   mutual

-- -- --     replLL-¬ordab≡ba-abs : ∀{u i lla tlla icta il eqa llb tllb ictb eqb fll rll ica icb gll frll} → ∀ a b
-- -- --       → (iceqa : ica ≡ ic {i} {u} {fll} {ll = lla} {tlla} {icta} {il} a {{eqa}})
-- -- --       → (iceqb : icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} {ictb} {il} b {{eqb}})
-- -- --       → (nord : ¬ Orderedᵢ icb ica)
-- -- --       → (fnord : ¬ Orderedᵢ ica icb)
-- -- --       → ∀ w1 w2
-- -- --       → replLL
-- -- --           (¬ord-morph-abs {frll = frll} a b iceqa iceqb nord w1) gll
-- -- --         ≡
-- -- --         replLL
-- -- --           (¬ord-morph-abs {frll = gll} b a iceqb iceqa fnord w2) frll
-- -- --     replLL-¬ordab≡ba-abs {tllb = tllb} {ictb} {eqb} {gll = gll} {frll} a b refl refl nord fnord (ictEq _ _ _ refl) (ictEq _ _ _ refl)
-- -- --       =  cong (λ z → il[ expLLT z ictb tllb ])
-- -- --               (replLL-¬ordab≡ba a b (¬ord-spec nord) (¬ord-spec fnord))
-- -- --     replLL-¬ordab≡ba-abs a b iceqa iceqb nord fnord (ictEq icteq lleq tlleq eqeq) (ict¬Eq ¬icteq reqa reqb) = ⊥-elim (¬icteq (sym icteq))
-- -- --     replLL-¬ordab≡ba-abs a b iceqa iceqb nord fnord (ict¬Eq ¬icteq reqa reqb) (ictEq icteq lleq tlleq eqeq) = ⊥-elim (¬icteq (sym icteq))
-- -- --     replLL-¬ordab≡ba-abs {eqa = eqa} {eqb = eqb} a b refl refl nord fnord (ict¬Eq _ refl refl) (ict¬Eq ¬icteq refl refl) = cong il[_] (rexpLLT⇒req ¬icteq eqb eqa)


-- -- --     replLL-¬ordab≡ba : ∀{i u rll ll fll}
-- -- --       → (emi : IndexLL {i} {u} fll ll) → ∀ {gll}
-- -- --       → (ind : IndexLL rll ll) → ∀ {frll}
-- -- --       → (nord : ¬ Orderedᵢ ind emi)
-- -- --       → (fnord : ¬ Orderedᵢ emi ind)
-- -- --       → replLL (¬ord-morph emi ind {frll} nord) gll ≡ replLL (¬ord-morph ind emi {gll} fnord) frll
-- -- --     replLL-¬ordab≡ba ↓ ind nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- --     replLL-¬ordab≡ba (ic emi) ↓ nord fnord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
-- -- --     replLL-¬ordab≡ba ice@(ic emi) ici@(ic ind) nord fnord = replLL-¬ordab≡ba-abs emi ind refl refl nord fnord compIndU compIndU 




-- -- -- module _ where

-- -- --   mutual

-- -- --     lemma₁-¬ord-a≤ᵢb-abs : ∀{u i ll tll ict il eq llc tllc ictc fll rll pll ica icb ell} → ∀ a b c
-- -- --                → ∀ {icc eqc}
-- -- --                → ica ≡ ic {i} {u} {fll} {ll = ll} {tll} {ict} {il} a {{eq}}
-- -- --                → icb ≡ ic {i} {u} {rll} {ll = ll} {tll} {ict} {il} b {{eq}}
-- -- --                → icc ≡ ic {i} {u} {pll} {ll = llc} {tllc} {ictc} {expLLT (replLL b ell) ict tll} c {{eqc}}
-- -- --                → ∀ lt
-- -- --                → ¬ Orderedᵢ (ic {tll = tll} {ict} (a≤ᵢb-morph a b {ell} lt)) icc
-- -- --                → IndU ict ictc refl eqc
-- -- --                → IndexLL pll il[ il ]
-- -- --     lemma₁-¬ord-a≤ᵢb-abs {tll = tll} {ict} {eq = eq} {ell = ell} a b c iceqa iceqb refl lt nord (ictEq _ _ _ refl) = ic {tll = tll} {ict = ict} (lemma₁-¬ord-a≤ᵢb a b ell lt c (¬ord-spec nord)) {{eq}}
-- -- --     lemma₁-¬ord-a≤ᵢb-abs {ll = ll} {eq = eq} {ictc = ictc} a b c {eqc = eqc} iceqa iceqb iceqc lt nord (ict¬Eq ¬icteq refl refl) = ic {tll = ll} {ictc} c {{trans eq (sym (rexpLLT⇒req ¬icteq refl eqc))}}


-- -- --     lemma₁-¬ord-a≤ᵢb : ∀{i u ll pll rll fll}
-- -- --           → (emi : IndexLL {i} {u} fll ll)
-- -- --           → (ind : IndexLL rll ll) → ∀ ell → (lt : emi ≤ᵢ ind)
-- -- --           → (omi : IndexLL pll (replLL ind ell))
-- -- --           → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind {ell} lt) omi)
-- -- --           → IndexLL pll ll
-- -- --     lemma₁-¬ord-a≤ᵢb .↓ ind ell ≤ᵢ↓ omi nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
-- -- --     lemma₁-¬ord-a≤ᵢb .(ic _) .(ic _) ell (≤ᵢic lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- --     lemma₁-¬ord-a≤ᵢb ica@(ic a) icb@(ic b {{eq}}) ell (≤ᵢic lt) icc@(ic c) nord = lemma₁-¬ord-a≤ᵢb-abs {eq = eq} a b c refl refl refl lt nord compIndU



-- -- -- module _ where

-- -- -- mutual

-- -- --     ¬ord-morph⇒¬ord-abs : ∀{u i lla tlla icta il eqa llb tllb ictb eqb fll rll frll ica icb} → ∀ a b
-- -- --            → (iceqa : ica ≡ ic {i} {u} {fll} {ll = lla} {tlla} {icta} {il} a {{eqa}})
-- -- --            → (iceqb : icb ≡ ic {i} {u} {rll} {ll = llb} {tllb} {ictb} {il} b {{eqb}})
-- -- --            → (nord : ¬ Orderedᵢ icb ica)
-- -- --            → (w : IndU icta ictb eqa eqb)
-- -- --            →  ¬ Orderedᵢ (ic {tll = tllb} {ict = ictb} (a≤ᵢb-morph b b {frll = frll} (≤ᵢ-reflexive b)))
-- -- --                          (¬ord-morph-abs {frll = frll} a b iceqa iceqb nord w)
-- -- --     ¬ord-morph⇒¬ord-abs {frll = frll} a b refl refl nord (ictEq icteq lleq tlleq refl) = λ x → r (ord-spec x) where
-- -- --       r = ¬ord-morph⇒¬ord a b {frll} (¬ord-spec nord)
-- -- --     ¬ord-morph⇒¬ord-abs a b refl refl nord (ict¬Eq ¬icteq refl refl) = ¬ict⇒¬ord a (a≤ᵢb-morph b b (≤ᵢ-reflexive b)) refl refl ¬icteq
  
  
-- -- --     ¬ord-morph⇒¬ord : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll)
-- -- --           → (ind : IndexLL rll ll) → ∀ {frll} → (nord : ¬ Orderedᵢ ind emi)
-- -- --           → ¬ Orderedᵢ (a≤ᵢb-morph ind ind {frll} (≤ᵢ-reflexive ind)) (¬ord-morph emi ind nord)
-- -- --     ¬ord-morph⇒¬ord ↓ ind nord = λ _ → nord (b≤ᵢa ≤ᵢ↓)
-- -- --     ¬ord-morph⇒¬ord (ic emi) ↓ nord = λ _ → nord (a≤ᵢb ≤ᵢ↓)
-- -- --     ¬ord-morph⇒¬ord (ic emi) (ic ind) nord = ¬ord-morph⇒¬ord-abs emi ind refl refl nord compIndU



-- -- -- module _ where

-- -- --   mutual

-- -- --     rlemma₁⇒¬ord-abs : ∀{u i ll tll ict il eq llc tllc ictc fll rll pll ica icb ell} → ∀ a b c
-- -- --            → ∀{eqc icc}
-- -- --            → (iceqa : ica ≡ ic {i} {u} {fll} {ll = ll} {tll} {ict} {il} a {{eq}})
-- -- --            → (iceqb : icb ≡ ic {i} {u} {rll} {ll = ll} {tll} {ict} {il} b {{eq}})
-- -- --            → (iceqc : icc ≡ ic {i} {u} {pll} {ll = llc} {tllc} {ictc} {expLLT (replLL b ell) ict tll} c {{eqc}})
-- -- --            → ∀ lt
-- -- --            → (nord : ¬ Orderedᵢ (ic {tll = tll} {ict} (a≤ᵢb-morph a b {ell} lt)) icc)
-- -- --            → (w : IndU ict ictc refl eqc)
-- -- --            → ¬ Orderedᵢ ica
-- -- --                         (lemma₁-¬ord-a≤ᵢb-abs a b c iceqa iceqb iceqc lt nord w)
-- -- --     rlemma₁⇒¬ord-abs {ell = ell} a b c refl refl refl lt nord (ictEq icteq lleq tlleq refl) = λ x → r (ord-spec x) where
-- -- --       r = rlemma₁⇒¬ord a b ell lt c (¬ord-spec nord)
-- -- --     rlemma₁⇒¬ord-abs a b c refl refl refl lt nord (ict¬Eq ¬icteq refl refl) = ¬ict⇒¬ord c a refl refl (λ x → ¬icteq (sym x))

-- -- --     rlemma₁⇒¬ord : ∀{i u ll pll rll fll}
-- -- --        → (emi : IndexLL {i} {u} fll ll)
-- -- --        → (ind : IndexLL rll ll) → ∀ ell → (lt : emi ≤ᵢ ind)
-- -- --        → (omi : IndexLL pll (replLL ind ell))
-- -- --        → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind lt) omi)
-- -- --        → ¬ Orderedᵢ emi (lemma₁-¬ord-a≤ᵢb emi ind ell lt omi nord)
-- -- --     rlemma₁⇒¬ord .↓ ind ell ≤ᵢ↓ omi nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
-- -- --     rlemma₁⇒¬ord .(ic _) .(ic _) ell (≤ᵢic lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- --     rlemma₁⇒¬ord (ic emi) (ic ind) ell (≤ᵢic lt) (ic omi) nord = rlemma₁⇒¬ord-abs emi ind omi refl refl refl lt nord compIndU



-- -- -- module _ where

-- -- --   mutual 

-- -- --     ¬ord-morph$lemma₁≡I-abs1 : ∀{u i ll tll ict il eq fll rll pll ica icb ell} → ∀ a b c
-- -- --                → ∀ {icc}
-- -- --                → (iceqa : ica ≡ ic {i} {u} {fll} {ll = ll} {tll} {ict} {il} a {{eq}})
-- -- --                → (iceqb : icb ≡ ic {i} {u} {rll} {ll = ll} {tll} {ict} {il} b {{eq}})
-- -- --                → (iceqc : icc ≡ ic {i} {u} {pll} {ll = replLL b ell} {tll} {ict} {expLLT (replLL b ell) ict tll} c {{refl}})
-- -- --                → ∀ lt
-- -- --                → (nord : ¬ Orderedᵢ (ic {tll = tll} {ict} (a≤ᵢb-morph a b {ell} lt)) (ic {tll = tll} {ict} c {{refl}}))
-- -- --                → (w : IndU ict ict eq eq)
-- -- --                → ¬ord-morph-abs
-- -- --                    (lemma₁-¬ord-a≤ᵢb a b ell lt c (λ ord → nord (ord-ext ord))) b refl refl
-- -- --                      (a≤ᵢb&¬ordac⇒¬ordbc (≤ᵢic lt)
-- -- --                        (λ x → rlemma₁⇒¬ord a b ell lt c (λ ord → nord (ord-ext ord)) (ord-spec x))) w
-- -- --                  ≡ ic {tll = tll} {ict} c {{refl}}
-- -- --     ¬ord-morph$lemma₁≡I-abs1 {ell = ell} a b c refl refl refl lt nord (ictEq icteq lleq tlleq refl) = {!r!} where
-- -- --       r = ¬ord-morph$lemma₁≡I ell a b lt c (¬ord-spec nord)
-- -- --     ¬ord-morph$lemma₁≡I-abs1 a b c refl refl refl lt nord (ict¬Eq ¬icteq reqa reqb) = {!!}          


-- -- --     ¬ord-morph$lemma₁≡I-abs : ∀{u i ll tll ict il eq llc tllc ictc fll rll pll ica icb ell} → ∀ a b c
-- -- --                → ∀ {icc eqc}
-- -- --                → (iceqa : ica ≡ ic {i} {u} {fll} {ll = ll} {tll} {ict} {il} a {{eq}})
-- -- --                → (iceqb : icb ≡ ic {i} {u} {rll} {ll = ll} {tll} {ict} {il} b {{eq}})
-- -- --                → (iceqc : icc ≡ ic {i} {u} {pll} {ll = llc} {tllc} {ictc} {expLLT (replLL b ell) ict tll} c {{eqc}})
-- -- --                → ∀ lt
-- -- --                → (nord : ¬ Orderedᵢ (ic {tll = tll} {ict} (a≤ᵢb-morph a b {ell} lt)) (ic c))
-- -- --                → (w : IndU ict ictc refl eqc)
-- -- --                → ¬ord-morph
-- -- --                    (lemma₁-¬ord-a≤ᵢb-abs {eq = eq} {ell = ell} a b c refl refl refl lt nord w) (ic b) {frll = ell} (a≤ᵢb&¬ordac⇒¬ordbc (≤ᵢic lt) (rlemma₁⇒¬ord-abs a b c refl refl refl lt nord w)) ≡ icc
-- -- --     ¬ord-morph$lemma₁≡I-abs a b c refl refl refl lt nord (ictEq icteq lleq tlleq refl) = {!!} -- ¬ord-morph$lemma₁≡I-abs1 a b c refl refl refl lt nord compIndU where
-- -- -- --      r = ¬ord-morph$lemma₁≡I ell a b lt c (¬ord-spec nord)
-- -- --     ¬ord-morph$lemma₁≡I-abs a b c refl refl refl lt nord (ict¬Eq ¬icteq refl refl) = {!!} 



-- -- --     ¬ord-morph$lemma₁≡I : ∀{i u pll ll cll fll} → ∀ ell → (emi : IndexLL {i} {u} fll ll) → (ind : IndexLL {i} {u} pll ll) → (lt : emi ≤ᵢ ind) → (lind : IndexLL cll (replLL ind ell)) → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind {ell} lt) lind)
-- -- --           → (¬ord-morph (lemma₁-¬ord-a≤ᵢb emi ind ell lt lind nord) ind (a≤ᵢb&¬ordac⇒¬ordbc lt (rlemma₁⇒¬ord emi ind ell lt lind nord)) ≡ lind)
-- -- --     ¬ord-morph$lemma₁≡I ell .↓ ind ≤ᵢ↓ lind nord = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
-- -- --     ¬ord-morph$lemma₁≡I ell .(ic _) .(ic _) (≤ᵢic lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- --     ¬ord-morph$lemma₁≡I ell ice@(ic emi) ici@(ic ind) clt@(≤ᵢic lt) icl@(ic lind) nord = {!!} -- ¬ord-morph$lemma₁≡I-abs emi ind lind refl refl refl lt nord  compIndU compIndU (a≤ᵢb&¬ordac⇒¬ordbc clt (rlemma₁⇒¬ord ice ici ell clt icl nord))


-- -- --     ¬ord-morph$lemma₁≡I' : ∀{i u pll ll cll fll} → ∀ ell → (emi : IndexLL {i} {u} fll ll) → (ind : IndexLL {i} {u} pll ll) → (lt : emi ≤ᵢ ind) → (lind : IndexLL cll (replLL ind ell)) → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind lt) lind) → (lnord : ¬ Orderedᵢ ind (lemma₁-¬ord-a≤ᵢb emi ind ell lt lind nord))
-- -- --         → (¬ord-morph (lemma₁-¬ord-a≤ᵢb emi ind ell lt lind nord) ind lnord ≡ lind)
-- -- --     ¬ord-morph$lemma₁≡I' = {!!}


-- -- -- -- module _ where

-- -- -- --   ¬ord-morph$lemma₁≡I' : ∀{i u pll ll cll fll} → ∀ ell → (emi : IndexLL {i} {u} fll ll) → (ind : IndexLL {i} {u} pll ll) → (lt : emi ≤ᵢ ind) → (lind : IndexLL cll (replLL ll ind ell)) → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind ell lt) lind) → (lnord : ¬ Orderedᵢ ind (lemma₁-¬ord-a≤ᵢb emi ind ell lt lind nord))
-- -- -- --          → (¬ord-morph (lemma₁-¬ord-a≤ᵢb emi ind ell lt lind nord) ind ell lnord ≡ lind)
-- -- -- --   ¬ord-morph$lemma₁≡I' ell ↓ ind ≤ᵢ↓ lind nord _ = ⊥-elim (nord (a≤ᵢb ≤ᵢ↓))
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (emi ←∧) (ind ←∧) (≤ᵢ←∧ lt) ↓ nord _ = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (emi ←∧) (ind ←∧) (≤ᵢ←∧ lt) (lind ←∧) nord lnord = cong (λ x → x ←∧) r where
-- -- -- --     r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (emi ←∧) (ind ←∧) (≤ᵢ←∧ lt) (∧→ lind) nord _ = refl
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (∧→ emi) (∧→ ind) (≤ᵢ∧→ lt) ↓ nord _ = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (∧→ emi) (∧→ ind) (≤ᵢ∧→ lt) (lind ←∧) nord _ = refl
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (∧→ emi) (∧→ ind) (≤ᵢ∧→ lt) (∧→ lind) nord lnord = cong (λ x → ∧→ x) r where
-- -- -- --     r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (emi ←∨) (ind ←∨) (≤ᵢ←∨ lt) ↓ nord _ = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (emi ←∨) (ind ←∨) (≤ᵢ←∨ lt) (lind ←∨) nord lnord = cong (λ x → x ←∨) r where
-- -- -- --     r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (emi ←∨) (ind ←∨) (≤ᵢ←∨ lt) (∨→ lind) nord _ = refl
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (∨→ emi) (∨→ ind) (≤ᵢ∨→ lt) ↓ nord = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (∨→ emi) (∨→ ind) (≤ᵢ∨→ lt) (lind ←∨) nord _ = refl
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (∨→ emi) (∨→ ind) (≤ᵢ∨→ lt) (∨→ lind) nord lnord = cong (λ x → ∨→ x) r where
-- -- -- --     r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (emi ←∂) (ind ←∂) (≤ᵢ←∂ lt) ↓ nord _ = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (emi ←∂) (ind ←∂) (≤ᵢ←∂ lt) (lind ←∂) nord lnord = cong (λ x → x ←∂) r where
-- -- -- --     r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (emi ←∂) (ind ←∂) (≤ᵢ←∂ lt) (∂→ lind) nord _ = refl
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (∂→ emi) (∂→ ind) (≤ᵢ∂→ lt) ↓ nord _ = ⊥-elim (nord (b≤ᵢa ≤ᵢ↓))
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (∂→ emi) (∂→ ind) (≤ᵢ∂→ lt) (lind ←∂) nord _ = refl
-- -- -- --   ¬ord-morph$lemma₁≡I' ell (∂→ emi) (∂→ ind) (≤ᵢ∂→ lt) (∂→ lind) nord lnord = cong (λ x → ∂→ x) r where
-- -- -- --     r = (¬ord-morph$lemma₁≡I' ell emi ind lt lind (¬ord-spec nord)) (¬ord-spec lnord)
    
-- -- -- --   ¬ord-morph$lemma₁≡I : ∀{i u pll ll cll fll} → ∀ ell → (emi : IndexLL {i} {u} fll ll) → (ind : IndexLL {i} {u} pll ll) → (lt : emi ≤ᵢ ind) → (lind : IndexLL cll (replLL ll ind ell)) → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind ell lt) lind)
-- -- -- --        → (¬ord-morph (lemma₁-¬ord-a≤ᵢb emi ind ell lt lind nord) ind ell (a≤ᵢb&¬ordac⇒¬ordbc lt (rlemma₁⇒¬ord emi ind ell lt lind nord)) ≡ lind)
-- -- -- --   ¬ord-morph$lemma₁≡I ell emi ind lt lind nord = ¬ord-morph$lemma₁≡I' ell emi ind lt lind nord (a≤ᵢb&¬ordac⇒¬ordbc lt (rlemma₁⇒¬ord emi ind ell lt lind nord))



-- -- -- -- _+ᵢ_ : ∀{i u pll cll ll} → IndexLL {i} {u} pll ll → IndexLL cll pll → IndexLL cll ll
-- -- -- -- _+ᵢ_ ↓ is = is
-- -- -- -- _+ᵢ_ (if ←∧) is = (_+ᵢ_ if is) ←∧
-- -- -- -- _+ᵢ_ (∧→ if) is = ∧→ (_+ᵢ_ if is)
-- -- -- -- _+ᵢ_ (if ←∨) is = (_+ᵢ_ if is) ←∨
-- -- -- -- _+ᵢ_ (∨→ if) is = ∨→ (_+ᵢ_ if is)
-- -- -- -- _+ᵢ_ (if ←∂) is = (_+ᵢ_ if is) ←∂
-- -- -- -- _+ᵢ_ (∂→ if) is = ∂→ (_+ᵢ_ if is)




-- -- -- -- +ᵢ⇒l≤ᵢ+ᵢ : ∀{i u pll cll ll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll)
-- -- -- --            → ind ≤ᵢ (ind +ᵢ lind)
-- -- -- -- +ᵢ⇒l≤ᵢ+ᵢ ↓ lind = ≤ᵢ↓
-- -- -- -- +ᵢ⇒l≤ᵢ+ᵢ (ind ←∧) lind = ≤ᵢ←∧ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
-- -- -- -- +ᵢ⇒l≤ᵢ+ᵢ (∧→ ind) lind = ≤ᵢ∧→ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
-- -- -- -- +ᵢ⇒l≤ᵢ+ᵢ (ind ←∨) lind = ≤ᵢ←∨ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
-- -- -- -- +ᵢ⇒l≤ᵢ+ᵢ (∨→ ind) lind = ≤ᵢ∨→ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
-- -- -- -- +ᵢ⇒l≤ᵢ+ᵢ (ind ←∂) lind = ≤ᵢ←∂ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)
-- -- -- -- +ᵢ⇒l≤ᵢ+ᵢ (∂→ ind) lind = ≤ᵢ∂→ (+ᵢ⇒l≤ᵢ+ᵢ ind lind)


-- -- -- -- a+↓≡a : ∀{i u pll ll} → (a : IndexLL {i} {u} pll ll) → a +ᵢ ↓ ≡ a
-- -- -- -- a+↓≡a ↓ = refl
-- -- -- -- a+↓≡a (a ←∧) with (a +ᵢ ↓) | (a+↓≡a a)
-- -- -- -- a+↓≡a (a ←∧) | .a | refl = refl
-- -- -- -- a+↓≡a (∧→ a) with (a +ᵢ ↓) | (a+↓≡a a)
-- -- -- -- a+↓≡a (∧→ a) | .a | refl = refl
-- -- -- -- a+↓≡a (a ←∨) with (a +ᵢ ↓) | (a+↓≡a a)
-- -- -- -- a+↓≡a (a ←∨) | .a | refl = refl
-- -- -- -- a+↓≡a (∨→ a) with (a +ᵢ ↓) | (a+↓≡a a)
-- -- -- -- a+↓≡a (∨→ a) | .a | refl = refl
-- -- -- -- a+↓≡a (a ←∂) with (a +ᵢ ↓) | (a+↓≡a a)
-- -- -- -- a+↓≡a (a ←∂) | .a | refl = refl
-- -- -- -- a+↓≡a (∂→ a) with (a +ᵢ ↓) | (a+↓≡a a)
-- -- -- -- a+↓≡a (∂→ a) | .a | refl = refl


-- -- -- -- [a+b]-a=b : ∀{i u rll ll fll} → (a : IndexLL {i} {u} fll ll)
-- -- -- --           → (b : IndexLL rll fll)
-- -- -- --           → ((a +ᵢ b) -ᵢ a) (+ᵢ⇒l≤ᵢ+ᵢ a b) ≡ b
-- -- -- -- [a+b]-a=b ↓ b = refl
-- -- -- -- [a+b]-a=b (a ←∧) b = [a+b]-a=b a b
-- -- -- -- [a+b]-a=b (∧→ a) b = [a+b]-a=b a b
-- -- -- -- [a+b]-a=b (a ←∨) b = [a+b]-a=b a b
-- -- -- -- [a+b]-a=b (∨→ a) b = [a+b]-a=b a b
-- -- -- -- [a+b]-a=b (a ←∂) b = [a+b]-a=b a b
-- -- -- -- [a+b]-a=b (∂→ a) b = [a+b]-a=b a b

-- -- -- -- a+[b-a]=b : ∀{i u rll ll fll} → (a : IndexLL {i} {u} fll ll)
-- -- -- --             → (b : IndexLL rll ll)
-- -- -- --             → (lt : a ≤ᵢ b)
-- -- -- --             → (a +ᵢ (b -ᵢ a) lt) ≡ b
-- -- -- -- a+[b-a]=b ↓ b ≤ᵢ↓ = refl
-- -- -- -- a+[b-a]=b (a ←∧) (b ←∧) (≤ᵢ←∧ lt) with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
-- -- -- -- a+[b-a]=b (a ←∧) (b ←∧) (≤ᵢ←∧ lt) | .b | refl = refl
-- -- -- -- a+[b-a]=b (∧→ a) (∧→ b) (≤ᵢ∧→ lt) with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
-- -- -- -- a+[b-a]=b (∧→ a) (∧→ b) (≤ᵢ∧→ lt) | .b | refl = refl
-- -- -- -- a+[b-a]=b (a ←∨) (b ←∨) (≤ᵢ←∨ lt) with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
-- -- -- -- a+[b-a]=b (a ←∨) (b ←∨) (≤ᵢ←∨ lt) | .b | refl = refl
-- -- -- -- a+[b-a]=b (∨→ a) (∨→ b) (≤ᵢ∨→ lt)with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
-- -- -- -- a+[b-a]=b (∨→ a) (∨→ b) (≤ᵢ∨→ lt) | .b | refl = refl
-- -- -- -- a+[b-a]=b (a ←∂) (b ←∂) (≤ᵢ←∂ lt) with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
-- -- -- -- a+[b-a]=b (a ←∂) (b ←∂) (≤ᵢ←∂ lt) | .b | refl = refl
-- -- -- -- a+[b-a]=b (∂→ a) (∂→ b) (≤ᵢ∂→ lt) with (a +ᵢ ((b -ᵢ a) lt)) | (a+[b-a]=b a b lt)
-- -- -- -- a+[b-a]=b (∂→ a) (∂→ b) (≤ᵢ∂→ lt) | .b | refl = refl



-- -- -- -- -- A predicate that is true if pll is not transformed by ltr.

-- -- -- -- data UpTran {i u} : ∀ {ll pll rll} → IndexLL pll ll → LLTr {i} {u} rll ll → Set (lsuc u) where
-- -- -- --   indI : ∀{pll ll} → {ind : IndexLL pll ll} → UpTran ind I
-- -- -- --   ←∂∂c : ∀{pll li ri rll ltr} → {ind : IndexLL pll ri} → UpTran {ll = li ∂ ri} {rll = rll} (∂→ ind) ltr
-- -- -- --          → UpTran (ind ←∂) (∂c ltr)
-- -- -- --   ∂→∂c : ∀{pll li ri rll ltr} → {ind : IndexLL pll li} → UpTran {ll = li ∂ ri} {rll = rll} (ind ←∂) ltr
-- -- -- --          → UpTran (∂→ ind) (∂c ltr)
-- -- -- --   ←∨∨c : ∀{pll li ri rll ltr} → {ind : IndexLL pll ri} → UpTran {ll = li ∨ ri} {rll = rll} (∨→ ind) ltr
-- -- -- --          → UpTran (ind ←∨) (∨c ltr)
-- -- -- --   ∨→∨c : ∀{pll li ri rll ltr} → {ind : IndexLL pll li} → UpTran {ll = li ∨ ri} {rll = rll} (ind ←∨) ltr
-- -- -- --          → UpTran (∨→ ind) (∨c ltr)
-- -- -- --   ←∧∧c : ∀{pll li ri rll ltr} → {ind : IndexLL pll ri} → UpTran {ll = li ∧ ri} {rll = rll} (∧→ ind) ltr
-- -- -- --          → UpTran (ind ←∧) (∧c ltr)
-- -- -- --   ∧→∧c : ∀{pll li ri rll ltr} → {ind : IndexLL pll li} → UpTran {ll = li ∧ ri} {rll = rll} (ind ←∧) ltr
-- -- -- --          → UpTran (∧→ ind) (∧c ltr)
-- -- -- --   ←∧]←∧∧∧d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lli}
-- -- -- --             → UpTran {rll = rll} (ind ←∧) ltr → UpTran {ll = (lli ∧ lri) ∧ ri} ((ind ←∧) ←∧) (∧∧d ltr)
-- -- -- --   ∧→]←∧∧∧d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lri}
-- -- -- --             → UpTran {rll = rll} (∧→ (ind ←∧)) ltr
-- -- -- --             → UpTran {ll = (lli ∧ lri) ∧ ri} ((∧→ ind) ←∧) (∧∧d ltr)
-- -- -- --   ∧→∧∧d    : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll ri}
-- -- -- --             → UpTran {rll = rll} (∧→ (∧→ ind)) ltr
-- -- -- --             → UpTran {ll = ((lli ∧ lri) ∧ ri)} (∧→ ind) (∧∧d ltr)
-- -- -- --   ←∧¬∧∧d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll li}
-- -- -- --             → UpTran {rll = rll} ((ind ←∧) ←∧) ltr
-- -- -- --             → UpTran {ll = li ∧ (rli ∧ rri)} (ind ←∧) (¬∧∧d ltr)
-- -- -- --   ∧→[←∧¬∧∧d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rli}
-- -- -- --             → UpTran {rll = rll} ((∧→ ind) ←∧) ltr
-- -- -- --             → UpTran {ll = li ∧ (rli ∧ rri)} (∧→ (ind ←∧)) (¬∧∧d ltr)
-- -- -- --   ∧→[∧→¬∧∧d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rri}
-- -- -- --             → UpTran {rll = rll} (∧→ ind) ltr
-- -- -- --             → UpTran {ll = li ∧ (rli ∧ rri)} (∧→ (∧→ ind)) (¬∧∧d ltr)
-- -- -- --   ←∨]←∨∨∨d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lli}
-- -- -- --             → UpTran {rll = rll} (ind ←∨) ltr → UpTran {ll = (lli ∨ lri) ∨ ri} ((ind ←∨) ←∨) (∨∨d ltr)
-- -- -- --   ∨→]←∨∨∨d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lri}
-- -- -- --             → UpTran {rll = rll} (∨→ (ind ←∨)) ltr
-- -- -- --             → UpTran {ll = (lli ∨ lri) ∨ ri} ((∨→ ind) ←∨) (∨∨d ltr)
-- -- -- --   ∨→∨∨d    : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll ri}
-- -- -- --             → UpTran {rll = rll} (∨→ (∨→ ind)) ltr
-- -- -- --             → UpTran {ll = (lli ∨ lri) ∨ ri} (∨→ ind) (∨∨d ltr)
-- -- -- --   ←∨¬∨∨d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll li}
-- -- -- --             → UpTran {rll = rll} ((ind ←∨) ←∨) ltr
-- -- -- --             → UpTran {ll = li ∨ (rli ∨ rri)} (ind ←∨) (¬∨∨d ltr)
-- -- -- --   ∨→[←∨¬∨∨d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rli}
-- -- -- --             → UpTran {rll = rll} ((∨→ ind) ←∨) ltr
-- -- -- --             → UpTran {ll = li ∨ (rli ∨ rri)} (∨→ (ind ←∨)) (¬∨∨d ltr)
-- -- -- --   ∨→[∨→¬∨∨d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rri}
-- -- -- --             → UpTran {rll = rll} (∨→ ind) ltr
-- -- -- --             → UpTran {ll = li ∨ (rli ∨ rri)} (∨→ (∨→ ind)) (¬∨∨d ltr)
-- -- -- --   ←∂]←∂∂∂d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lli}
-- -- -- --             → UpTran {rll = rll} (ind ←∂) ltr → UpTran {ll = (lli ∂ lri) ∂ ri} ((ind ←∂) ←∂) (∂∂d ltr)
-- -- -- --   ∂→]←∂∂∂d : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll lri}
-- -- -- --             → UpTran {rll = rll} (∂→ (ind ←∂)) ltr
-- -- -- --             → UpTran {ll = (lli ∂ lri) ∂ ri} ((∂→ ind) ←∂) (∂∂d ltr)
-- -- -- --   ∂→∂∂d    : ∀{pll lli lri ri rll ltr} → {ind : IndexLL pll ri}
-- -- -- --             → UpTran {rll = rll} (∂→ (∂→ ind)) ltr
-- -- -- --             → UpTran {ll = (lli ∂ lri) ∂ ri} (∂→ ind) (∂∂d ltr)
-- -- -- --   ←∂¬∂∂d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll li}
-- -- -- --             → UpTran {rll = rll} ((ind ←∂) ←∂) ltr
-- -- -- --             → UpTran {ll = li ∂ (rli ∂ rri)} (ind ←∂) (¬∂∂d ltr)
-- -- -- --   ∂→[←∂¬∂∂d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rli}
-- -- -- --             → UpTran {rll = rll} ((∂→ ind) ←∂) ltr
-- -- -- --             → UpTran {ll = li ∂ (rli ∂ rri)} (∂→ (ind ←∂)) (¬∂∂d ltr)
-- -- -- --   ∂→[∂→¬∂∂d : ∀{pll li rli rri rll ltr} → {ind : IndexLL pll rri}
-- -- -- --             → UpTran {rll = rll} (∂→ ind) ltr
-- -- -- --             → UpTran {ll = li ∂ (rli ∂ rri)} (∂→ (∂→ ind)) (¬∂∂d ltr)

-- -- -- -- isUpTran : ∀ {i u ll pll rll} → (ind : IndexLL pll ll) → (ltr : LLTr {i} {u} rll ll) → Dec (UpTran ind ltr)
-- -- -- -- isUpTran ind I = yes indI
-- -- -- -- isUpTran ↓ (∂c ltr) = no (λ ())
-- -- -- -- isUpTran (ind ←∂) (∂c ltr) with (isUpTran (∂→ ind) ltr)
-- -- -- -- isUpTran (ind ←∂) (∂c ltr) | yes ut = yes (←∂∂c ut)
-- -- -- -- isUpTran (ind ←∂) (∂c ltr) | no ¬ut = no (λ {(←∂∂c ut) → ¬ut ut})
-- -- -- -- isUpTran (∂→ ind) (∂c ltr)  with (isUpTran (ind ←∂) ltr)
-- -- -- -- isUpTran (∂→ ind) (∂c ltr) | yes ut = yes (∂→∂c ut)
-- -- -- -- isUpTran (∂→ ind) (∂c ltr) | no ¬ut = no (λ {(∂→∂c ut) → ¬ut ut})
-- -- -- -- isUpTran ↓ (∨c ltr) = no (λ ())
-- -- -- -- isUpTran (ind ←∨) (∨c ltr) with (isUpTran (∨→ ind) ltr)
-- -- -- -- isUpTran (ind ←∨) (∨c ltr) | yes p = yes (←∨∨c p)
-- -- -- -- isUpTran (ind ←∨) (∨c ltr) | no ¬p = no (λ {(←∨∨c p) → ¬p p}) 
-- -- -- -- isUpTran (∨→ ind) (∨c ltr) with (isUpTran (ind ←∨) ltr)
-- -- -- -- isUpTran (∨→ ind) (∨c ltr) | yes p = yes (∨→∨c p)
-- -- -- -- isUpTran (∨→ ind) (∨c ltr) | no ¬p = no (λ {(∨→∨c ut) → ¬p ut})
-- -- -- -- isUpTran ↓ (∧c ltr) = no (λ ())
-- -- -- -- isUpTran (ind ←∧) (∧c ltr) with (isUpTran (∧→ ind) ltr)
-- -- -- -- isUpTran (ind ←∧) (∧c ltr) | yes p = yes (←∧∧c p)
-- -- -- -- isUpTran (ind ←∧) (∧c ltr) | no ¬p = no (λ {(←∧∧c ut) → ¬p ut}) 
-- -- -- -- isUpTran (∧→ ind) (∧c ltr) with (isUpTran (ind ←∧) ltr)
-- -- -- -- isUpTran (∧→ ind) (∧c ltr) | yes p = yes (∧→∧c p)
-- -- -- -- isUpTran (∧→ ind) (∧c ltr) | no ¬p = no (λ {(∧→∧c ut) → ¬p ut})
-- -- -- -- isUpTran ↓ (∧∧d ltr) = no (λ ())
-- -- -- -- isUpTran (↓ ←∧) (∧∧d ltr) = no (λ ())
-- -- -- -- isUpTran ((ind ←∧) ←∧) (∧∧d ltr) with (isUpTran (ind ←∧) ltr)
-- -- -- -- isUpTran ((ind ←∧) ←∧) (∧∧d ltr) | yes p = yes (←∧]←∧∧∧d p)
-- -- -- -- isUpTran ((ind ←∧) ←∧) (∧∧d ltr) | no ¬p = no (λ {(←∧]←∧∧∧d ut) → ¬p ut}) 
-- -- -- -- isUpTran ((∧→ ind) ←∧) (∧∧d ltr) with (isUpTran (∧→ (ind ←∧)) ltr)
-- -- -- -- isUpTran ((∧→ ind) ←∧) (∧∧d ltr) | yes p = yes (∧→]←∧∧∧d p)
-- -- -- -- isUpTran ((∧→ ind) ←∧) (∧∧d ltr) | no ¬p = no (λ {(∧→]←∧∧∧d ut) → ¬p ut}) 
-- -- -- -- isUpTran (∧→ ind) (∧∧d ltr) with (isUpTran (∧→ (∧→ ind)) ltr)
-- -- -- -- isUpTran (∧→ ind) (∧∧d ltr) | yes p = yes (∧→∧∧d p)
-- -- -- -- isUpTran (∧→ ind) (∧∧d ltr) | no ¬p = no (λ {(∧→∧∧d ut) → ¬p ut})
-- -- -- -- isUpTran ↓ (¬∧∧d ltr) = no (λ ())
-- -- -- -- isUpTran (ind ←∧) (¬∧∧d ltr) with (isUpTran ((ind ←∧) ←∧) ltr)
-- -- -- -- isUpTran (ind ←∧) (¬∧∧d ltr) | yes p = yes (←∧¬∧∧d p)
-- -- -- -- isUpTran (ind ←∧) (¬∧∧d ltr) | no ¬p = no (λ {(←∧¬∧∧d ut) → ¬p ut})
-- -- -- -- isUpTran (∧→ ↓) (¬∧∧d ltr) = no (λ ())
-- -- -- -- isUpTran (∧→ (ind ←∧)) (¬∧∧d ltr) with (isUpTran ((∧→ ind) ←∧) ltr)
-- -- -- -- isUpTran (∧→ (ind ←∧)) (¬∧∧d ltr) | yes p = yes (∧→[←∧¬∧∧d p)
-- -- -- -- isUpTran (∧→ (ind ←∧)) (¬∧∧d ltr) | no ¬p = no (λ {(∧→[←∧¬∧∧d ut) → ¬p ut})
-- -- -- -- isUpTran (∧→ (∧→ ind)) (¬∧∧d ltr) with (isUpTran (∧→ ind) ltr)
-- -- -- -- isUpTran (∧→ (∧→ ind)) (¬∧∧d ltr) | yes p = yes (∧→[∧→¬∧∧d p)
-- -- -- -- isUpTran (∧→ (∧→ ind)) (¬∧∧d ltr) | no ¬p = no (λ {(∧→[∧→¬∧∧d ut) → ¬p ut})
-- -- -- -- isUpTran ↓ (∨∨d ltr) = no (λ ())
-- -- -- -- isUpTran (↓ ←∨) (∨∨d ltr) = no (λ ())
-- -- -- -- isUpTran ((ind ←∨) ←∨) (∨∨d ltr) with (isUpTran (ind ←∨) ltr)
-- -- -- -- isUpTran ((ind ←∨) ←∨) (∨∨d ltr) | yes p = yes (←∨]←∨∨∨d p)
-- -- -- -- isUpTran ((ind ←∨) ←∨) (∨∨d ltr) | no ¬p = no (λ {(←∨]←∨∨∨d ut) → ¬p ut}) 
-- -- -- -- isUpTran ((∨→ ind) ←∨) (∨∨d ltr) with (isUpTran (∨→ (ind ←∨)) ltr)
-- -- -- -- isUpTran ((∨→ ind) ←∨) (∨∨d ltr) | yes p = yes (∨→]←∨∨∨d p)
-- -- -- -- isUpTran ((∨→ ind) ←∨) (∨∨d ltr) | no ¬p = no (λ {(∨→]←∨∨∨d ut) → ¬p ut}) 
-- -- -- -- isUpTran (∨→ ind) (∨∨d ltr) with (isUpTran (∨→ (∨→ ind)) ltr)
-- -- -- -- isUpTran (∨→ ind) (∨∨d ltr) | yes p = yes (∨→∨∨d p)
-- -- -- -- isUpTran (∨→ ind) (∨∨d ltr) | no ¬p = no (λ {(∨→∨∨d ut) → ¬p ut})
-- -- -- -- isUpTran ↓ (¬∨∨d ltr) = no (λ ())
-- -- -- -- isUpTran (ind ←∨) (¬∨∨d ltr) with (isUpTran ((ind ←∨) ←∨) ltr)
-- -- -- -- isUpTran (ind ←∨) (¬∨∨d ltr) | yes p = yes (←∨¬∨∨d p)
-- -- -- -- isUpTran (ind ←∨) (¬∨∨d ltr) | no ¬p = no (λ {(←∨¬∨∨d ut) → ¬p ut})
-- -- -- -- isUpTran (∨→ ↓) (¬∨∨d ltr) = no (λ ())
-- -- -- -- isUpTran (∨→ (ind ←∨)) (¬∨∨d ltr) with (isUpTran ((∨→ ind) ←∨) ltr)
-- -- -- -- isUpTran (∨→ (ind ←∨)) (¬∨∨d ltr) | yes p = yes (∨→[←∨¬∨∨d p)
-- -- -- -- isUpTran (∨→ (ind ←∨)) (¬∨∨d ltr) | no ¬p = no (λ {(∨→[←∨¬∨∨d ut) → ¬p ut})
-- -- -- -- isUpTran (∨→ (∨→ ind)) (¬∨∨d ltr) with (isUpTran (∨→ ind) ltr)
-- -- -- -- isUpTran (∨→ (∨→ ind)) (¬∨∨d ltr) | yes p = yes (∨→[∨→¬∨∨d p)
-- -- -- -- isUpTran (∨→ (∨→ ind)) (¬∨∨d ltr) | no ¬p = no (λ {(∨→[∨→¬∨∨d ut) → ¬p ut})
-- -- -- -- isUpTran ↓ (∂∂d ltr) = no (λ ())
-- -- -- -- isUpTran (↓ ←∂) (∂∂d ltr) = no (λ ())
-- -- -- -- isUpTran ((ind ←∂) ←∂) (∂∂d ltr) with (isUpTran (ind ←∂) ltr)
-- -- -- -- isUpTran ((ind ←∂) ←∂) (∂∂d ltr) | yes p = yes (←∂]←∂∂∂d p)
-- -- -- -- isUpTran ((ind ←∂) ←∂) (∂∂d ltr) | no ¬p = no (λ {(←∂]←∂∂∂d ut) → ¬p ut})
-- -- -- -- isUpTran ((∂→ ind) ←∂) (∂∂d ltr) with (isUpTran (∂→ (ind ←∂)) ltr)
-- -- -- -- isUpTran ((∂→ ind) ←∂) (∂∂d ltr) | yes p = yes (∂→]←∂∂∂d p)
-- -- -- -- isUpTran ((∂→ ind) ←∂) (∂∂d ltr) | no ¬p = no (λ {(∂→]←∂∂∂d ut) → ¬p ut})
-- -- -- -- isUpTran (∂→ ind) (∂∂d ltr) with (isUpTran (∂→ (∂→ ind)) ltr)
-- -- -- -- isUpTran (∂→ ind) (∂∂d ltr) | yes p = yes (∂→∂∂d p)
-- -- -- -- isUpTran (∂→ ind) (∂∂d ltr) | no ¬p = no (λ {(∂→∂∂d ut) → ¬p ut})
-- -- -- -- isUpTran ↓ (¬∂∂d ltr) = no (λ ())
-- -- -- -- isUpTran (ind ←∂) (¬∂∂d ltr) with (isUpTran ((ind ←∂) ←∂) ltr)
-- -- -- -- isUpTran (ind ←∂) (¬∂∂d ltr) | yes p = yes (←∂¬∂∂d p)
-- -- -- -- isUpTran (ind ←∂) (¬∂∂d ltr) | no ¬p = no (λ {(←∂¬∂∂d ut) → ¬p ut})
-- -- -- -- isUpTran (∂→ ↓) (¬∂∂d ltr) = no (λ ())
-- -- -- -- isUpTran (∂→ (ind ←∂)) (¬∂∂d ltr) with (isUpTran ((∂→ ind) ←∂) ltr)
-- -- -- -- isUpTran (∂→ (ind ←∂)) (¬∂∂d ltr) | yes p = yes (∂→[←∂¬∂∂d p)
-- -- -- -- isUpTran (∂→ (ind ←∂)) (¬∂∂d ltr) | no ¬p = no (λ {(∂→[←∂¬∂∂d ut) → ¬p ut})
-- -- -- -- isUpTran (∂→ (∂→ ind)) (¬∂∂d ltr) with (isUpTran (∂→ ind) ltr)
-- -- -- -- isUpTran (∂→ (∂→ ind)) (¬∂∂d ltr) | yes p = yes (∂→[∂→¬∂∂d p)
-- -- -- -- isUpTran (∂→ (∂→ ind)) (¬∂∂d ltr) | no ¬p = no (λ {(∂→[∂→¬∂∂d ut) → ¬p ut})


-- -- -- -- indLow⇒UpTran : ∀ {i u rll ll n dt df} → (ind : IndexLL (τ {i} {u} {n} {dt} df) ll)
-- -- -- --                 → (ltr : LLTr {i} {u} rll ll) → UpTran ind ltr
-- -- -- -- indLow⇒UpTran ↓ I = indI
-- -- -- -- indLow⇒UpTran (ind ←∧) I = indI
-- -- -- -- indLow⇒UpTran (ind ←∧) (∧c ltr) = ←∧∧c r where
-- -- -- --   r = indLow⇒UpTran (∧→ ind) ltr
-- -- -- -- indLow⇒UpTran ((ind ←∧) ←∧) (∧∧d ltr) = ←∧]←∧∧∧d r where
-- -- -- --   r = indLow⇒UpTran (ind ←∧) ltr
-- -- -- -- indLow⇒UpTran ((∧→ ind) ←∧) (∧∧d ltr) = ∧→]←∧∧∧d r where
-- -- -- --   r = indLow⇒UpTran (∧→ (ind ←∧)) ltr
-- -- -- -- indLow⇒UpTran (ind ←∧) (¬∧∧d ltr) = ←∧¬∧∧d r where
-- -- -- --   r = indLow⇒UpTran ((ind ←∧) ←∧) ltr
-- -- -- -- indLow⇒UpTran (∧→ ind) I = indI
-- -- -- -- indLow⇒UpTran (∧→ ind) (∧c ltr) = ∧→∧c r where
-- -- -- --   r = indLow⇒UpTran (ind ←∧) ltr
-- -- -- -- indLow⇒UpTran (∧→ ind) (∧∧d ltr) = ∧→∧∧d r where
-- -- -- --   r = indLow⇒UpTran (∧→ (∧→ ind)) ltr
-- -- -- -- indLow⇒UpTran (∧→ (ind ←∧)) (¬∧∧d ltr) = ∧→[←∧¬∧∧d r where
-- -- -- --   r = indLow⇒UpTran ((∧→ ind) ←∧) ltr
-- -- -- -- indLow⇒UpTran (∧→ (∧→ ind)) (¬∧∧d ltr) = ∧→[∧→¬∧∧d r where
-- -- -- --   r = indLow⇒UpTran (∧→ ind) ltr
-- -- -- -- indLow⇒UpTran (ind ←∨) I = indI
-- -- -- -- indLow⇒UpTran (ind ←∨) (∨c ltr) = ←∨∨c r where
-- -- -- --   r = indLow⇒UpTran (∨→ ind) ltr
-- -- -- -- indLow⇒UpTran ((ind ←∨) ←∨) (∨∨d ltr) = ←∨]←∨∨∨d r where
-- -- -- --   r = indLow⇒UpTran (ind ←∨) ltr
-- -- -- -- indLow⇒UpTran ((∨→ ind) ←∨) (∨∨d ltr) = ∨→]←∨∨∨d r where
-- -- -- --   r = indLow⇒UpTran (∨→ (ind ←∨)) ltr
-- -- -- -- indLow⇒UpTran (ind ←∨) (¬∨∨d ltr) = ←∨¬∨∨d r where
-- -- -- --   r = indLow⇒UpTran ((ind ←∨) ←∨) ltr
-- -- -- -- indLow⇒UpTran (∨→ ind) I = indI
-- -- -- -- indLow⇒UpTran (∨→ ind) (∨c ltr) = ∨→∨c r where
-- -- -- --   r = indLow⇒UpTran (ind ←∨) ltr
-- -- -- -- indLow⇒UpTran (∨→ ind) (∨∨d ltr) = ∨→∨∨d r where
-- -- -- --   r = indLow⇒UpTran (∨→ (∨→ ind)) ltr
-- -- -- -- indLow⇒UpTran (∨→ (ind ←∨)) (¬∨∨d ltr) = ∨→[←∨¬∨∨d r where
-- -- -- --   r = indLow⇒UpTran ((∨→ ind) ←∨) ltr
-- -- -- -- indLow⇒UpTran (∨→ (∨→ ind)) (¬∨∨d ltr) = ∨→[∨→¬∨∨d r where
-- -- -- --   r = indLow⇒UpTran (∨→ ind) ltr
-- -- -- -- indLow⇒UpTran (ind ←∂) I = indI
-- -- -- -- indLow⇒UpTran (ind ←∂) (∂c ltr) = ←∂∂c r where
-- -- -- --   r = indLow⇒UpTran (∂→ ind) ltr
-- -- -- -- indLow⇒UpTran ((ind ←∂) ←∂) (∂∂d ltr) = ←∂]←∂∂∂d r where
-- -- -- --   r = indLow⇒UpTran (ind ←∂) ltr
-- -- -- -- indLow⇒UpTran ((∂→ ind) ←∂) (∂∂d ltr) = ∂→]←∂∂∂d r where
-- -- -- --   r = indLow⇒UpTran (∂→ (ind ←∂)) ltr
-- -- -- -- indLow⇒UpTran (ind ←∂) (¬∂∂d ltr) = ←∂¬∂∂d r where
-- -- -- --   r = indLow⇒UpTran ((ind ←∂) ←∂) ltr
-- -- -- -- indLow⇒UpTran (∂→ ind) I = indI
-- -- -- -- indLow⇒UpTran (∂→ ind) (∂c ltr) = ∂→∂c r where
-- -- -- --   r = indLow⇒UpTran (ind ←∂) ltr
-- -- -- -- indLow⇒UpTran (∂→ ind) (∂∂d ltr) = ∂→∂∂d r where
-- -- -- --   r = indLow⇒UpTran (∂→ (∂→ ind)) ltr
-- -- -- -- indLow⇒UpTran (∂→ (ind ←∂)) (¬∂∂d ltr) = ∂→[←∂¬∂∂d r where
-- -- -- --   r = indLow⇒UpTran ((∂→ ind) ←∂) ltr
-- -- -- -- indLow⇒UpTran (∂→ (∂→ ind)) (¬∂∂d ltr) = ∂→[∂→¬∂∂d r where
-- -- -- --   r = indLow⇒UpTran (∂→ ind) ltr



-- -- -- -- tran : ∀ {i u ll pll rll} → (ind : IndexLL pll ll) → (ltr : LLTr {i} {u} rll ll) → UpTran ind ltr
-- -- -- --        → IndexLL pll rll
-- -- -- -- tran ind I indI = ind 
-- -- -- -- tran ↓ (∂c ltr) () 
-- -- -- -- tran (ind ←∂) (∂c ltr) (←∂∂c ut) = tran (∂→ ind) ltr ut
-- -- -- -- tran (∂→ ind) (∂c ltr) (∂→∂c ut) =  tran (ind ←∂) ltr ut
-- -- -- -- tran ↓ (∨c ltr) () 
-- -- -- -- tran (ind ←∨) (∨c ltr) (←∨∨c ut) = tran (∨→ ind) ltr ut
-- -- -- -- tran (∨→ ind) (∨c ltr) (∨→∨c ut) = tran (ind ←∨) ltr ut
-- -- -- -- tran ↓ (∧c ltr) () 
-- -- -- -- tran (ind ←∧) (∧c ltr) (←∧∧c ut) = tran (∧→ ind) ltr ut
-- -- -- -- tran (∧→ ind) (∧c ltr) (∧→∧c ut) = tran (ind ←∧) ltr ut
-- -- -- -- tran ↓ (∧∧d ltr) () 
-- -- -- -- tran (↓ ←∧) (∧∧d ltr) () 
-- -- -- -- tran ((ind ←∧) ←∧) (∧∧d ltr) (←∧]←∧∧∧d ut) = tran (ind ←∧) ltr ut
-- -- -- -- tran ((∧→ ind) ←∧) (∧∧d ltr) (∧→]←∧∧∧d ut) = tran (∧→ (ind ←∧)) ltr ut
-- -- -- -- tran (∧→ ind) (∧∧d ltr) (∧→∧∧d ut) = tran (∧→ (∧→ ind)) ltr ut
-- -- -- -- tran ↓ (¬∧∧d ltr) () 
-- -- -- -- tran (ind ←∧) (¬∧∧d ltr) (←∧¬∧∧d ut) = tran ((ind ←∧) ←∧) ltr ut
-- -- -- -- tran (∧→ ↓) (¬∧∧d ltr) () 
-- -- -- -- tran (∧→ (ind ←∧)) (¬∧∧d ltr) (∧→[←∧¬∧∧d ut) = tran ((∧→ ind) ←∧) ltr ut
-- -- -- -- tran (∧→ (∧→ ind)) (¬∧∧d ltr) (∧→[∧→¬∧∧d ut) = tran (∧→ ind) ltr ut
-- -- -- -- tran ↓ (∨∨d ltr) () 
-- -- -- -- tran (↓ ←∨) (∨∨d ltr) () 
-- -- -- -- tran ((ind ←∨) ←∨) (∨∨d ltr) (←∨]←∨∨∨d ut) = tran (ind ←∨) ltr ut
-- -- -- -- tran ((∨→ ind) ←∨) (∨∨d ltr) (∨→]←∨∨∨d ut) = tran (∨→ (ind ←∨)) ltr ut
-- -- -- -- tran (∨→ ind) (∨∨d ltr) (∨→∨∨d ut) = tran (∨→ (∨→ ind)) ltr ut
-- -- -- -- tran ↓ (¬∨∨d ltr) () 
-- -- -- -- tran (ind ←∨) (¬∨∨d ltr) (←∨¬∨∨d ut) = tran ((ind ←∨) ←∨) ltr ut
-- -- -- -- tran (∨→ ↓) (¬∨∨d ltr) () 
-- -- -- -- tran (∨→ (ind ←∨)) (¬∨∨d ltr) (∨→[←∨¬∨∨d ut) = tran ((∨→ ind) ←∨) ltr ut
-- -- -- -- tran (∨→ (∨→ ind)) (¬∨∨d ltr) (∨→[∨→¬∨∨d ut) = tran (∨→ ind) ltr ut
-- -- -- -- tran ↓ (∂∂d ltr) () 
-- -- -- -- tran (↓ ←∂) (∂∂d ltr) () 
-- -- -- -- tran ((ind ←∂) ←∂) (∂∂d ltr) (←∂]←∂∂∂d ut) = tran (ind ←∂) ltr ut
-- -- -- -- tran ((∂→ ind) ←∂) (∂∂d ltr) (∂→]←∂∂∂d ut) = tran (∂→ (ind ←∂)) ltr ut
-- -- -- -- tran (∂→ ind) (∂∂d ltr) (∂→∂∂d ut) = tran (∂→ (∂→ ind)) ltr ut
-- -- -- -- tran ↓ (¬∂∂d ltr) () 
-- -- -- -- tran (ind ←∂) (¬∂∂d ltr) (←∂¬∂∂d ut) = tran ((ind ←∂) ←∂) ltr ut
-- -- -- -- tran (∂→ ↓) (¬∂∂d ltr) () 
-- -- -- -- tran (∂→ (ind ←∂)) (¬∂∂d ltr) (∂→[←∂¬∂∂d ut) = tran ((∂→ ind) ←∂) ltr ut
-- -- -- -- tran (∂→ (∂→ ind)) (¬∂∂d ltr) (∂→[∂→¬∂∂d ut) = tran (∂→ ind) ltr ut


-- -- -- -- tr-ltr-morph : ∀ {i u ll pll orll} → ∀ frll → (ind : IndexLL pll ll) → (ltr : LLTr {i} {u} orll ll) → (rvT : UpTran ind ltr) → LLTr (replLL orll (tran ind ltr rvT) frll) (replLL ll ind frll)
-- -- -- -- tr-ltr-morph frll ↓ .I indI = I
-- -- -- -- tr-ltr-morph frll (ind ←∧) I indI = I
-- -- -- -- tr-ltr-morph frll (ind ←∧) (∧c ltr) (←∧∧c rvT) with tr-ltr-morph frll (∧→ ind) ltr rvT
-- -- -- -- ... | r = ∧c r
-- -- -- -- tr-ltr-morph frll ((ind ←∧) ←∧) (∧∧d ltr) (←∧]←∧∧∧d rvT) with tr-ltr-morph frll (ind ←∧) ltr rvT
-- -- -- -- ... | r = ∧∧d r
-- -- -- -- tr-ltr-morph frll ((∧→ ind) ←∧) (∧∧d ltr) (∧→]←∧∧∧d rvT) with tr-ltr-morph frll (∧→ (ind ←∧)) ltr rvT
-- -- -- -- ... | r = ∧∧d r
-- -- -- -- tr-ltr-morph frll (ind ←∧) (¬∧∧d ltr) (←∧¬∧∧d rvT) with tr-ltr-morph frll ((ind ←∧) ←∧) ltr rvT
-- -- -- -- ... | r = ¬∧∧d r
-- -- -- -- tr-ltr-morph frll (∧→ ind) I indI = I
-- -- -- -- tr-ltr-morph frll (∧→ ind) (∧c ltr) (∧→∧c rvT) with tr-ltr-morph frll (ind ←∧) ltr rvT
-- -- -- -- ... | r = ∧c r
-- -- -- -- tr-ltr-morph frll (∧→ ind) (∧∧d ltr) (∧→∧∧d rvT) with tr-ltr-morph frll (∧→ (∧→ ind)) ltr rvT
-- -- -- -- ... | r = ∧∧d r
-- -- -- -- tr-ltr-morph frll (∧→ (ind ←∧)) (¬∧∧d ltr) (∧→[←∧¬∧∧d rvT) with tr-ltr-morph frll ((∧→ ind) ←∧) ltr rvT
-- -- -- -- ... | r = ¬∧∧d r
-- -- -- -- tr-ltr-morph frll (∧→ (∧→ ind)) (¬∧∧d ltr) (∧→[∧→¬∧∧d rvT)  with tr-ltr-morph frll (∧→ ind) ltr rvT
-- -- -- -- ... | r = ¬∧∧d r
-- -- -- -- tr-ltr-morph frll (ind ←∨) I indI = I
-- -- -- -- tr-ltr-morph frll (ind ←∨) (∨c ltr) (←∨∨c rvT) with tr-ltr-morph frll (∨→ ind) ltr rvT
-- -- -- -- ... | r = ∨c r
-- -- -- -- tr-ltr-morph frll ((ind ←∨) ←∨) (∨∨d ltr) (←∨]←∨∨∨d rvT) with tr-ltr-morph frll (ind ←∨) ltr rvT
-- -- -- -- ... | r = ∨∨d r
-- -- -- -- tr-ltr-morph frll ((∨→ ind) ←∨) (∨∨d ltr) (∨→]←∨∨∨d rvT) with tr-ltr-morph frll (∨→ (ind ←∨)) ltr rvT
-- -- -- -- ... | r = ∨∨d r
-- -- -- -- tr-ltr-morph frll (ind ←∨) (¬∨∨d ltr) (←∨¬∨∨d rvT) with tr-ltr-morph frll ((ind ←∨) ←∨) ltr rvT
-- -- -- -- ... | r = ¬∨∨d r
-- -- -- -- tr-ltr-morph frll (∨→ ind) I indI = I
-- -- -- -- tr-ltr-morph frll (∨→ ind) (∨c ltr) (∨→∨c rvT) with tr-ltr-morph frll (ind ←∨) ltr rvT
-- -- -- -- ... | r = ∨c r
-- -- -- -- tr-ltr-morph frll (∨→ ind) (∨∨d ltr) (∨→∨∨d rvT) with tr-ltr-morph frll (∨→ (∨→ ind)) ltr rvT
-- -- -- -- ... | r = ∨∨d r
-- -- -- -- tr-ltr-morph frll (∨→ (ind ←∨)) (¬∨∨d ltr) (∨→[←∨¬∨∨d rvT) with tr-ltr-morph frll ((∨→ ind) ←∨) ltr rvT
-- -- -- -- ... | r = ¬∨∨d r
-- -- -- -- tr-ltr-morph frll (∨→ (∨→ ind)) (¬∨∨d ltr) (∨→[∨→¬∨∨d rvT)  with tr-ltr-morph frll (∨→ ind) ltr rvT
-- -- -- -- ... | r = ¬∨∨d r
-- -- -- -- tr-ltr-morph frll (ind ←∂) I indI = I
-- -- -- -- tr-ltr-morph frll (ind ←∂) (∂c ltr) (←∂∂c rvT) with tr-ltr-morph frll (∂→ ind) ltr rvT
-- -- -- -- ... | r = ∂c r
-- -- -- -- tr-ltr-morph frll ((ind ←∂) ←∂) (∂∂d ltr) (←∂]←∂∂∂d rvT) with tr-ltr-morph frll (ind ←∂) ltr rvT
-- -- -- -- ... | r = ∂∂d r
-- -- -- -- tr-ltr-morph frll ((∂→ ind) ←∂) (∂∂d ltr) (∂→]←∂∂∂d rvT) with tr-ltr-morph frll (∂→ (ind ←∂)) ltr rvT
-- -- -- -- ... | r = ∂∂d r
-- -- -- -- tr-ltr-morph frll (ind ←∂) (¬∂∂d ltr) (←∂¬∂∂d rvT) with tr-ltr-morph frll ((ind ←∂) ←∂) ltr rvT
-- -- -- -- ... | r = ¬∂∂d r
-- -- -- -- tr-ltr-morph frll (∂→ ind) I indI = I
-- -- -- -- tr-ltr-morph frll (∂→ ind) (∂c ltr) (∂→∂c rvT) with tr-ltr-morph frll (ind ←∂) ltr rvT
-- -- -- -- ... | r = ∂c r
-- -- -- -- tr-ltr-morph frll (∂→ ind) (∂∂d ltr) (∂→∂∂d rvT) with tr-ltr-morph frll (∂→ (∂→ ind)) ltr rvT
-- -- -- -- ... | r = ∂∂d r
-- -- -- -- tr-ltr-morph frll (∂→ (ind ←∂)) (¬∂∂d ltr) (∂→[←∂¬∂∂d rvT) with tr-ltr-morph frll ((∂→ ind) ←∂) ltr rvT
-- -- -- -- ... | r = ¬∂∂d r
-- -- -- -- tr-ltr-morph frll (∂→ (∂→ ind)) (¬∂∂d ltr) (∂→[∂→¬∂∂d rvT)  with tr-ltr-morph frll (∂→ ind) ltr rvT
-- -- -- -- ... | r = ¬∂∂d r



-- -- -- -- drepl=>repl+ : ∀{i u pll ll cll frll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll)
-- -- -- --                → (replLL ll ind (replLL pll lind frll)) ≡ replLL ll (ind +ᵢ lind) frll
-- -- -- -- drepl=>repl+ ↓ lind = refl
-- -- -- -- drepl=>repl+ {pll = pll} {ll = li ∧ ri} {frll = frll} (ind ←∧) lind
-- -- -- --              with (replLL li ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
-- -- -- -- drepl=>repl+ {_} {_} {pll} {li ∧ ri} {_} {frll} (ind ←∧) lind
-- -- -- --              | .(replLL li (ind +ᵢ lind) frll) | refl = refl
-- -- -- -- drepl=>repl+ {pll = pll} {ll = li ∧ ri} {frll = frll} (∧→ ind) lind
-- -- -- --              with (replLL ri ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
-- -- -- -- drepl=>repl+ {_} {_} {pll} {li ∧ ri} {_} {frll} (∧→ ind) lind
-- -- -- --              | .(replLL ri (ind +ᵢ lind) frll) | refl = refl
-- -- -- -- drepl=>repl+ {pll = pll} {ll = li ∨ ri} {frll = frll} (ind ←∨) lind
-- -- -- --              with (replLL li ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
-- -- -- -- drepl=>repl+ {_} {_} {pll} {li ∨ ri} {_} {frll} (ind ←∨) lind
-- -- -- --              | .(replLL li (ind +ᵢ lind) frll) | refl = refl
-- -- -- -- drepl=>repl+ {pll = pll} {ll = li ∨ ri} {frll = frll} (∨→ ind) lind
-- -- -- --              with (replLL ri ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
-- -- -- -- drepl=>repl+ {_} {_} {pll} {li ∨ ri} {_} {frll} (∨→ ind) lind
-- -- -- --              | .(replLL ri (ind +ᵢ lind) frll) | refl = refl
-- -- -- -- drepl=>repl+ {pll = pll} {ll = li ∂ ri} {frll = frll} (ind ←∂) lind
-- -- -- --              with (replLL li ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
-- -- -- -- drepl=>repl+ {_} {_} {pll} {li ∂ ri} {_} {frll} (ind ←∂) lind
-- -- -- --              | .(replLL li (ind +ᵢ lind) frll) | refl = refl
-- -- -- -- drepl=>repl+ {pll = pll} {ll = li ∂ ri} {frll = frll} (∂→ ind) lind
-- -- -- --              with (replLL ri ind (replLL pll lind frll)) | (drepl=>repl+ {frll = frll} ind lind)
-- -- -- -- drepl=>repl+ {_} {_} {pll} {li ∂ ri} {_} {frll} (∂→ ind) lind
-- -- -- --              | .(replLL ri (ind +ᵢ lind) frll) | refl = refl



-- -- -- -- repl-r=>l : ∀{i u pll ll cll frll} → ∀ ell → (ind : IndexLL {i} {u} pll ll) → (x : IndexLL cll (replLL ll ind ell)) → let uind = a≤ᵢb-morph ind ind ell (≤ᵢ-reflexive ind)
-- -- -- --        in (ltuindx : uind ≤ᵢ x)
-- -- -- --        → (replLL ll ind (replLL ell (ind-rpl↓ ind ((x -ᵢ uind) ltuindx)) frll) ≡ replLL (replLL ll ind ell) x frll)
-- -- -- -- repl-r=>l ell ↓ x ≤ᵢ↓ = refl
-- -- -- -- repl-r=>l {ll = li ∧ ri} ell (ind ←∧) (x ←∧) (≤ᵢ←∧ ltuindx) = cong (λ x → x ∧ ri) (repl-r=>l ell ind x ltuindx)
-- -- -- -- repl-r=>l {ll = li ∧ ri} ell (∧→ ind) (∧→ x) (≤ᵢ∧→ ltuindx) = cong (λ x → li ∧ x) (repl-r=>l ell ind x ltuindx)
-- -- -- -- repl-r=>l {ll = li ∨ ri} ell (ind ←∨) (x ←∨) (≤ᵢ←∨ ltuindx) = cong (λ x → x ∨ ri) (repl-r=>l ell ind x ltuindx)
-- -- -- -- repl-r=>l {ll = li ∨ ri} ell (∨→ ind) (∨→ x) (≤ᵢ∨→ ltuindx) = cong (λ x → li ∨ x) (repl-r=>l ell ind x ltuindx)
-- -- -- -- repl-r=>l {ll = li ∂ ri} ell (ind ←∂) (x ←∂) (≤ᵢ←∂ ltuindx) = cong (λ x → x ∂ ri) (repl-r=>l ell ind x ltuindx)
-- -- -- -- repl-r=>l {ll = li ∂ ri} ell (∂→ ind) (∂→ x) (≤ᵢ∂→ ltuindx) = cong (λ x → li ∂ x) (repl-r=>l ell ind x ltuindx)



-- -- -- -- -- Deprecated
-- -- -- -- updInd : ∀{i u rll ll} → ∀ nrll → (ind : IndexLL {i} {u} rll ll)
-- -- -- --          → IndexLL {i} {u} nrll (replLL ll ind nrll)
-- -- -- -- updInd nrll ↓ = ↓
-- -- -- -- updInd nrll (ind ←∧) = (updInd nrll ind) ←∧
-- -- -- -- updInd nrll (∧→ ind) = ∧→ (updInd nrll ind)
-- -- -- -- updInd nrll (ind ←∨) = (updInd nrll ind) ←∨
-- -- -- -- updInd nrll (∨→ ind) = ∨→ (updInd nrll ind)
-- -- -- -- updInd nrll (ind ←∂) = (updInd nrll ind) ←∂
-- -- -- -- updInd nrll (∂→ ind) = ∂→ (updInd nrll ind)

-- -- -- -- -- Deprecated
-- -- -- -- -- Maybe instead of this function use a≤ᵢb-morph
-- -- -- -- updIndGen : ∀{i u pll ll cll} → ∀ nrll → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll)
-- -- -- --             → IndexLL {i} {u} (replLL pll lind nrll) (replLL ll (ind +ᵢ lind) nrll)
-- -- -- -- updIndGen nrll ↓ lind = ↓
-- -- -- -- updIndGen nrll (ind ←∧) lind = (updIndGen nrll ind lind) ←∧
-- -- -- -- updIndGen nrll (∧→ ind) lind = ∧→ (updIndGen nrll ind lind)
-- -- -- -- updIndGen nrll (ind ←∨) lind = (updIndGen nrll ind lind) ←∨
-- -- -- -- updIndGen nrll (∨→ ind) lind = ∨→ (updIndGen nrll ind lind)
-- -- -- -- updIndGen nrll (ind ←∂) lind = (updIndGen nrll ind lind) ←∂
-- -- -- -- updIndGen nrll (∂→ ind) lind = ∂→ (updIndGen nrll ind lind)



-- -- -- -- -- TODO This negation was writen so as to return nothing if ¬ (b ≤ᵢ a)
-- -- -- -- _-ₘᵢ_ : ∀ {i u pll cll ll} → IndexLL {i} {u} cll ll → IndexLL pll ll → Maybe $ IndexLL cll pll
-- -- -- -- a -ₘᵢ ↓ = just a
-- -- -- -- ↓ -ₘᵢ (b ←∧) = nothing
-- -- -- -- (a ←∧) -ₘᵢ (b ←∧) = a -ₘᵢ b
-- -- -- -- (∧→ a) -ₘᵢ (b ←∧) = nothing
-- -- -- -- ↓ -ₘᵢ (∧→ b) = nothing
-- -- -- -- (a ←∧) -ₘᵢ (∧→ b) = nothing
-- -- -- -- (∧→ a) -ₘᵢ (∧→ b) = a -ₘᵢ b
-- -- -- -- ↓ -ₘᵢ (b ←∨) = nothing
-- -- -- -- (a ←∨) -ₘᵢ (b ←∨) = a -ₘᵢ b
-- -- -- -- (∨→ a) -ₘᵢ (b ←∨) = nothing
-- -- -- -- ↓ -ₘᵢ (∨→ b) = nothing
-- -- -- -- (a ←∨) -ₘᵢ (∨→ b) = nothing
-- -- -- -- (∨→ a) -ₘᵢ (∨→ b) = a -ₘᵢ b
-- -- -- -- ↓ -ₘᵢ (b ←∂) = nothing
-- -- -- -- (a ←∂) -ₘᵢ (b ←∂) = a -ₘᵢ b
-- -- -- -- (∂→ a) -ₘᵢ (b ←∂) = nothing
-- -- -- -- ↓ -ₘᵢ (∂→ b) = nothing
-- -- -- -- (a ←∂) -ₘᵢ (∂→ b) = nothing
-- -- -- -- (∂→ a) -ₘᵢ (∂→ b) = a -ₘᵢ b

-- -- -- -- -- Deprecated
-- -- -- -- b-s≡j⇒s≤ᵢb : ∀ {i u pll cll ll} → (bind : IndexLL {i} {u} cll ll) → (sind : IndexLL pll ll)
-- -- -- --              →  Σ (IndexLL {i} {u} cll pll) (λ x → (bind -ₘᵢ sind) ≡ just x) → sind ≤ᵢ bind
-- -- -- -- b-s≡j⇒s≤ᵢb bind ↓ (rs , x) = ≤ᵢ↓
-- -- -- -- b-s≡j⇒s≤ᵢb ↓ (sind ←∧) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb (bind ←∧) (sind ←∧) (rs , x) = ≤ᵢ←∧ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
-- -- -- -- b-s≡j⇒s≤ᵢb (∧→ bind) (sind ←∧) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb ↓ (∧→ sind) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb (bind ←∧) (∧→ sind) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb (∧→ bind) (∧→ sind) (rs , x) = ≤ᵢ∧→ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
-- -- -- -- b-s≡j⇒s≤ᵢb ↓ (sind ←∨) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb (bind ←∨) (sind ←∨) (rs , x) = ≤ᵢ←∨ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
-- -- -- -- b-s≡j⇒s≤ᵢb (∨→ bind) (sind ←∨) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb ↓ (∨→ sind) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb (bind ←∨) (∨→ sind) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb (∨→ bind) (∨→ sind) (rs , x) =  ≤ᵢ∨→ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
-- -- -- -- b-s≡j⇒s≤ᵢb ↓ (sind ←∂) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb (bind ←∂) (sind ←∂) (rs , x) = ≤ᵢ←∂ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)
-- -- -- -- b-s≡j⇒s≤ᵢb (∂→ bind) (sind ←∂) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb ↓ (∂→ sind) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb (bind ←∂) (∂→ sind) (rs , ())
-- -- -- -- b-s≡j⇒s≤ᵢb (∂→ bind) (∂→ sind) (rs , x) = ≤ᵢ∂→ $ b-s≡j⇒s≤ᵢb bind sind (rs , x)

-- -- -- -- -- Deprecated
-- -- -- -- revUpdInd : ∀{i u ll cll ell pll} → (b : IndexLL pll ll) → (a : IndexLL {i} {u} cll (replLL ll b ell))
-- -- -- --             → a -ₘᵢ (updInd ell b) ≡ nothing → (updInd ell b) -ₘᵢ a ≡ nothing → IndexLL cll ll
-- -- -- -- revUpdInd ↓ a () b-a
-- -- -- -- revUpdInd (b ←∧) ↓ refl ()
-- -- -- -- revUpdInd (b ←∧) (a ←∧) a-b b-a = revUpdInd b a a-b b-a ←∧
-- -- -- -- revUpdInd (b ←∧) (∧→ a) a-b b-a = ∧→ a
-- -- -- -- revUpdInd (∧→ b) ↓ refl ()
-- -- -- -- revUpdInd (∧→ b) (a ←∧) a-b b-a = a ←∧
-- -- -- -- revUpdInd (∧→ b) (∧→ a) a-b b-a = ∧→ revUpdInd b a a-b b-a
-- -- -- -- revUpdInd (b ←∨) ↓ refl ()
-- -- -- -- revUpdInd (b ←∨) (a ←∨) a-b b-a = revUpdInd b a a-b b-a ←∨
-- -- -- -- revUpdInd (b ←∨) (∨→ a) a-b b-a = ∨→ a
-- -- -- -- revUpdInd (∨→ b) ↓ refl ()
-- -- -- -- revUpdInd (∨→ b) (a ←∨) a-b b-a = a ←∨
-- -- -- -- revUpdInd (∨→ b) (∨→ a) a-b b-a = ∨→ revUpdInd b a a-b b-a
-- -- -- -- revUpdInd (b ←∂) ↓ refl ()
-- -- -- -- revUpdInd (b ←∂) (a ←∂) a-b b-a = revUpdInd b a a-b b-a ←∂
-- -- -- -- revUpdInd (b ←∂) (∂→ a) a-b b-a = ∂→ a
-- -- -- -- revUpdInd (∂→ b) ↓ refl ()
-- -- -- -- revUpdInd (∂→ b) (a ←∂) a-b b-a = a ←∂
-- -- -- -- revUpdInd (∂→ b) (∂→ a) a-b b-a = ∂→ revUpdInd b a a-b b-a


-- -- -- -- -- Deprecated
-- -- -- -- updIndPart : ∀{i u ll cll ell pll} → (b : IndexLL pll ll) → (a : IndexLL {i} {u} cll ll)
-- -- -- --              → a -ₘᵢ b ≡ nothing → b -ₘᵢ a ≡ nothing → IndexLL cll (replLL ll b ell)
-- -- -- -- updIndPart ↓ a () eq2
-- -- -- -- updIndPart (b ←∧) ↓ refl ()
-- -- -- -- updIndPart (b ←∧) (a ←∧) eq1 eq2 = updIndPart b a eq1 eq2 ←∧
-- -- -- -- updIndPart (b ←∧) (∧→ a) eq1 eq2 = ∧→ a
-- -- -- -- updIndPart (∧→ b) ↓ refl ()
-- -- -- -- updIndPart (∧→ b) (a ←∧) eq1 eq2 = a ←∧
-- -- -- -- updIndPart (∧→ b) (∧→ a) eq1 eq2 = ∧→ updIndPart b a eq1 eq2
-- -- -- -- updIndPart (b ←∨) ↓ refl ()
-- -- -- -- updIndPart (b ←∨) (a ←∨) eq1 eq2 = updIndPart b a eq1 eq2 ←∨
-- -- -- -- updIndPart (b ←∨) (∨→ a) eq1 eq2 = ∨→ a
-- -- -- -- updIndPart (∨→ b) ↓ refl ()
-- -- -- -- updIndPart (∨→ b) (a ←∨) eq1 eq2 = a ←∨
-- -- -- -- updIndPart (∨→ b) (∨→ a) eq1 eq2 = ∨→ updIndPart b a eq1 eq2
-- -- -- -- updIndPart (b ←∂) ↓ refl ()
-- -- -- -- updIndPart (b ←∂) (a ←∂) eq1 eq2 = updIndPart b a eq1 eq2 ←∂
-- -- -- -- updIndPart (b ←∂) (∂→ a) eq1 eq2 = ∂→ a
-- -- -- -- updIndPart (∂→ b) ↓ refl ()
-- -- -- -- updIndPart (∂→ b) (a ←∂) eq1 eq2 = a ←∂
-- -- -- -- updIndPart (∂→ b) (∂→ a) eq1 eq2 = ∂→ updIndPart b a eq1 eq2

-- -- -- -- -- Deprecated
-- -- -- -- rev⇒rs-i≡n : ∀{i u ll cll ell pll} → (ind : IndexLL pll ll)
-- -- -- --              → (lind : IndexLL {i} {u} cll (replLL ll ind ell))
-- -- -- --              → (eq₁ : (lind -ₘᵢ (updInd ell ind) ≡ nothing))
-- -- -- --              → (eq₂ : ((updInd ell ind) -ₘᵢ lind ≡ nothing))
-- -- -- --              → let rs = revUpdInd ind lind eq₁ eq₂ in
-- -- -- --                  ((rs -ₘᵢ ind) ≡ nothing) × ((ind -ₘᵢ rs) ≡ nothing)
-- -- -- -- rev⇒rs-i≡n ↓ lind () eq2
-- -- -- -- rev⇒rs-i≡n (ind ←∧) ↓ eq1 ()
-- -- -- -- rev⇒rs-i≡n (ind ←∧) (lind ←∧) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
-- -- -- -- rev⇒rs-i≡n (ind ←∧) (∧→ lind) eq1 eq2 = refl , refl
-- -- -- -- rev⇒rs-i≡n (∧→ ind) ↓ eq1 ()
-- -- -- -- rev⇒rs-i≡n (∧→ ind) (lind ←∧) eq1 eq2 = refl , refl
-- -- -- -- rev⇒rs-i≡n (∧→ ind) (∧→ lind) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
-- -- -- -- rev⇒rs-i≡n (ind ←∨) ↓ eq1 ()
-- -- -- -- rev⇒rs-i≡n (ind ←∨) (lind ←∨) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
-- -- -- -- rev⇒rs-i≡n (ind ←∨) (∨→ lind) eq1 eq2 = refl , refl
-- -- -- -- rev⇒rs-i≡n (∨→ ind) ↓ eq1 ()
-- -- -- -- rev⇒rs-i≡n (∨→ ind) (lind ←∨) eq1 eq2 = refl , refl
-- -- -- -- rev⇒rs-i≡n (∨→ ind) (∨→ lind) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
-- -- -- -- rev⇒rs-i≡n (ind ←∂) ↓ eq1 ()
-- -- -- -- rev⇒rs-i≡n (ind ←∂) (lind ←∂) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2
-- -- -- -- rev⇒rs-i≡n (ind ←∂) (∂→ lind) eq1 eq2 = refl , refl
-- -- -- -- rev⇒rs-i≡n (∂→ ind) ↓ eq1 ()
-- -- -- -- rev⇒rs-i≡n (∂→ ind) (lind ←∂) eq1 eq2 = refl , refl
-- -- -- -- rev⇒rs-i≡n (∂→ ind) (∂→ lind) eq1 eq2 = rev⇒rs-i≡n ind lind eq1 eq2




-- -- -- -- -- Deprecated
-- -- -- -- remRepl : ∀{i u ll frll ell pll cll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll)
-- -- -- --           → replLL (replLL ll (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell ≡ replLL ll ind ell
-- -- -- -- remRepl ↓ lind = refl
-- -- -- -- remRepl {ll = li ∧ ri} {frll = frll} {ell = ell} (ind ←∧) lind
-- -- -- --         with (replLL (replLL li (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
-- -- -- --         | (remRepl {frll = frll} {ell = ell} ind lind)
-- -- -- -- remRepl {_} {_} {li ∧ ri} {frll} {ell} (ind ←∧) lind | .(replLL li ind ell) | refl = refl
-- -- -- -- remRepl {ll = li ∧ ri} {frll = frll} {ell = ell} (∧→ ind) lind
-- -- -- --         with (replLL (replLL ri (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
-- -- -- --         | (remRepl {frll = frll} {ell = ell} ind lind)
-- -- -- -- remRepl {_} {_} {li ∧ ri} {frll} {ell} (∧→ ind) lind | .(replLL ri ind ell) | refl = refl
-- -- -- -- remRepl {ll = li ∨ ri} {frll = frll} {ell = ell} (ind ←∨) lind
-- -- -- --         with (replLL (replLL li (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
-- -- -- --         | (remRepl {frll = frll} {ell = ell} ind lind)
-- -- -- -- remRepl {_} {_} {li ∨ ri} {frll} {ell} (ind ←∨) lind | .(replLL li ind ell) | refl = refl
-- -- -- -- remRepl {ll = li ∨ ri} {frll = frll} {ell = ell} (∨→ ind) lind
-- -- -- --         with (replLL (replLL ri (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
-- -- -- --         | (remRepl {frll = frll} {ell = ell} ind lind)
-- -- -- -- remRepl {_} {_} {li ∨ ri} {frll} {ell} (∨→ ind) lind | .(replLL ri ind ell) | refl = refl
-- -- -- -- remRepl {ll = li ∂ ri} {frll = frll} {ell = ell} (ind ←∂) lind
-- -- -- --         with (replLL (replLL li (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
-- -- -- --         | (remRepl {frll = frll} {ell = ell} ind lind)
-- -- -- -- remRepl {_} {_} {li ∂ ri} {frll} {ell} (ind ←∂) lind | .(replLL li ind ell) | refl = refl
-- -- -- -- remRepl {ll = li ∂ ri} {frll = frll} {ell = ell} (∂→ ind) lind
-- -- -- --         with (replLL (replLL ri (ind +ᵢ lind) frll) (updIndGen frll ind lind) ell)
-- -- -- --         | (remRepl {frll = frll} {ell = ell} ind lind)
-- -- -- -- remRepl {_} {_} {li ∂ ri} {frll} {ell} (∂→ ind) lind | .(replLL ri ind ell) | refl = refl

-- -- -- -- -- Deprecated
-- -- -- -- replLL-inv : ∀{i u ll ell pll} → (ind : IndexLL {i} {u} pll ll)
-- -- -- --              → replLL (replLL ll ind ell) (updInd ell ind) pll ≡ ll
-- -- -- -- replLL-inv ↓ = refl
-- -- -- -- replLL-inv {ll = li ∧ ri} {ell = ell} {pll = pll} (ind ←∧)
-- -- -- --            with (replLL (replLL li ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
-- -- -- -- replLL-inv {_} {_} {li ∧ ri} {ell} {pll} (ind ←∧) | .li | refl = refl
-- -- -- -- replLL-inv {ll = li ∧ ri} {ell = ell} {pll = pll} (∧→ ind)
-- -- -- --            with (replLL (replLL ri ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
-- -- -- -- replLL-inv {_} {_} {li ∧ ri} {ell} {pll} (∧→ ind) | .ri | refl = refl
-- -- -- -- replLL-inv {ll = li ∨ ri} {ell = ell} {pll = pll} (ind ←∨)
-- -- -- --            with (replLL (replLL li ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
-- -- -- -- replLL-inv {_} {_} {li ∨ ri} {ell} {pll} (ind ←∨) | .li | refl = refl
-- -- -- -- replLL-inv {ll = li ∨ ri} {ell = ell} {pll = pll} (∨→ ind)
-- -- -- --            with (replLL (replLL ri ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
-- -- -- -- replLL-inv {_} {_} {li ∨ ri} {ell} {pll} (∨→ ind) | .ri | refl = refl
-- -- -- -- replLL-inv {ll = li ∂ ri} {ell = ell} {pll = pll} (ind ←∂)
-- -- -- --            with (replLL (replLL li ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
-- -- -- -- replLL-inv {_} {_} {li ∂ ri} {ell} {pll} (ind ←∂) | .li | refl = refl
-- -- -- -- replLL-inv {ll = li ∂ ri} {ell = ell} {pll = pll} (∂→ ind)
-- -- -- --            with (replLL (replLL ri ind ell) (updInd ell ind) pll) | (replLL-inv {ell = ell} ind)
-- -- -- -- replLL-inv {_} {_} {li ∂ ri} {ell} {pll} (∂→ ind) | .ri | refl = refl


