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
    ≅ᵢic : ∀{fll il d l r} → {sind : IndexLL gll (pickLL d l r)} → {bind : IndexLL fll (pickLL d l r)} → {{ieq : sind ≅ᵢ bind}}
           → _≅ᵢ_ {ll = l < il > r} (ic d sind) (ic d bind)


instance
  ≅ᵢ-reflexive : ∀{i u rll ll} → {a : IndexLL {i} {u} rll ll} → a ≅ᵢ a
  ≅ᵢ-reflexive {a = ↓} = ≅ᵢ↓
  ≅ᵢ-reflexive {a = (ic _ _)} = ≅ᵢic 

-- Possibly it needs to be removed.
instance
  ≡-to-≅ᵢ : ∀{i u rll ll} → {a b : IndexLL {i} {u} rll ll} → a ≡ b → a ≅ᵢ b
  ≡-to-≅ᵢ refl = ≅ᵢ-reflexive



data _≤ᵢ_ {i u gll fll} : ∀{ll} → IndexLL {i} {u} gll ll → IndexLL {i} {u} fll ll → Set (lsuc u) where
  instance
    ≤ᵢ↓ : {ind : IndexLL fll gll} → ↓ ≤ᵢ ind
    ≤ᵢic : ∀{il d l r} → {sind : IndexLL gll (pickLL d l r)} → {bind : IndexLL fll (pickLL d l r)} → {{ieq : sind ≤ᵢ bind}}
           → _≤ᵢ_ {ll = (l < il > r)} (ic d sind) (ic d bind)


≤ᵢ-spec : ∀{i u il d l r gll fll} → {sind : IndexLL {i} {u} gll (pickLL d l r)}
          → {bind : IndexLL fll (pickLL d l r)} → _≤ᵢ_ {ll = l < il > r} (ic d sind) (ic d bind)
          → (sind ≤ᵢ bind)
≤ᵢ-spec ≤ᵢic = it


instance
  ≤ᵢ-reflexive : ∀{i u gll ll} → {ind : IndexLL {i} {u} gll ll} → ind ≤ᵢ ind
  ≤ᵢ-reflexive {ind = ↓} = ≤ᵢ↓
  ≤ᵢ-reflexive {ind = (ic _ _)} = ≤ᵢic

≤ᵢ-transitive : ∀{i u gll fll mll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL fll ll} → {c : IndexLL mll ll} → (a ≤ᵢ b) → (b ≤ᵢ c) → (a ≤ᵢ c)
≤ᵢ-transitive ≤ᵢ↓ b = ≤ᵢ↓
≤ᵢ-transitive (≤ᵢic {{ieq = x}}) (≤ᵢic {{ieq = y}}) = ≤ᵢic {{ieq = (≤ᵢ-transitive x y)}}


isLTi : ∀{i u gll ll fll} → (a : IndexLL {i} {u} gll ll) → (b : IndexLL fll ll) → Dec (a ≤ᵢ b)
isLTi ↓ b = yes it
isLTi (ic d a) ↓ = no λ ()
isLTi (ic d a) (ic d1 b) with isEqICT d d1
isLTi (ic d a) (ic .d b) | yes refl with isLTi a b
isLTi (ic d a) (ic .d b) | yes refl | yes p = p asInst yes it 
isLTi (ic d a) (ic .d b) | yes refl | no ¬p = no λ { (≤ᵢic {{ieq}}) → ¬p ieq}
isLTi (ic d a) (ic d1 b) | no ~p = no λ { ≤ᵢic → ~ict⇒¬≡ ~p refl}



isEqᵢ : ∀{u i ll rll} → (a : IndexLL {i} {u} rll ll) → (b : IndexLL rll ll) → Dec (a ≡ b)
isEqᵢ ↓ ↓ = yes refl
isEqᵢ ↓ (ic d b) = no λ ()
isEqᵢ (ic d a) ↓ = no (λ ())
isEqᵢ (ic d a) (ic d1 b) with isEqICT d d1
isEqᵢ (ic d a) (ic .d b) | yes refl with isEqᵢ a b
isEqᵢ (ic d a) (ic .d .a) | yes refl | yes refl = yes refl
isEqᵢ (ic d a) (ic .d b) | yes refl | no ¬p = no λ { refl → ¬p refl}
isEqᵢ (ic d a) (ic d1 b) | no ~p = no λ { refl → ~ict⇒¬≡ ~p refl}



instance
  indτ-le⇒ieq : ∀{i u rll ll n dt df} → {ind : IndexLL {i} {u} (τ {i} {u} {n} {dt} df) ll} → {ind2 : IndexLL rll ll} → {{rl : ind ≤ᵢ ind2}} → (ind2 ≅ᵢ ind)
  indτ-le⇒ieq {ind = .↓} {↓} {{≤ᵢ↓}} = ≅ᵢ↓
  indτ-le⇒ieq {ind = .(ic _ _)} {.(ic _ _)} {{≤ᵢic}} = ≅ᵢic
  



data Orderedᵢ {i u gll fll ll} (a : IndexLL {i} {u} gll ll) (b : IndexLL {i} {u} fll ll) : Set (lsuc u) where
  instance
    a≤ᵢb : {{rl : a ≤ᵢ b}} → Orderedᵢ a b
    b≤ᵢa : {{rl : b ≤ᵢ a}} → Orderedᵢ a b



ord-spec : ∀{i u rll il l r d fll} → {emi : IndexLL {i} {u} fll (pickLL d l r)}
           → {ind : IndexLL rll (pickLL d l r)} → Orderedᵢ (ic {il = il} d ind) (ic d emi) → Orderedᵢ ind emi
ord-spec (a≤ᵢb {{rl = x}}) = a≤ᵢb {{rl = (≤ᵢ-spec x)}}
ord-spec (b≤ᵢa {{rl = x}}) = b≤ᵢa {{rl = (≤ᵢ-spec x)}}


instance
  ord-ext : ∀{i u rll il l r d fll} → {emi : IndexLL {i} {u} fll (pickLL d l r)}
             → {ind : IndexLL rll (pickLL d l r)} → Orderedᵢ ind emi → Orderedᵢ (ic {il = il} d ind) (ic d emi)
  ord-ext a≤ᵢb = a≤ᵢb
  ord-ext b≤ᵢa = b≤ᵢa



ord-spec∘ord-ext≡id : ∀{i u il l r d fll rll} → (ind : IndexLL {i} {u} fll (pickLL d l r)) → (lind : IndexLL rll (pickLL d l r)) → {{ ord : Orderedᵢ ind lind }} → ord-spec {il = il} {l} {r} {d} (ord-ext ord) ≡ ord
ord-spec∘ord-ext≡id _ _ {{ord = a≤ᵢb}} = refl
ord-spec∘ord-ext≡id _ _ {{ord = b≤ᵢa}} = refl


≅⇒bord : ∀{i u rll pll ll}
              → {ind : IndexLL {i} {u} pll ll} {lind : IndexLL rll ll}
              → {{eq : lind ≅ᵢ ind}} → (ind ≤ᵢ lind) × (lind ≤ᵢ ind)
≅⇒bord {{eq = ≅ᵢ↓}} = ≤ᵢ↓ , ≤ᵢ↓
≅⇒bord {{eq = ≅ᵢic}} = ≤ᵢic {{ieq = (proj₁ r)}} , ≤ᵢic {{ieq = (proj₂ r)}} where
  r = ≅⇒bord


¬lt¬gt⇒¬Ord : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
              → ¬ (a ≤ᵢ b) → ¬ (b ≤ᵢ a) → ¬ (Orderedᵢ a b)
¬lt¬gt⇒¬Ord nlt ngt a≤ᵢb = nlt it
¬lt¬gt⇒¬Ord nlt ngt b≤ᵢa = ngt it



isOrdᵢ : ∀{i u gll fll ll} → (a : IndexLL {i} {u} gll ll) → (b : IndexLL {i} {u} fll ll)
         → Dec (Orderedᵢ a b)
isOrdᵢ a b with isLTi a b
isOrdᵢ a b | yes p = p asInst yes it
isOrdᵢ a b | no ¬p with isLTi b a
isOrdᵢ a b | no ¬p | yes p = p asInst yes it
isOrdᵢ a b | no ¬p | no ¬p₁ = no (¬lt¬gt⇒¬Ord ¬p ¬p₁)





flipOrdᵢ : ∀{i u gll fll ll} → {a : IndexLL {i} {u} gll ll} → {b : IndexLL {i} {u} fll ll}
           → Orderedᵢ a b → Orderedᵢ b a
flipOrdᵢ a≤ᵢb = b≤ᵢa
flipOrdᵢ b≤ᵢa = a≤ᵢb





ord⇒icteq : ∀{u i l r il da db fll rll a b ica icb}
       → (iceqa : ica ≡ ic {i} {u} {fll} {l} {r} {il} da a)
       → (iceqb : icb ≡ ic {i} {u} {rll} db b)
       → Orderedᵢ icb ica
       → da ≡ db
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
((ic _ bind) -ᵢ (ic _ sind)) {{rl = ≤ᵢic}} = bind -ᵢ sind


ind-ᵢind≡↓ : ∀ {i u pll ll} → (ind : IndexLL {i} {u} pll ll) → {{rl : ind ≤ᵢ ind}}
       → (ind -ᵢ ind) {{rl = rl}} ≡ ↓
ind-ᵢind≡↓ _ {{rl = ≤ᵢ↓}} = refl
ind-ᵢind≡↓ (ic _ ind) {{rl = ≤ᵢic}} = ind-ᵢind≡↓ ind



rpl↓ : ∀{i u ll pll} → ∀ ell → (ind : IndexLL {i} {u} pll ll)
        → (replLL (ind -ᵢ ind) ell) ≡ ell
rpl↓ ell ind = cong (λ z → replLL z ell) (ind-ᵢind≡↓ ind)

ind-rpl↓1 : ∀{i u ll pll cll ell} → (ind : IndexLL {i} {u} pll ll)
        → IndexLL cll (replLL (ind -ᵢ ind) ell) → IndexLL cll ell
ind-rpl↓1 {_} {_} {_} {pll} {cll} {ell} ind y
  =  subst (λ x → x) (cong (λ x → IndexLL cll x) (rpl↓ ell ind)) y 

ind-rpl↓2 : ∀{i u ll pll cll ell} → (ind : IndexLL {i} {u} pll ll)
        → IndexLL (replLL (ind -ᵢ ind) ell) cll → IndexLL ell cll
ind-rpl↓2 {_} {_} {_} {pll} {cll} {ell} ind y
  =  subst (λ x → x) (cong (λ x → IndexLL x cll) (rpl↓ ell ind)) y 


a≤ᵢb-morph : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll)
             → (ind : IndexLL rll ll) → ∀ {frll} → {{lt : emi ≤ᵢ ind}}
             → IndexLL (replLL (ind -ᵢ emi) frll) (replLL ind frll) 
a≤ᵢb-morph .↓ ind {{lt = ≤ᵢ↓}} = ↓
a≤ᵢb-morph (ic d emi) (ic {l = l} {r} _ ind) {frll} {{lt = ≤ᵢic}}
  = ic d
       (subst
         (λ z → IndexLL (replLL (ind -ᵢ emi) frll) z)
         (sym (trans (pickLL-eq d pickLL pickLL (replLL ind frll) l r (replLL ind frll) refl refl) (sym (pickLL-id d (replLL ind frll)))))
         (a≤ᵢb-morph emi ind))





a≤ᵢb-morph-id-abs1 : ∀ {i u} {l r : LinLogic i {u}} {d}
                     {rll : LinLogic i} {w3 : IndexLL rll (pickLL d l r)} {il}
                     → ∀{w1Tl w1Tr}
                     → (w1 : w1Tl < il > w1Tr ≡ l < il > r)
                     → (w2 : pickLL d l r ≡ pickLL d w1Tl w1Tr)
                     →   subst₂ IndexLL refl w1
                           (ic {il = il} d (subst (IndexLL rll) w2 w3))
                       ≡
                         ic d w3
a≤ᵢb-morph-id-abs1 refl refl = refl

a≤ᵢb-morph-id-abs : ∀ {i u} {l r : LinLogic i {u}} {il}
               {rll : LinLogic i} {d} {ind : IndexLL rll (pickLL d l r)}
               → ∀{w1T w2T}
               → (w1 : w1T ≡ rll)
               → (w2 : w2T ≡ pickLL d l r)
               → (w3 : IndexLL w1T w2T)
               → (w4 : subst₂ IndexLL w1 w2 w3 ≡ ind)
               →   subst₂ IndexLL w1 (replLL-id-abs rll d ind w2)
                    (ic {il = il} d
                      (subst (IndexLL w1T) (sym (trans (pickLL-eq d pickLL pickLL w2T l r w2T refl refl) (sym (pickLL-id d w2T)))) w3))
                 ≡
                   ic d ind
a≤ᵢb-morph-id-abs {l = l} {r} {il} {d = d} refl refl w3 refl = a≤ᵢb-morph-id-abs1 e q where
  e = (cong₂ (λ x → _<_>_ x il)
        (trans (pickLL-eq d pickLL (λ _ _ _ → l) l r l r refl refl)
          (sym (pickLL-id d l)))
          (trans (pickLL-eq d (λ _ _ _ → r) pickLL l r l r refl refl)
            (sym (pickLL-id d r))))
  q = (sym (trans
             (pickLL-eq d pickLL pickLL (pickLL d l r) l r (pickLL d l r) refl refl)
             (sym (pickLL-id d (pickLL d l r)))))


a≤ᵢb-morph-id : ∀{i u ll rll}
                → (ind : IndexLL {i} {u} rll ll)
                → subst₂ (λ x y → IndexLL x y) (rpl↓ rll ind) (replLL-id ind) (a≤ᵢb-morph ind ind) ≡ ind
a≤ᵢb-morph-id ↓ = refl
a≤ᵢb-morph-id {rll = rll} (ic {l = l} {r} d ind) = a≤ᵢb-morph-id-abs (rpl↓ rll ind) (replLL-id ind) (a≤ᵢb-morph ind ind {rll}) (a≤ᵢb-morph-id ind) 






replLL-a≤b≡a : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll) → ∀ {gll}
               → (ind : IndexLL rll ll) → ∀ frll → {{lt : emi ≤ᵢ ind}}
               → replLL (a≤ᵢb-morph emi ind {frll = frll}) gll ≡ replLL emi gll
replLL-a≤b≡a .↓ ind _ {{lt = ≤ᵢ↓}} = refl
replLL-a≤b≡a (ic {r = r} {il} ic← emi) (ic _ ind) _ {{≤ᵢic}} = cong (λ z → z < il > r) (replLL-a≤b≡a emi ind _)
replLL-a≤b≡a (ic {l = l} {il = il} ic→ emi) (ic _ ind) _ {{≤ᵢic}} = cong (λ z → l < il > z) (replLL-a≤b≡a emi ind _)



mutual 
  
  ¬ord-morph-abs : ∀ {i u} {l : LinLogic i {u}} {il}
      {r rll fll : LinLogic i} {de} {di}
      {emi  : IndexLL fll (pickLL de l r)}
      {ind : IndexLL rll (pickLL di l r)}
      {frll : LinLogic i}
      → DecICT de di
      → (nord : ¬ Orderedᵢ (ic {il = il} di ind) (ic de emi))
      → IndexLL fll
         (pickLL di (replLL ind frll) l < il > pickLL di r (replLL ind frll))
  ¬ord-morph-abs {l = l} {r = r} {de = de} {emi = emi} {ind} {frll} (yes refl) nord
    = ic de
         (subst
            (IndexLL _)
            (sym (trans (pickLL-eq de pickLL pickLL _ l r _ refl refl) (sym (pickLL-id de (replLL ind frll)))))
            (¬ord-morph emi {ind} {frll} (λ p → nord (ord-ext p))))
  ¬ord-morph-abs {l = l} {r = r} {de = de} {di} {emi} {ind} {frll} (no ¬p) nord = ic de (subst (IndexLL _) (sym (pickLL-neq de di ¬p pickLL pickLL _ _ _ _ refl refl)) emi)
  
  
  ¬ord-morph : ∀{i u rll ll fll} → (emi : IndexLL {i} {u} fll ll)
               → {ind : IndexLL rll ll} → ∀ {frll} → (nord : ¬ Orderedᵢ ind emi)
               → IndexLL fll (replLL ind frll)
  ¬ord-morph emi {ind = ↓} nord = ⊥-elim (nord it)
  ¬ord-morph ↓ {ind = (ic _ _)} nord = ⊥-elim (nord it)
  ¬ord-morph (ic de emi) {ind = (ic di ind)} {frll} nord
    = ¬ord-morph-abs (isEqICT de di) nord 
  



mutual

  ¬ord-morph-¬ord-ir-abs : ∀ {i u} {l : LinLogic i {u}} {il}
       {r rll fll : LinLogic i} {de} {emi : IndexLL fll (pickLL de l r)}
       {di} {ind : IndexLL rll (pickLL di l r)} {frll : LinLogic i}
       → (deq : DecICT de di)
       → (nord nord2 : Orderedᵢ (ic {il = il} di ind) (ic de emi) → ⊥)
       →   ¬ord-morph-abs {frll = frll} deq nord
         ≡
           ¬ord-morph-abs deq nord2
  ¬ord-morph-¬ord-ir-abs {l = l} {r = r} {fll = fll} {de = de} {ind = ind} {frll = frll} (yes refl) nord nord2
    = cong (λ z → ic de
             (subst
               (IndexLL fll)
               (sym (trans (pickLL-eq de pickLL pickLL (replLL ind frll) l r (replLL ind frll) refl refl) (sym (pickLL-id de (replLL ind frll)))))
               z)) (¬ord-morph-¬ord-ir frll (λ p → nord (ord-ext p)) (λ p → nord2 (ord-ext p)))
  ¬ord-morph-¬ord-ir-abs (no ¬p) nord nord2 = refl


  ¬ord-morph-¬ord-ir : ∀{i u rll ll fll} → {emi : IndexLL {i} {u} fll ll}
                       → {ind : IndexLL rll ll} → ∀ frll → (nord nord2 : ¬ Orderedᵢ ind emi)
                       → ¬ord-morph emi {ind = ind} {frll} nord ≡ ¬ord-morph emi nord2
  ¬ord-morph-¬ord-ir {emi = ↓} _ nord nord2 = ⊥-elim (nord it)
  ¬ord-morph-¬ord-ir {emi = (ic _ emi)} {ind = ↓} _ nord nord2 = ⊥-elim (nord it)
  ¬ord-morph-¬ord-ir {emi = ice@(ic de emi)} {ind = ici@(ic di ind)} _ nord nord2 = ¬ord-morph-¬ord-ir-abs (isEqICT de di) nord nord2






replLL-¬ordab≡ba-abs2 : ∀ {de i u} {l : LinLogic i {u}} {il}
         {r rll fll : LinLogic i} {emi : IndexLL fll (pickLL de l r)}
         {gll : LinLogic i} {ind : IndexLL rll (pickLL de l r)}
         {frll : LinLogic i}
         (nord : Orderedᵢ ind emi → ⊥)
         (fnord : Orderedᵢ emi ind → ⊥)
         → replLL (¬ord-morph emi {ind = ind} {frll} nord) gll ≡ replLL (¬ord-morph ind {ind = emi} {gll} fnord) frll
         → 
                        (pickLL de
                         (replLL
                          (subst (IndexLL fll)
                           (sym
                            (trans
                             (pickLL-eq de pickLL pickLL (replLL ind frll) l r (replLL ind frll)
                              refl refl)
                             (sym (pickLL-id de (replLL ind frll)))))
                           (¬ord-morph emi nord))
                          gll)
                         (pickLL de (replLL ind frll) l)
                         < il >
                         pickLL de (pickLL de r (replLL ind frll))
                         (replLL
                          (subst (IndexLL fll)
                           (sym
                            (trans
                             (pickLL-eq de pickLL pickLL (replLL ind frll) l r (replLL ind frll)
                              refl refl)
                             (sym (pickLL-id de (replLL ind frll)))))
                           (¬ord-morph emi nord))
                          gll))
                        ≡
                        (pickLL de
                         (replLL
                          (subst (IndexLL rll)
                           (sym
                            (trans
                             (pickLL-eq de pickLL pickLL (replLL emi gll) l r (replLL emi gll)
                              refl refl)
                             (sym (pickLL-id de (replLL emi gll)))))
                           (¬ord-morph ind fnord))
                          frll)
                         (pickLL de (replLL emi gll) l)
                         < il >
                         pickLL de (pickLL de r (replLL emi gll))
                         (replLL
                          (subst (IndexLL rll)
                           (sym
                            (trans
                             (pickLL-eq de pickLL pickLL (replLL emi gll) l r (replLL emi gll)
                              refl refl)
                             (sym (pickLL-id de (replLL emi gll)))))
                           (¬ord-morph ind fnord))
                          frll))
replLL-¬ordab≡ba-abs2 {ic←} _ _ eq = cong (λ z → z < _ > _) eq
replLL-¬ordab≡ba-abs2 {ic→} _ _ eq = cong (λ z → _ < _ > z) eq


mutual

  replLL-¬ordab≡ba-abs : ∀ {i u} {l : LinLogic i {u}} {il}
       {r rll fll : LinLogic i} {de} {emi : IndexLL fll (pickLL de l r)}
       (gll : LinLogic i) {di} {ind : IndexLL rll (pickLL di l r)}
       (frll : LinLogic i)
       (nord : Orderedᵢ (ic {il = il} di ind) (ic de emi) → ⊥)
       (fnord : Orderedᵢ (ic {il = il} de emi) (ic di ind) → ⊥)
       → ∀ w w1
       →   replLL (¬ord-morph-abs {frll = frll} w nord) gll
         ≡
           replLL (¬ord-morph-abs {frll = gll} w1 fnord) frll
  replLL-¬ordab≡ba-abs {l = l} {r = r} {de = de} gll {di = di} frll nord fnord (yes refl) (yes refl) = replLL-¬ordab≡ba-abs2 {de = de} {l = l} {r = r} nnord nfnord (replLL-¬ordab≡ba gll frll nnord nfnord) where
    nnord = (λ p → nord (ord-ext p))
    nfnord = (λ p → fnord (ord-ext p))
  replLL-¬ordab≡ba-abs gll frll nord fnord (yes p) (no ~p) = ⊥-elim (~ict⇒¬≡ ~p (sym p))
  replLL-¬ordab≡ba-abs gll frll nord fnord (no ~p) (yes p) = ⊥-elim (~ict⇒¬≡ ~p (sym p))
  replLL-¬ordab≡ba-abs {de = ic←} gll {ic←} frll nord fnord (no ()) (no p₁)
  replLL-¬ordab≡ba-abs {de = ic←} gll {ic→} frll nord fnord (no p) (no p₁) = refl
  replLL-¬ordab≡ba-abs {de = ic→} gll {ic←} frll nord fnord (no p) (no p₁) = refl
  replLL-¬ordab≡ba-abs {de = ic→} gll {ic→} frll nord fnord (no ()) (no p₁)

  replLL-¬ordab≡ba : ∀{i u rll ll fll}
    → {emi : IndexLL {i} {u} fll ll} → ∀ gll
    → {ind : IndexLL rll ll} → ∀ frll
    → (nord : ¬ Orderedᵢ ind emi)
    → (fnord : ¬ Orderedᵢ emi ind)
    → replLL (¬ord-morph emi {ind = ind} {frll} nord) gll ≡ replLL (¬ord-morph ind {ind = emi} {gll} fnord) frll
  replLL-¬ordab≡ba {emi = ↓} _ _ nord = ⊥-elim (nord it)
  replLL-¬ordab≡ba {emi = (ic _ emi)} _ {ind = ↓} _ nord fnord = ⊥-elim (nord it)
  replLL-¬ordab≡ba {emi = ice@(ic de emi)} gll {ind = ici@(ic di ind)} frll nord fnord = replLL-¬ordab≡ba-abs gll frll nord fnord (isEqICT de di) (isEqICT di de)





lemma₁-¬ord-a≤ᵢb-abs2 : ∀ {i u d w} {l r : LinLogic i {u}} {il}
            {pll rll ell fll : LinLogic i}
            → {a    : IndexLL fll (pickLL d l r)}
            → {b    : IndexLL rll (pickLL d l r)}
            → {{lt : a ≤ᵢ b}}
            → {c    : IndexLL pll
                      (pickLL w (pickLL w (replLL b ell) l)
                        (pickLL w r (replLL b ell)))}
            → (nord : ¬
                    Orderedᵢ
                    (ic {il = il} w
                     (subst (IndexLL (replLL (b -ᵢ a) ell))
                      (sym
                       (trans
                        (pickLL-eq w pickLL pickLL (replLL b ell) l r (replLL b ell)
                         refl refl)
                        (sym (pickLL-id w (replLL b ell)))))
                      (a≤ᵢb-morph a b)))
                    (ic w c))
            → Σ (IndexLL pll (replLL b ell)) (λ c → ¬ Orderedᵢ (a≤ᵢb-morph a b) c)
lemma₁-¬ord-a≤ᵢb-abs2 {w = ic←} {c = c} nord = c , λ p → nord (ord-ext p)
lemma₁-¬ord-a≤ᵢb-abs2 {w = ic→} {c = c} nord = c , λ p → nord (ord-ext p)

mutual

  lemma₁-¬ord-a≤ᵢb-abs : ∀ {i u d dc} {l r : LinLogic i {u}} {il}
            {pll rll ell fll : LinLogic i}
            → {a    : IndexLL fll (pickLL d l r)}
            → {b    : IndexLL rll (pickLL d l r)}
            → {{lt : a ≤ᵢ b}}
            → {c    : IndexLL pll
                      (pickLL dc (pickLL d (replLL b ell) l)
                        (pickLL d r (replLL b ell)))}
            → (nord : ¬
                    Orderedᵢ
                    (ic {il = il} d
                     (subst (IndexLL (replLL (b -ᵢ a) ell))
                      (sym
                       (trans
                        (pickLL-eq d pickLL pickLL (replLL b ell) l r (replLL b ell)
                         refl refl)
                        (sym (pickLL-id d (replLL b ell)))))
                      (a≤ᵢb-morph a b)))
                    (ic dc c))
            → DecICT d dc
            → IndexLL pll (l < il > r)
  lemma₁-¬ord-a≤ᵢb-abs {d = d} nord (yes refl) = ic d (lemma₁-¬ord-a≤ᵢb (proj₂ (lemma₁-¬ord-a≤ᵢb-abs2 {d = d} nord)))
  lemma₁-¬ord-a≤ᵢb-abs {d = d} {dc = dc} {l = l} {r} {ell = ell} {b = b} {c = c} nord (no p) = ic dc (subst (IndexLL _) (pickLL-neq dc d (sym (~ict-sym p)) pickLL pickLL (replLL b ell) l r (replLL b ell) refl refl) c )


-- This is the reverse of ¬ord-morph
  lemma₁-¬ord-a≤ᵢb : ∀{i u ll pll rll fll}
        → {emi : IndexLL {i} {u} fll ll}
        → {ind : IndexLL rll ll} → ∀ {ell} → {{lt : emi ≤ᵢ ind}}
        → {omi : IndexLL pll (replLL ind ell)}
        → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind {ell}) omi)
        → IndexLL pll ll
  lemma₁-¬ord-a≤ᵢb {ind = ind} {{≤ᵢ↓}} nord = ⊥-elim (nord it)
  lemma₁-¬ord-a≤ᵢb {{≤ᵢic}} {omi = ↓} nord = ⊥-elim (nord it)
  lemma₁-¬ord-a≤ᵢb {emi = ica@(ic d a)} {ind = icb@(ic .d b)} {{≤ᵢic}} {omi = icc@(ic dc c)} nord = lemma₁-¬ord-a≤ᵢb-abs nord (isEqICT d dc)








¬ord-morph⇒¬ord-abs2 : ∀ {de i u} {l : LinLogic i {u}} {il}
                         {r rll fll : LinLogic i} {emi : IndexLL fll (pickLL de l r)}
                         {ind : IndexLL rll (pickLL de l r)} {frll : LinLogic i}
                         {nord : Orderedᵢ ind emi → ⊥} →
                       (Orderedᵢ (a≤ᵢb-morph ind ind {frll})
                        (¬ord-morph emi nord) →
                        ⊥) →
                       Orderedᵢ
                       (ic {il = il} de
                        (subst (IndexLL (replLL (ind -ᵢ ind) frll))
                         (sym
                          (trans
                           (pickLL-eq de pickLL pickLL (replLL ind frll) l r (replLL ind frll)
                            refl refl)
                           (sym (pickLL-id de (replLL ind frll)))))
                         (a≤ᵢb-morph ind ind)))
                       (ic de
                        (subst (IndexLL fll)
                         (sym
                          (trans
                           (pickLL-eq de pickLL pickLL (replLL ind frll) l r (replLL ind frll)
                            refl refl)
                           (sym (pickLL-id de (replLL ind frll)))))
                         (¬ord-morph emi nord))) →
                       ⊥
¬ord-morph⇒¬ord-abs2 {ic←} is = λ p → is (ord-spec p)
¬ord-morph⇒¬ord-abs2 {ic→} is = λ p → is (ord-spec p)



mutual

  ¬ord-morph⇒¬ord-abs : ∀ {i u} {l : LinLogic i {u}} {il}
       {r rll fll : LinLogic i} {de} {emi : IndexLL fll (pickLL de l r)}
       {di} {ind : IndexLL rll (pickLL di l r)} {frll : LinLogic i}
       (nord : Orderedᵢ (ic {il = il} di ind) (ic de emi) → ⊥)
       → (w : DecICT de di)
       → Orderedᵢ
            (ic di
             (subst (IndexLL (replLL (ind -ᵢ ind) frll))
              (sym
               (trans
                (pickLL-eq di pickLL pickLL (replLL ind frll) l r (replLL ind frll)
                 refl refl)
                (sym (pickLL-id di (replLL ind frll)))))
              (a≤ᵢb-morph ind ind)))
            (¬ord-morph-abs w nord) → ⊥
  ¬ord-morph⇒¬ord-abs {frll = frll} nord (yes refl) = ¬ord-morph⇒¬ord-abs2 (¬ord-morph⇒¬ord nnord) where
    nnord = λ p → nord (ord-ext p)
  ¬ord-morph⇒¬ord-abs {de = de} {di = di} nord (no p) = λ x → ~ict⇒¬≡ p (ord⇒icteq refl refl x)



  ¬ord-morph⇒¬ord : ∀{i u rll ll fll} → {emi : IndexLL {i} {u} fll ll}
      → {ind : IndexLL rll ll} → ∀ {frll} → (nord : ¬ Orderedᵢ ind emi)
      → ¬ Orderedᵢ (a≤ᵢb-morph ind ind {frll}) (¬ord-morph emi nord)
  ¬ord-morph⇒¬ord {emi = ↓} nord = ⊥-elim (nord it)
  ¬ord-morph⇒¬ord {emi = (ic _ emi)} {ind = ↓} nord = ⊥-elim (nord it)
  ¬ord-morph⇒¬ord {emi = (ic de emi)} {ind = (ic di ind)} {frll} nord = ¬ord-morph⇒¬ord-abs nord (isEqICT de di)
  




mutual

  rlemma₁⇒¬ord-abs : ∀ {i u} {l r : LinLogic i {u}} {d} {rll : LinLogic i}
                 {ind : IndexLL rll (pickLL d l r)} {ell : LinLogic i} {il}
                 {fll : LinLogic i} {emi : IndexLL fll (pickLL d l r)}
                 {pll : LinLogic i} {{ieq : emi ≤ᵢ ind}} {dc}
                 {omi
                  : IndexLL pll
                    (pickLL dc (pickLL d (replLL ind ell) l)
                     (pickLL d r (replLL ind ell)))}
                 (nord
                  : Orderedᵢ
                    (ic {il = il} d
                     (subst (IndexLL (replLL (ind -ᵢ emi) ell))
                      (sym
                       (trans
                        (pickLL-eq d pickLL pickLL (replLL ind ell) l r (replLL ind ell)
                         refl refl)
                        (sym (pickLL-id d (replLL ind ell)))))
                      (a≤ᵢb-morph emi ind)))
                    (ic dc omi) →
                    ⊥)
                 (w : DecICT d dc) →
               Orderedᵢ (ic d emi) (lemma₁-¬ord-a≤ᵢb-abs nord w) → ⊥
  rlemma₁⇒¬ord-abs {d = d} nord (yes refl) = λ x → r (ord-spec x) where
    r = rlemma₁⇒¬ord (proj₂ (lemma₁-¬ord-a≤ᵢb-abs2 {d = d} {w = d} nord))
  rlemma₁⇒¬ord-abs {d = d} {dc = dc} nord (no p) = λ x → ~ict⇒¬≡ p (sym (ord⇒icteq refl refl x)) 


  rlemma₁⇒¬ord : ∀{i u ll pll rll fll}
     → {emi : IndexLL {i} {u} fll ll}
     → {ind : IndexLL rll ll} → ∀ {ell} → {{lt : emi ≤ᵢ ind}}
     → {omi : IndexLL pll (replLL ind ell)}
     → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind {ell}) omi)
     → ¬ Orderedᵢ emi (lemma₁-¬ord-a≤ᵢb nord)
  rlemma₁⇒¬ord {{lt = ≤ᵢ↓}} {omi} nord = ⊥-elim (nord it)
  rlemma₁⇒¬ord {{lt = ≤ᵢic}} {↓} nord = ⊥-elim (nord it)
  rlemma₁⇒¬ord {emi = (ic d emi)} {ind = (ic .d ind)} {{lt = ≤ᵢic}} {omi = (ic dc omi)} nord = rlemma₁⇒¬ord-abs nord (isEqICT d dc)






  ¬ord-morph$lemma₁≡I-abs3 : ∀ {d i u} {l : LinLogic i {u}}
                             {r : LinLogic i} {pll : LinLogic i}
                             {bind : IndexLL pll (pickLL d l r)} {ell : LinLogic i} {il}
                             {fll : LinLogic i} {x : IndexLL fll (pickLL d l r)}
                             {cll : LinLogic i} {{ieq : x ≤ᵢ bind}}
                             {lind
                              : IndexLL cll
                                (pickLL d (pickLL d (replLL bind ell) l)
                                 (pickLL d r (replLL bind ell)))}
                             (nord
                              : Orderedᵢ
                                (ic {il = il} d
                                 (subst (IndexLL (replLL (bind -ᵢ x) ell))
                                  (sym
                                   (trans
                                    (pickLL-eq d pickLL pickLL (replLL bind ell) l r
                                     (replLL bind ell) refl refl)
                                    (sym (pickLL-id d (replLL bind ell)))))
                                  (a≤ᵢb-morph x bind)))
                                (ic d lind) →
                                ⊥)
                             (lnord
                              : Orderedᵢ (ic {il = il} d bind)
                                (ic {il = il} d (lemma₁-¬ord-a≤ᵢb (proj₂ (lemma₁-¬ord-a≤ᵢb-abs2 {d = d} nord)))) →
                                ⊥) →
                           ¬ord-morph (lemma₁-¬ord-a≤ᵢb (proj₂ (lemma₁-¬ord-a≤ᵢb-abs2 nord)))
                           (λ z → lnord (ord-ext z))
                           ≡ proj₁ (lemma₁-¬ord-a≤ᵢb-abs2 {d = d} nord) →
                           ic {il = il} d
                           (subst (IndexLL cll)
                            (sym
                             (trans
                              (pickLL-eq d pickLL pickLL (replLL bind ell) l r (replLL bind ell)
                               refl refl)
                              (sym (pickLL-id d (replLL bind ell)))))
                            (¬ord-morph (lemma₁-¬ord-a≤ᵢb (proj₂ (lemma₁-¬ord-a≤ᵢb-abs2 {d = d} nord)))
                             (λ p → lnord (ord-ext p))))
                           ≡ ic d lind
  ¬ord-morph$lemma₁≡I-abs3 {ic←} _ _ eq = cong (λ z → ic ic← z) eq
  ¬ord-morph$lemma₁≡I-abs3 {ic→} _ _ eq = cong (λ z → ic ic→ z) eq

mutual

  ¬ord-morph$lemma₁≡I-abs2 : ∀ {d i u} {l r pll : LinLogic i {u}}
                             {bind : IndexLL pll (pickLL d l r)} {ell : LinLogic i} {il}
                             {fll : LinLogic i} {x : IndexLL fll (pickLL d l r)}
                             {cll : LinLogic i} {{ieq : x ≤ᵢ bind}}
                             {lind
                              : IndexLL cll
                                (pickLL d (pickLL d (replLL bind ell) l)
                                 (pickLL d r (replLL bind ell)))}
                             (w : DecICT d d)
                             (nord
                              : Orderedᵢ
                                (ic {il = il} d
                                 (subst (IndexLL (replLL (bind -ᵢ x) ell))
                                  (sym
                                   (trans
                                    (pickLL-eq d pickLL pickLL (replLL bind ell) l r
                                     (replLL bind ell) refl refl)
                                    (sym (pickLL-id d (replLL bind ell)))))
                                  (a≤ᵢb-morph x bind)))
                                (ic d lind) →
                                ⊥)
                             (lnord
                              : Orderedᵢ (ic {il = il} d bind)
                                (ic d (lemma₁-¬ord-a≤ᵢb (proj₂ (lemma₁-¬ord-a≤ᵢb-abs2 {d = d} nord)))) →
                                ⊥) →
                           ¬ord-morph-abs w lnord ≡ ic d lind
  ¬ord-morph$lemma₁≡I-abs2 (yes refl) nord lnord = ¬ord-morph$lemma₁≡I-abs3 nord lnord r where
    r = ¬ord-morph$lemma₁≡I (proj₂ (lemma₁-¬ord-a≤ᵢb-abs2 nord)) (λ z → lnord (ord-ext z))
  ¬ord-morph$lemma₁≡I-abs2 (no p) nord lnord = ⊥-elim (~ict⇒¬≡ p refl) 


  ¬ord-morph$lemma₁≡I-abs : ∀ {i u} {l r : LinLogic i {u}} {d}
                            {pll : LinLogic i} {bind : IndexLL pll (pickLL d l r)}
                            {ell : LinLogic i} {il} {fll : LinLogic i}
                            {x : IndexLL fll (pickLL d l r)} {cll : LinLogic i}
                            {{ieq : x ≤ᵢ bind}} {dc}
                            {lind
                             : IndexLL cll
                               (pickLL dc (pickLL d (replLL bind ell) l)
                                (pickLL d r (replLL bind ell)))}
                            (w : DecICT d dc)
                            (nord
                             : Orderedᵢ
                               (ic  {il = il} d
                                (subst (IndexLL (replLL (bind -ᵢ x) ell))
                                 (sym
                                  (trans
                                   (pickLL-eq d pickLL pickLL (replLL bind ell) l r
                                    (replLL bind ell) refl refl)
                                   (sym (pickLL-id d (replLL bind ell)))))
                                 (a≤ᵢb-morph x bind)))
                               (ic dc lind) →
                               ⊥)
                            (lnord : Orderedᵢ (ic d bind) (lemma₁-¬ord-a≤ᵢb-abs nord w) → ⊥) →
                          ¬ord-morph (lemma₁-¬ord-a≤ᵢb-abs nord w) lnord ≡ ic dc lind
  ¬ord-morph$lemma₁≡I-abs {d = d}(yes refl) nord lnord = ¬ord-morph$lemma₁≡I-abs2 (isEqICT d d) nord lnord
  ¬ord-morph$lemma₁≡I-abs {d = ic←} {dc = ic←} (no p) nord lnord = ⊥-elim (~ict⇒¬≡ p refl)
  ¬ord-morph$lemma₁≡I-abs {d = ic←} {dc = ic→} (no p) nord lnord = refl
  ¬ord-morph$lemma₁≡I-abs {d = ic→} {dc = ic←} (no p) nord lnord = refl
  ¬ord-morph$lemma₁≡I-abs {d = ic→} {dc = ic→} (no p) nord lnord = ⊥-elim (~ict⇒¬≡ p refl)


  ¬ord-morph$lemma₁≡I : ∀{i u pll ll cll fll ell} → {emi : IndexLL {i} {u} fll ll} → {ind : IndexLL {i} {u} pll ll} → {{lt : emi ≤ᵢ ind}} → {lind : IndexLL cll (replLL ind ell)} → (nord : ¬ Orderedᵢ (a≤ᵢb-morph emi ind {ell}) lind) → (lnord : ¬ Orderedᵢ ind (lemma₁-¬ord-a≤ᵢb nord))
         → (¬ord-morph (lemma₁-¬ord-a≤ᵢb nord) lnord ≡ lind)
  ¬ord-morph$lemma₁≡I {emi = .↓} {ind} {{≤ᵢ↓}} nord lnord = ⊥-elim (nord it)
  ¬ord-morph$lemma₁≡I {emi = .(ic _ _)} {.(ic _ _)} {{≤ᵢic}} {↓} nord lnord = ⊥-elim (nord it)
  ¬ord-morph$lemma₁≡I {emi = (ic d _)} {.(ic _ _)} {{≤ᵢic}} {ic dc lind} nord lnord = ¬ord-morph$lemma₁≡I-abs (isEqICT d dc) nord lnord 



_+ᵢ_ : ∀{i u pll cll ll} → IndexLL {i} {u} pll ll → IndexLL cll pll → IndexLL cll ll
↓ +ᵢ b = b
ic d a +ᵢ b = ic d (a +ᵢ b)


instance
  +ᵢ⇒l≤ᵢ+ᵢ : ∀{i u pll cll ll} → {ind : IndexLL {i} {u} pll ll} → {lind : IndexLL cll pll}
             → ind ≤ᵢ (ind +ᵢ lind)
  +ᵢ⇒l≤ᵢ+ᵢ {ind = ↓} = ≤ᵢ↓
  +ᵢ⇒l≤ᵢ+ᵢ {ind = ic _ _} = ≤ᵢic


a+↓≡a : ∀{i u pll ll} → {a : IndexLL {i} {u} pll ll} → a +ᵢ ↓ ≡ a
a+↓≡a {a = ↓} = refl
a+↓≡a {a = ic d a} = cong (λ z → ic d z) a+↓≡a


[a+b]-a=b : ∀{i u rll ll fll} → (a : IndexLL {i} {u} fll ll)
          → (b : IndexLL rll fll)
          → ((a +ᵢ b) -ᵢ a) ≡ b
[a+b]-a=b ↓ b = refl
[a+b]-a=b (ic d a) b = [a+b]-a=b a b


a+[b-a]=b : ∀{i u rll ll fll} → (a : IndexLL {i} {u} fll ll)
            → (b : IndexLL rll ll)
            → {{lt : a ≤ᵢ b}}
            → (a +ᵢ (b -ᵢ a))  ≡ b
a+[b-a]=b .↓ b {{≤ᵢ↓}} = refl
a+[b-a]=b (ic _ a) (ic _ b) {{≤ᵢic}} = cong (λ z → ic _ z) (a+[b-a]=b a b)




drepl=>repl+ : ∀{i u pll ll cll frll} → (ind : IndexLL {i} {u} pll ll) → (lind : IndexLL cll pll)
               → (replLL ind (replLL lind frll)) ≡ replLL (ind +ᵢ lind) frll
drepl=>repl+ ↓ lind = refl
drepl=>repl+ (ic d ind) lind = cong (λ z → (pickLL d z _ < _ > pickLL d _ z)) (drepl=>repl+ ind lind)






repl-r⇒l-lt-lemma : ∀ {d i u} {l r pll ell : LinLogic i {u}}
                      {ind : IndexLL pll (pickLL d l r)} {cll : LinLogic i}
                      {x
                       : IndexLL cll
                         (pickLL d (pickLL d (replLL ind ell) l)
                          (pickLL d r (replLL ind ell)))}
                      {{lt
                        : subst (IndexLL (replLL (ind -ᵢ ind) ell))
                          (sym
                           (trans
                            (pickLL-eq d pickLL pickLL (replLL ind ell) l r (replLL ind ell)
                             refl refl)
                            (sym (pickLL-id d (replLL ind ell)))))
                          (a≤ᵢb-morph ind ind)
                          ≤ᵢ x}} →
                    a≤ᵢb-morph ind ind ≤ᵢ
                    subst (IndexLL cll)
                    (trans
                     (pickLL-eq d pickLL pickLL (replLL ind ell) l r (replLL ind ell)
                      refl refl)
                     (sym (pickLL-id d (replLL ind ell))))
                    x
repl-r⇒l-lt-lemma {ic←} {{lt = lt}} = lt
repl-r⇒l-lt-lemma {ic→} {{lt = lt}} = lt



repl-r⇒l-lemma : ∀ {d i u} {l r pll ell : LinLogic i {u}}
                   {ind : IndexLL pll (pickLL d l r)} {cll : LinLogic i}
                   {x
                    : IndexLL cll
                      (pickLL d (pickLL d (replLL ind ell) l)
                       (pickLL d r (replLL ind ell)))}
                   {il} {frll : LinLogic i}
                   {{lt
                    : subst (IndexLL (replLL (ind -ᵢ ind) ell))
                      (sym
                       (trans
                        (pickLL-eq d pickLL pickLL (replLL ind ell) l r (replLL ind ell)
                         refl refl)
                        (sym (pickLL-id d (replLL ind ell)))))
                      (a≤ᵢb-morph ind ind)
                      ≤ᵢ x}}
                   {{w
                     : a≤ᵢb-morph ind ind ≤ᵢ
                       subst (IndexLL cll)
                       (trans
                        (pickLL-eq d pickLL pickLL (replLL ind ell) l r (replLL ind ell)
                         refl refl)
                        (sym (pickLL-id d (replLL ind ell))))
                       x}}
                {lteq : repl-r⇒l-lt-lemma {d = d} {{lt}} ≡ w}
                 →
                 replLL ind
                 (replLL
                  (subst (λ x₁ → x₁)
                   (cong (IndexLL cll) (cong (λ z → replLL z ell) (ind-ᵢind≡↓ ind)))
                   (subst (IndexLL cll)
                    (trans
                     (pickLL-eq d pickLL pickLL (replLL ind ell) l r (replLL ind ell)
                      refl refl)
                     (sym (pickLL-id d (replLL ind ell))))
                    x
                    -ᵢ a≤ᵢb-morph ind ind))
                  frll)
                 ≡
                 replLL
                 (subst (IndexLL cll)
                  (trans
                   (pickLL-eq d pickLL pickLL (replLL ind ell) l r (replLL ind ell)
                    refl refl)
                   (sym (pickLL-id d (replLL ind ell))))
                  x)
                 frll →
                 (pickLL d
                  (replLL ind
                   (replLL
                    (subst (λ x₁ → x₁)
                     (cong (IndexLL cll) (cong (λ z → replLL z ell) (ind-ᵢind≡↓ ind)))
                     (x -ᵢ
                      subst (IndexLL (replLL (ind -ᵢ ind) ell))
                      (sym
                       (trans
                        (pickLL-eq d pickLL pickLL (replLL ind ell) l r (replLL ind ell)
                         refl refl)
                        (sym (pickLL-id d (replLL ind ell)))))
                      (a≤ᵢb-morph ind ind)))
                    frll))
                  l
                  < il >
                  pickLL d r
                  (replLL ind
                   (replLL
                    (subst (λ x₁ → x₁)
                     (cong (IndexLL cll) (cong (λ z → replLL z ell) (ind-ᵢind≡↓ ind)))
                     (x -ᵢ
                      subst (IndexLL (replLL (ind -ᵢ ind) ell))
                      (sym
                       (trans
                        (pickLL-eq d pickLL pickLL (replLL ind ell) l r (replLL ind ell)
                         refl refl)
                        (sym (pickLL-id d (replLL ind ell)))))
                      (a≤ᵢb-morph ind ind)))
                    frll)))
                 ≡
                 (pickLL d (replLL x frll) (pickLL d (replLL ind ell) l) < il >
                  pickLL d (pickLL d r (replLL ind ell)) (replLL x frll))
repl-r⇒l-lemma {d = ic←} {r = r} {il = il} {lteq = refl} eq = cong (λ z → z < il > r) eq
repl-r⇒l-lemma {d = ic→} {l = l} {il = il} {lteq = refl} eq = cong (λ z → l < il > z) eq


repl-r⇒l : ∀{i u pll ll cll} → ∀ frll ell → (ind : IndexLL {i} {u} pll ll) → (x : IndexLL cll (replLL ind ell)) → let uind = a≤ᵢb-morph ind ind {ell}
        in {{lt : uind ≤ᵢ x}}
        → (replLL ind (replLL (ind-rpl↓1 ind (x -ᵢ uind)) frll) ≡ replLL x frll)
repl-r⇒l _ _ ↓ x {{≤ᵢ↓}} = refl
repl-r⇒l {cll = cll} frll ell (ic {l = l} {r = r} d ind) (ic .d x) {{≤ᵢic {{lt}}}} = repl-r⇒l-lemma {d = d} {{w = nlt}} {refl} is where
  nx = subst (IndexLL _) (trans (pickLL-eq d pickLL pickLL _ l r _ refl refl) (sym (pickLL-id d (replLL ind ell)))) x
  nlt = repl-r⇒l-lt-lemma {d = d} {{lt}}
  is = repl-r⇒l frll ell ind nx {{nlt}}







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




