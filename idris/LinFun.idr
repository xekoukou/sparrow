module LinFun


import public LinT

%access public export

%default total


-- IMPORTANT TODO We could only allow parallel execution of Embedding that have disjoint input. This way, we can reuse LFun and feed it into the epoller.


mutual
  ||| Linear Function : It is used to express the use of resources/Inputs and their transformation to other resources/outputs.
  ||| All inputs are used exactly one time.
  ||| @ll The input linear logic sequence.
  ||| @rll The output linear logic sequence.
  data LFun : (ll : LinLogic) -> (rll : LinLogic) -> Nat -> Type where
    ||| The identity function.
    LFunId : LFun ll ll (S Z)
    ||| Another linear function is called and the transformation then continues from the results of that function.
    ||| @i determines the sub-tree which the linear function will take as input and transform.
    Emb    : (i : IndexLL ll pll) -> (lFun : LFun pll ell en) -> {auto prf : lFunUsesInput lFun = True} -> LFun (replLL ll i ell) rll n -> LFun ll rll (S (en + n))
    |||
    Call   : (lFun : Inf $ LFun ll crll k) -> {auto prf : lFunUsesInput lFun = True} -> LFun crll rll n -> LFun ll rll (S n)
    ||| Transformations of the tree to forms that can be used as inputs to known linear functions.
    Trans  : (ltr : LLTr ll orll) -> LFun orll rll n -> LFun ll rll (S n)
    ||| Transformation of input to output through consuption of the resource or through communication.
    Com    : {rll : LinLogic} -> {isf : IsFiniteLL ll} -> {risf : IsFiniteLL rll} -> {auto prfi : onlyNilOrNoNil ll isf= True} -> {auto prfi : onlyNilOrNoNil rll risf = True} -> (df : ((lDT : LinDepT ll) -> LinT lDT -> LinDepT rll)) -> LFun rll nrll n -> LFun ll nrll (S n)
  
  ||| Guarantees that all Inputs are used.
  lFunUsesInput : LFun ll rll _-> Bool
  lFunUsesInput x = lFunUsesInput' x SEmpty where
    lFunUsesInput' : LFun ll rll _-> MSetLL ll -> Bool
    lFunUsesInput' LFunId s = False
    lFunUsesInput' (Emb i lFun x {ell}) SEmpty    = lFunUsesInput' x $ SSome $ setLLAddEmpty i ell
    lFunUsesInput' (Emb i lFun x {ell}) (SSome s) = let ns = contructSetLL $ setLLAdd s i ell in case (ns) of
                                                                            SElem => True
                                                                            _     => lFunUsesInput' x $ SSome ns
    lFunUsesInput' (Call _ _) _  = True
    lFunUsesInput' (Trans ltr y) SEmpty    = lFunUsesInput' y $ SEmpty
    lFunUsesInput' (Trans ltr y) (SSome s) = lFunUsesInput' y $ SSome $ trSetLL s ltr
    lFunUsesInput' (Com _ _) _   = True





data EList : IndexLL ofl pll -> LFun pll _ _ -> LFun all _ _-> Nat -> Type where
  ENil : EList (LHere {ll=ll}) (LFunId {ll=ll}) (LFunId {ll=ll}) (S Z)
  EL : (ni : IndexLL ll pll) -> (nflFun : LFun pll ell _) -> (nlFun : LFun (replLL ll ni ell) rll n) 
  -> {flFun : LFun _ rll _} -> EList i flFun lFun k -> EList ni nflFun nlFun (n + k)

data EVect : EList ni nflFun nlFun n -> Type where
  EVNil : EVect ENil
  EV : (ni : IndexLL ll pll) -> {nflFun : LFun pll ell _} -> (nlFun : LFun (replLL ll ni ell) rll _) -> {flFun : LFun _ rll _} 
  -> {prEL : EList i flFun lFun k} -> (prL : LinDepT ll) ->  EVect prEL -> EVect $ EL ni nflFun nlFun prEL




data Conti : LinDepT prll -> LFun ll rll _ -> Nat -> Type where
  CEnd    : Conti prLDT (LFunId {ll=ll}) (S Z)
  CInter   : (lFun : LFun ll rll k) -> {flFun : LFun pll rll _} -> (el : EList ei flFun elFun n) -> EVect el 
            -> LinDepT ll -> Conti prLDT lFun (k + n)
  CNext   : (lFun : LFun ll rll k) -> {flFun : LFun pll rll _} -> (el : EList ei flFun elFun n) -> EVect el -> (prLDT : LinDepT prll) ->
            (LinT prLDT -> LinDepT ll) -> Conti prLDT lFun (k + n)

isCInter : Conti _ lFun _ -> Bool
isCInter CEnd              = False
isCInter (CInter _ _ _ _)  = True
isCInter (CNext _ _ _ _ _) = False



contiNEqSK : Conti _ _ n -> (k : Nat ** (n = S k))
contiNEqSK CEnd = (Z ** Refl)
contiNEqSK (CInter LFunId _ _ _ {n}) = (n ** Refl)
contiNEqSK (CInter (Emb _ _ _ {en} {n=n'}) _ _ _{n}) = (plus (plus en n') n ** Refl)
contiNEqSK (CInter (Trans _ _{n=n'}) _ _ _{n}) = (plus n' n ** Refl)
contiNEqSK (CInter (Com _ _{n=n'}) _ _ _ {n}) = (plus n' n ** Refl)
contiNEqSK (CInter (Call _ _{n=n'}) _ _ _ {n}) = (plus n' n ** Refl)
contiNEqSK (CNext LFunId _ _ _ _ {n}) = (n ** Refl)
contiNEqSK (CNext (Emb _ _ _ {en} {n=n'}) _ _ _ _ {n}) = (plus (plus en n') n ** Refl)
contiNEqSK (CNext (Trans _ _{n=n'}) _ _ _ _ {n}) = (plus n' n ** Refl)
contiNEqSK (CNext (Com _ _{n=n'}) _ _ _ _ {n}) = (plus n' n ** Refl)
contiNEqSK (CNext (Call _ _{n=n'}) _ _ _ _ {n}) = (plus n' n ** Refl)




lteRemoveLeft : (n,k,l : Nat) -> LTE (n + k) l -> LTE k l
lteRemoveLeft Z k l x = x
lteRemoveLeft (S j) k l x = lteRemoveLeft j k l $ lteSuccLeft x

comStep'_emb_prf1 : (en,ne,k,bnd' : Nat) -> (isBnd' : LTE (plus (plus en ne) k) bnd') -> LTE (ne + k) bnd'
comStep'_emb_prf1 en ne k bnd' isBnd' = lteRemoveLeft en (ne + k) bnd' $ rewrite (plusAssociative en ne k) in isBnd'
  


comStep' : (c : Conti _ lFun k) -> {auto prf : isCInter c = True} -> (bnd : Nat) -> (isBnd : LTE k bnd) -> (prll ** prLDT : LinDepT prll ** ull ** urll ** un ** nk ** nc : LFun ull urll un  ** Conti prLDT nc nk) 
comStep' CEnd {prf} _ _ = void $ falseNotTrue prf
comStep' (CNext _ _ _ _ _) {prf} _ _ = void $ falseNotTrue prf
comStep' (CInter (LFunId {ll}) ENil ev lDT) _ _ = (ll ** lDT ** ll ** ll ** (S Z) ** (S Z) ** LFunId ** CEnd )
comStep' (CInter LFunId (EL ei nflFun elFun pEL {n} {k}) ev lDT ) (S bnd') (LTESucc isBnd') = 
    let EV _ _ prL prEV = ev in
    comStep' (CInter elFun pEL prEV (replLDT prL ei lDT) {prLDT=lDT}) bnd' isBnd'
comStep' (CInter (Emb ni nflFun nlFun {pll} {ell} {en} {n=ne}) el ev lDT {n=k} ) (S bnd') (LTESucc isBnd')  = let tr = truncLDT lDT ni in
    case (tr) of
        Just tlDT => comStep' (CInter nflFun (EL ni nflFun nlFun el) (EV ni nlFun lDT ev) tlDT {prLDT=lDT} ) bnd' 
                     (rewrite (plusAssociative en ne k) in isBnd')
        Nothing => let ntr = ifNotTruncLDT lDT ni ell in
                   case (ntr) of
                     Just ntlDT => comStep' (CInter nlFun el ev ntlDT {prLDT=lDT}) bnd' $ comStep'_emb_prf1 en ne k bnd' isBnd'
                     _ => assert_unreachable
comStep' (CInter (Call _ _) _ _ _) _ _ = ?ddsfdf
comStep' (CInter (Trans ltr nlFun ) el ev lDT ) (S bnd') (LTESucc isBnd') = 
    comStep' (CInter nlFun el ev (trLDT lDT ltr) {prLDT=lDT}) bnd' isBnd'
comStep' (CInter (Com df nlFun {rll} {nrll}) el ev lDT {ll} {k=S q} {n=n}) bnd' isBnd' = (ll ** lDT ** rll ** nrll ** q ** (q+n) ** nlFun ** (CNext nlFun el ev lDT $ df lDT))


||| Since communications can be infinite, this function is used to find the next Comm that contains the function to compute the
||| next LinDepT given a specific input by the user that abides to the specification, ie the previous LinDepT.
||| It also contains information so that when executed again with that info, it will give the next Comm.
comStep : (c : Conti _ lFun k) -> {auto prf : isCInter c = True} -> (prll ** prLDT : LinDepT prll ** ull ** urll ** un ** nk ** nc : LFun ull urll un  ** Conti prLDT nc nk)
comStep c {k} {prf} = comStep' c {prf=prf} k lteRefl
