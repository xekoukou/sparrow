module Simul


import LinFun


%access public export

%default total




data SFun : LFun ll rll _ -> Type where
  SFunId : SFun $ LFunId
  SEmb : SFun elFun -> {auto prf : lFunUsesInput elFun = True} -> SFun nlFun -> SFun $ Emb i elFun nlFun {prf = prf}
  SCall : Inf $ SFun clFun -> {auto prf : lFunUsesInput clFun = True} -> SFun nlFun -> SFun $ Call clFun nlFun {prf = prf}
  STrans : SFun nlFun -> SFun $ Trans ltr nlFun
  SCom :  {isf : IsFiniteLL ll} -> {risf : IsFiniteLL rll} -> {auto prfi : onlyNilOrNoNil ll isf= True} -> {auto prfi : onlyNilOrNoNil rll risf = True} -> (LinT lDT' -> {lDT : LinDepT ll} -> LinT lDT) -> SFun nlFun -> SFun $ Com df nlFun {ll=ll}


-- simul : (c : Conti lFun _ ) -> {auto prf : isCInter c = True} -> SFun lFun -> (ull ** urll ** un ** nc : LFun ull urll un ** (Conti nc, SFun nc))
-- simul c x = ?simul_rhs

-- (prll ** prLDT : LinDepT prll ** ull ** urll ** un ** nk ** nc : LFun ull urll un  ** Conti prLDT nc nk) 

