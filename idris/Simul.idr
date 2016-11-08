module Simul


import Sparrow


%access public export

%default total




data SFun : LFun ll rll _ -> Type where
  SFunId : SFun $ LFunId
  SEmb : SFun elFun -> {auto prf : lFunUsesInput elFun = True} -> SFun nlFun -> SFun $ Emb i elFun nlFun {prf = prf}
  STrans : SFun nlFun -> SFun $ Trans i ltr nlFun
  SCom : (LinT lDT' -> {lDT : LinDepT ll} -> LinT lDT) -> SFun nlFun -> SFun $ Com df nlFun {ll=ll}


simul : (c : Conti lFun _ ) -> {auto prf : isCInter c = True} -> SFun lFun -> (ull ** urll ** un ** nc : LFun ull urll un ** (Conti nc, SFun nc))
simul c x = ?simul_rhs


