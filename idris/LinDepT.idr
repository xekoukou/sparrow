module LinDepT


import public LinLogic

%access public export

%default total

||| This type is computed by the protocol specification and all in/out-puts'
||| types depend on it.
data LinDepT : LinLogic -> Type where
  ||| Do not send anything.
  TNil  : LinDepT Nil
  |||
  ||| @ hv is used to compute the type of this specific input/output.
  TAtom : {dt : Vect n Type} -> {df : genT dt} -> (hv : HVect dt) -> LinDepT $ Atom df {dt=dt}
  TAnd  : LinDepT a -> LinDepT b         -> LinDepT $ And a b
  TUor  : LinDepT a -> LinDepT b         -> LinDepT $ Uor a b
  ||| Dor takes a specific value. Only one of the two possible.
  TDor  : Either (LinDepT a) (LinDepT b) -> LinDepT $ Dor a b



||| Given a linear transformation and a LinDepT, 
||| this function computes the LinDepT of the transformed
||| linear logic.
trLDT : LinDepT ll -> LLTr ll rll -> LinDepT rll
trLDT x Id = x
trLDT (TDor (Left l)) (DorC y)  = trLDT (TDor $ Right l) y
trLDT (TDor (Right r)) (DorC y) = trLDT (TDor $ Left r) y
trLDT (TAnd x z) (AndC y)       = trLDT (TAnd z x) y
trLDT (TUor x z) (UorC y)       = trLDT (TUor z x) y
trLDT (TAnd (TDor (Left l)) x) (AndDorD y)   = trLDT (TDor $ Left $ TAnd l x) y
trLDT (TAnd (TDor (Right r)) x) (AndDorD y)  = trLDT (TDor $ Right $ TAnd r x) y
trLDT (TAnd (TUor x w) z) (AndUorD y)             = trLDT (TUor (TAnd x z) (TAnd w z)) y


||| Trancuates the LinDepT, leaving only the node that is
||| pointed by the index.
|||
||| If the index points to path that the LinDept does not contain, 
||| it returns Nothing.
truncLDT : LinDepT ll -> (i : IndexLL ll pll) -> Maybe $ LinDepT pll
truncLDT x LHere = Just x
truncLDT (TAnd x y) (LLeftAnd w)  = truncLDT x w
truncLDT (TAnd x y) (LRightAnd w) = truncLDT y w
truncLDT (TUor x y) (LLeftUor w)  = truncLDT x w
truncLDT (TUor x y) (LRightUor w) = truncLDT y w
truncLDT (TDor (Left l)) (LLeftDor w)   = truncLDT l w
truncLDT (TDor (Right r)) (LLeftDor w)  = Nothing
truncLDT (TDor (Left l)) (LRightDor w)  = Nothing
truncLDT (TDor (Right r)) (LRightDor w) = truncLDT r w



||| Replaces a node of a LinDepT with another one.
replLDT : LinDepT ll -> (i: IndexLL ll _) -> LinDepT $ nfl -> LinDepT $ replLL ll i nfl
replLDT x LHere nfT  = nfT
replLDT (TAnd x y) (LLeftAnd w) nfT   = TAnd (replLDT x w nfT) y
replLDT (TAnd x y) (LRightAnd w) nfT  = TAnd x $ replLDT y w nfT
replLDT (TUor x y) (LLeftUor w) nfT   = TUor (replLDT x w nfT) y
replLDT (TUor x y) (LRightUor w) nfT  = TUor x $ replLDT y w nfT
replLDT (TDor (Left l)) (LLeftDor w) nfT   = TDor (Left $ replLDT l w nfT)
replLDT (TDor (Right r)) (LLeftDor w) nfT  = TDor (Right r)
replLDT (TDor (Left l)) (LRightDor w) nfT  = TDor (Left l)
replLDT (TDor (Right r)) (LRightDor w) nfT =  TDor (Right $ replLDT r w nfT)


||| If the index points to a path that is not part of LinDepT, then the same LinDepT can 
||| be the computation of a different linear logic tree in which we replace the logic node
||| that it does not contain.
ifNotTruncLDT : (lDT : LinDepT ll) -> (i: IndexLL ll pll) -> (rll : LinLogic) -> Maybe $ LinDepT $ replLL ll i rll
ifNotTruncLDT x LHere  rll = Nothing
ifNotTruncLDT (TAnd x y) (LLeftAnd w) rll        = pure $ TAnd !(ifNotTruncLDT x w rll) y 
ifNotTruncLDT (TAnd x y) (LRightAnd w) rll       = pure $ TAnd x  !(ifNotTruncLDT y w rll) 
ifNotTruncLDT (TUor x y) (LLeftUor w) rll        = pure $ TUor !(ifNotTruncLDT x w rll) y 
ifNotTruncLDT (TUor x y) (LRightUor w) rll       = pure $ TUor x !(ifNotTruncLDT y w rll) 
ifNotTruncLDT (TDor (Left l)) (LLeftDor w) rll   = pure $ TDor (Left  !(ifNotTruncLDT l w rll)) 
ifNotTruncLDT (TDor (Right r)) (LLeftDor w) rll  = pure $ TDor (Right r) 
ifNotTruncLDT (TDor (Left l)) (LRightDor w) rll  = pure $ TDor (Left l) 
ifNotTruncLDT (TDor (Right r)) (LRightDor w) rll = pure $ TDor (Right !(ifNotTruncLDT r w rll)) 




||| Transform a LinDepT after a specific node pointed by the index i.
indTrLDT : LinDepT ll -> (i: IndexLL ll pll) -> (ltr : LLTr pll rll) -> LinDepT $ replLL ll i rll
indTrLDT x LHere ltr = trLDT x ltr
indTrLDT (TAnd x y) (LLeftAnd w) ltr = TAnd (indTrLDT x w ltr) y
indTrLDT (TAnd x y) (LRightAnd w) ltr = TAnd x $ indTrLDT y w ltr
indTrLDT (TUor x y) (LLeftUor w) ltr = TUor (indTrLDT x w ltr) y
indTrLDT (TUor x y) (LRightUor w) ltr = TUor x $ indTrLDT y w ltr
indTrLDT (TDor (Left l)) (LLeftDor w) ltr = TDor (Left $ indTrLDT l w ltr)
indTrLDT (TDor (Right r)) (LLeftDor w) ltr = TDor (Right r)
indTrLDT (TDor (Left l)) (LRightDor w) ltr = TDor (Left l)
indTrLDT (TDor (Right r)) (LRightDor w) ltr =  TDor (Right $ indTrLDT r w ltr)

