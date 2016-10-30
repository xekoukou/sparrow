module Sparrow


import Syntax.PreorderReasoning
import Data.Vect
import Data.HVect

%access public export

%default total



-- One node should only be accessed by a single set of input nodes. A reuse of a sublFunaph, like in the case of a recursion needs to be done with function sublFunaphs.


-- Currying can happen asynchronously
-- The number of arguments/Types are not determined at the beginning.
-- The Types of the next arguments can also be determined by a computation that is not in the types.
-- Two operators:

-- If a or b in the type system.
-- a or b that is not in the type system.
-- IMPORTANT: a xor b that is determined by the lFunaph because of the two previous. In this case, a timeout should only be set for all of them,
-- not individually.
-- All inputs receive the timeout data type after a specific period of time. When an event timeouts, PROBABLY, we need to send expiry 
-- msgs to all the others that depend on us. Thus, they will not wait, but will immediately stop.


-- It should be locally deadlock free.


--Each edge depends on a number of previous nodes and sends to specific nodes.
-- There are also the Roles to which the data are sent.
-- It has a function that determines what it receives and tranmits.

--We need to split those three points. The first is the embedding of that function to another one.
--The second is the definiition itself.



------------------------------

--ChoreolFunaph
-- Audition Casting Actors

-- Each function has a set of nodes

genT : Vect n Type -> Type
genT [] = Type
genT (x :: xs) = x -> genT xs

applyH : {vt : Vect n Type} -> HVect vt -> genT vt -> Type
applyH [] y = y
applyH (x :: z) y = applyH z $ y x

data LinLogic: Type where
  Atom : {dt : Vect n Type} -> genT dt -> LinLogic 
  And  : LinLogic -> LinLogic -> LinLogic
  Uor  : LinLogic -> LinLogic -> LinLogic
  Xor  : LinLogic -> LinLogic -> LinLogic  -- d decides on that



data LLTr : LinLogic -> LinLogic -> Type where
  Id      : LLTr ll ll
  XorC    : LLTr (Xor b a) rll   -> LLTr (Xor a b) rll
  AndC    : LLTr (And b a) rll   -> LLTr (And a b) rll
  UorC    : LLTr (Uor b a) rll   -> LLTr (Uor a b) rll
  AndXorD : LLTr (Xor (And a1 c) (And a2 c)) rll -> LLTr (And (Xor a1 a2) c) rll
  AndUorD : LLTr (Uor (And a1 c) (And a2 c)) rll -> LLTr (And (Uor a1 a2) c) rll



data LinDepT : LinLogic -> Type where
    TAtom : {dt : Vect n Type} -> {df : genT dt} -> (hv : HVect dt) -> LinDepT $ Atom df {dt=dt}
    TAnd  : LinDepT a -> LinDepT b         -> LinDepT $ And a b
    TUor  : LinDepT a -> LinDepT b         -> LinDepT $ Uor a b
    TXor  : Either (LinDepT a) (LinDepT b) -> LinDepT $ Xor a b




trLDT : LinDepT ll -> LLTr ll rll -> LinDepT rll
trLDT x Id = x
trLDT (TXor (Left l)) (XorC y)  = trLDT (TXor $ Right l) y
trLDT (TXor (Right r)) (XorC y) = trLDT (TXor $ Left r) y
trLDT (TAnd x z) (AndC y)       = trLDT (TAnd z x) y
trLDT (TUor x z) (UorC y)       = trLDT (TUor z x) y
trLDT (TAnd (TXor (Left l)) x) (AndXorD y)   = trLDT (TXor $ Left $ TAnd l x) y
trLDT (TAnd (TXor (Right r)) x) (AndXorD y)  = trLDT (TXor $ Right $ TAnd r x) y
trLDT (TAnd (TUor x w) z) (AndUorD y)             = trLDT (TUor (TAnd x z) (TAnd w z)) y



data LinT : LinDepT a -> Type where
  IAtom      : {dt : Vect n Type} -> {df : genT dt} -> {hv : HVect dt} -> applyH hv df -> LinT $ TAtom hv {dt=dt} {df=df}
  IAnd       : LinT a -> LinT b         -> LinT $ TAnd a b
  IUor       : Either (LinT a) (LinT b) -> LinT $ TUor a b
  IXorLeft   : LinT a                      -> LinT $ TXor $ Left a
  IXorRight  : LinT b                      -> LinT $ TXor $ Right b



data IndexLL : LinLogic -> LinLogic -> Type where
  LHere     : IndexLL ll ll
  LLeftAnd  : IndexLL x rll -> IndexLL (And x y) rll
  LRightAnd : IndexLL y rll -> IndexLL (And x y) rll
  LLeftUor  : IndexLL x rll -> IndexLL (Uor x y) rll
  LRightUor : IndexLL y rll -> IndexLL (Uor x y) rll
  LLeftXor  : IndexLL x rll -> IndexLL (Xor x y) rll
  LRightXor : IndexLL y rll -> IndexLL (Xor x y) rll


truncLDT : LinDepT ll -> (i : IndexLL ll pll) -> Maybe $ LinDepT pll
truncLDT x LHere = Just x
truncLDT (TAnd x y) (LLeftAnd w)  = truncLDT x w
truncLDT (TAnd x y) (LRightAnd w) = truncLDT y w
truncLDT (TUor x y) (LLeftUor w)  = truncLDT x w
truncLDT (TUor x y) (LRightUor w) = truncLDT y w
truncLDT (TXor (Left l)) (LLeftXor w)   = truncLDT l w
truncLDT (TXor (Right r)) (LLeftXor w)  = Nothing
truncLDT (TXor (Left l)) (LRightXor w)  = Nothing
truncLDT (TXor (Right r)) (LRightXor w) = truncLDT r w



replLL : (ll : LinLogic) -> IndexLL ll _ -> LinLogic -> LinLogic
replLL ll LHere y = y
replLL (And x z) (LLeftAnd w) y  = And (replLL x w y) z
replLL (And x z) (LRightAnd w) y = And x (replLL z w y)
replLL (Uor x z) (LLeftUor w) y  = Uor (replLL x w y) z
replLL (Uor x z) (LRightUor w) y = Uor x (replLL z w y)
replLL (Xor x z) (LLeftXor w) y  = Xor (replLL x w y) z
replLL (Xor x z) (LRightXor w) y = Xor x (replLL z w y)


replLDT : LinDepT ll -> (i: IndexLL ll _) -> LinDepT $ nfl -> LinDepT $ replLL ll i nfl
replLDT x LHere nfT  = nfT
replLDT (TAnd x y) (LLeftAnd w) nfT   = TAnd (replLDT x w nfT) y
replLDT (TAnd x y) (LRightAnd w) nfT  = TAnd x $ replLDT y w nfT
replLDT (TUor x y) (LLeftUor w) nfT   = TUor (replLDT x w nfT) y
replLDT (TUor x y) (LRightUor w) nfT  = TUor x $ replLDT y w nfT
replLDT (TXor (Left l)) (LLeftXor w) nfT   = TXor (Left $ replLDT l w nfT)
replLDT (TXor (Right r)) (LLeftXor w) nfT  = TXor (Right r)
replLDT (TXor (Left l)) (LRightXor w) nfT  = TXor (Left l)
replLDT (TXor (Right r)) (LRightXor w) nfT =  TXor (Right $ replLDT r w nfT)



ifNotTruncLDT : (lDT : LinDepT ll) -> (i: IndexLL ll pll) -> (rll : LinLogic) -> Maybe $ LinDepT $ replLL ll i rll
ifNotTruncLDT x LHere  rll = Nothing
ifNotTruncLDT (TAnd x y) (LLeftAnd w) rll        = pure $ TAnd !(ifNotTruncLDT x w rll) y 
ifNotTruncLDT (TAnd x y) (LRightAnd w) rll       = pure $ TAnd x  !(ifNotTruncLDT y w rll) 
ifNotTruncLDT (TUor x y) (LLeftUor w) rll        = pure $ TUor !(ifNotTruncLDT x w rll) y 
ifNotTruncLDT (TUor x y) (LRightUor w) rll       = pure $ TUor x !(ifNotTruncLDT y w rll) 
ifNotTruncLDT (TXor (Left l)) (LLeftXor w) rll   = pure $ TXor (Left  !(ifNotTruncLDT l w rll)) 
ifNotTruncLDT (TXor (Right r)) (LLeftXor w) rll  = pure $ TXor (Right r) 
ifNotTruncLDT (TXor (Left l)) (LRightXor w) rll  = pure $ TXor (Left l) 
ifNotTruncLDT (TXor (Right r)) (LRightXor w) rll = pure $ TXor (Right !(ifNotTruncLDT r w rll)) 



data SetLL : LinLogic -> Type where
  SElem      : SetLL ll
  SLeftAnd   : SetLL x -> SetLL (And x y) 
  SRightAnd  : SetLL y -> SetLL (And x y) 
  SBothAnd   : SetLL x -> SetLL y -> SetLL (And x y) 
  SLeftUor   : SetLL x -> SetLL (Uor x y) 
  SRightUor  : SetLL y -> SetLL (Uor x y) 
  SBothUor   : SetLL x -> SetLL y -> SetLL (Uor x y) 
  SLeftXor   : SetLL x -> SetLL (Xor x y) 
  SRightXor  : SetLL y -> SetLL (Xor x y) 
  SBothXor   : SetLL x -> SetLL y -> SetLL (Xor x y) 


data MSetLL : LinLogic -> Type where
  SEmpty : MSetLL ll
  SSome : SetLL ll -> MSetLL ll

setLLAddEmpty : (i: IndexLL ll _) -> (rll : LinLogic) -> SetLL $ replLL ll i rll
setLLAddEmpty LHere rll = SElem
setLLAddEmpty (LLeftAnd z)  rll = SLeftAnd $ setLLAddEmpty z rll
setLLAddEmpty (LRightAnd z) rll = SRightAnd $ setLLAddEmpty z rll
setLLAddEmpty (LLeftUor z)  rll = SLeftUor $ setLLAddEmpty z rll
setLLAddEmpty (LRightUor z) rll = SRightUor $ setLLAddEmpty z rll
setLLAddEmpty (LLeftXor z)  rll = SLeftXor $ setLLAddEmpty z rll
setLLAddEmpty (LRightXor z) rll =  SRightXor $ setLLAddEmpty z rll

contructSetLL : SetLL ll -> SetLL ll
contructSetLL (SBothAnd SElem SElem)  = SElem
contructSetLL (SBothUor SElem SElem)  = SElem
contructSetLL (SBothXor  SElem SElem) = SElem
contructSetLL SElem = SElem
contructSetLL (SLeftAnd z) = (SLeftAnd (contructSetLL z))
contructSetLL (SRightAnd z) = (SRightAnd (contructSetLL z))
contructSetLL (SBothAnd z w) = let  cr = (SBothAnd (contructSetLL z) (contructSetLL w)) in
                                   case (cr) of
                                        (SBothAnd SElem SElem) => SElem
                                        _                      => cr
contructSetLL (SLeftUor z) = (SLeftUor (contructSetLL z))
contructSetLL (SRightUor z) = (SRightUor (contructSetLL z))
contructSetLL (SBothUor z w) = let  cr = (SBothUor (contructSetLL z) (contructSetLL w)) in
                                   case (cr) of
                                        (SBothUor SElem SElem) => SElem
                                        _                      => cr
contructSetLL (SLeftXor z) = (SLeftXor (contructSetLL z))
contructSetLL (SRightXor z) = (SRightXor (contructSetLL z))
contructSetLL (SBothXor z w) = let  cr = (SBothXor (contructSetLL z) (contructSetLL w)) in
                                   case (cr) of
                                        (SBothXor SElem SElem) => SElem
                                        _                      => cr


setLLAdd : SetLL ll -> (i : IndexLL ll _) -> (rll : LinLogic) -> SetLL $ replLL ll i rll
setLLAdd SElem y rll = SElem
setLLAdd x LHere rll = SElem
setLLAdd (SLeftAnd x) (LLeftAnd w)    rll = SLeftAnd $ setLLAdd x w rll
setLLAdd (SRightAnd x) (LLeftAnd w)   rll = SBothAnd (setLLAddEmpty w rll) x
setLLAdd (SBothAnd x y) (LLeftAnd w)  rll = SBothAnd (setLLAdd x w rll) y
setLLAdd (SRightAnd x) (LRightAnd w)  rll = SRightAnd $ setLLAdd x w rll
setLLAdd (SLeftAnd x) (LRightAnd w)   rll = SBothAnd x (setLLAddEmpty w rll)
setLLAdd (SBothAnd x y) (LRightAnd w) rll = SBothAnd x (setLLAdd y w rll)
setLLAdd (SLeftUor x) (LLeftUor w)    rll = SLeftUor $ setLLAdd x w rll
setLLAdd (SRightUor x) (LLeftUor w)   rll = SBothUor (setLLAddEmpty w rll) x
setLLAdd (SBothUor x y) (LLeftUor w)  rll = SBothUor (setLLAdd x w rll) y
setLLAdd (SRightUor x) (LRightUor w)  rll = SRightUor $ setLLAdd x w rll
setLLAdd (SLeftUor x) (LRightUor w)   rll = SBothUor x (setLLAddEmpty w rll)
setLLAdd (SBothUor x y) (LRightUor w) rll = SBothUor x (setLLAdd y w rll)
setLLAdd (SLeftXor x) (LLeftXor w)    rll = SLeftXor $ setLLAdd x w rll
setLLAdd (SRightXor x) (LLeftXor w)   rll = SBothXor (setLLAddEmpty w rll) x
setLLAdd (SBothXor x y) (LLeftXor w)  rll = SBothXor (setLLAdd x w rll) y
setLLAdd (SRightXor x) (LRightXor w)  rll = SRightXor $ setLLAdd x w rll
setLLAdd (SLeftXor x) (LRightXor w)   rll = SBothXor x (setLLAddEmpty w rll)
setLLAdd (SBothXor x y) (LRightXor w) rll = SBothXor x (setLLAdd y w rll)




trSetLL : SetLL ll -> (ltr : LLTr ll rll) -> SetLL $ replLL ll LHere rll
trSetLL SElem ltr = SElem
trSetLL x Id = x
trSetLL (SLeftXor x) (XorC y)   = trSetLL (SRightXor x) y
trSetLL (SRightXor x) (XorC y)  = trSetLL (SLeftXor x) y
trSetLL (SBothXor x z) (XorC y) = trSetLL (SBothXor z x) y
trSetLL (SLeftAnd x) (AndC y)   = trSetLL (SRightAnd x) y
trSetLL (SRightAnd x) (AndC y)  = trSetLL (SLeftAnd x) y
trSetLL (SBothAnd x z) (AndC y) = trSetLL (SBothAnd z x) y
trSetLL (SLeftUor x) (UorC y)   = trSetLL (SRightUor x) y
trSetLL (SRightUor x) (UorC y)  = trSetLL (SLeftUor x) y
trSetLL (SBothUor x z) (UorC y) = trSetLL (SBothUor z x) y
trSetLL (SLeftAnd SElem) (AndXorD y) = trSetLL (SBothXor (SLeftAnd SElem) (SLeftAnd SElem)) y
trSetLL (SLeftAnd (SLeftXor x)) (AndXorD y) = trSetLL (SLeftXor $ SLeftAnd x) y
trSetLL (SLeftAnd (SRightXor x)) (AndXorD y) = trSetLL (SRightXor $ SLeftAnd x) y
trSetLL (SLeftAnd (SBothXor x z)) (AndXorD y) = trSetLL (SBothXor (SLeftAnd x) (SLeftAnd z)) y
trSetLL (SRightAnd x) (AndXorD y) = trSetLL (SBothXor (SRightAnd x) (SRightAnd x)) y
trSetLL (SBothAnd SElem z) (AndXorD y) = trSetLL (SBothXor (SBothAnd SElem z) (SBothAnd SElem z)) y
trSetLL (SBothAnd (SLeftXor x) z) (AndXorD y) = trSetLL (SLeftXor $ SBothAnd x z) y
trSetLL (SBothAnd (SRightXor x) z) (AndXorD y) =  trSetLL (SRightXor $ SBothAnd x z) y
trSetLL (SBothAnd (SBothXor x w) z) (AndXorD y) = trSetLL (SBothXor (SBothAnd x z) (SBothAnd w z)) y
trSetLL (SLeftAnd SElem) (AndUorD y) = trSetLL (SBothUor (SLeftAnd SElem) (SLeftAnd SElem)) y
trSetLL (SLeftAnd (SLeftUor x)) (AndUorD y) = trSetLL (SLeftUor $ SLeftAnd x) y
trSetLL (SLeftAnd (SRightUor x)) (AndUorD y) = trSetLL (SRightUor $ SLeftAnd x) y
trSetLL (SLeftAnd (SBothUor x z)) (AndUorD y) = trSetLL (SBothUor (SLeftAnd x) (SLeftAnd z)) y
trSetLL (SRightAnd x) (AndUorD y) = trSetLL (SBothUor (SRightAnd x) (SRightAnd x)) y
trSetLL (SBothAnd SElem z) (AndUorD y) = trSetLL (SBothUor (SBothAnd SElem z) (SBothAnd SElem z)) y
trSetLL (SBothAnd (SLeftUor x) z) (AndUorD y) = trSetLL (SLeftUor $ SBothAnd x z) y
trSetLL (SBothAnd (SRightUor x) z) (AndUorD y) =  trSetLL (SRightUor $ SBothAnd x z) y
trSetLL (SBothAnd (SBothUor x w) z) (AndUorD y) = trSetLL (SBothUor (SBothAnd x z) (SBothAnd w z)) y


indTrSetLL : SetLL ll -> (i : IndexLL ll pll) -> (ltr : LLTr pll rll) -> SetLL $ replLL ll i rll
indTrSetLL SElem i ltr = SElem
indTrSetLL x LHere ltr = trSetLL x ltr
indTrSetLL (SLeftAnd x) (LLeftAnd w) ltr    = SLeftAnd $ indTrSetLL x w ltr
indTrSetLL (SRightAnd x) (LLeftAnd w) ltr   = SRightAnd x
indTrSetLL (SBothAnd x y) (LLeftAnd w) ltr  = SBothAnd (indTrSetLL x w ltr) y
indTrSetLL (SLeftAnd x) (LRightAnd w) ltr   = SLeftAnd x
indTrSetLL (SRightAnd x) (LRightAnd w) ltr  = SRightAnd $ indTrSetLL x w ltr
indTrSetLL (SBothAnd x y) (LRightAnd w) ltr = SBothAnd x (indTrSetLL y w ltr)
indTrSetLL (SLeftUor x) (LLeftUor w) ltr    = SLeftUor $ indTrSetLL x w ltr
indTrSetLL (SRightUor x) (LLeftUor w) ltr   = SRightUor x
indTrSetLL (SBothUor x y) (LLeftUor w) ltr  = SBothUor (indTrSetLL x w ltr) y
indTrSetLL (SLeftUor x) (LRightUor w) ltr   = SLeftUor x
indTrSetLL (SRightUor x) (LRightUor w) ltr  = SRightUor $ indTrSetLL x w ltr
indTrSetLL (SBothUor x y) (LRightUor w) ltr = SBothUor x (indTrSetLL y w ltr)
indTrSetLL (SLeftXor x) (LLeftXor w) ltr    = SLeftXor $ indTrSetLL x w ltr
indTrSetLL (SRightXor x) (LLeftXor w) ltr   = SRightXor x
indTrSetLL (SBothXor x y) (LLeftXor w) ltr  = SBothXor (indTrSetLL x w ltr) y
indTrSetLL (SLeftXor x) (LRightXor w) ltr   = SLeftXor x
indTrSetLL (SRightXor x) (LRightXor w) ltr  = SRightXor $ indTrSetLL x w ltr
indTrSetLL (SBothXor x y) (LRightXor w) ltr = SBothXor x (indTrSetLL y w ltr)



indTrLDT : LinDepT ll -> (i: IndexLL ll pll) -> (ltr : LLTr pll rll) -> LinDepT $ replLL ll i rll
indTrLDT x LHere ltr = trLDT x ltr
indTrLDT (TAnd x y) (LLeftAnd w) ltr = TAnd (indTrLDT x w ltr) y
indTrLDT (TAnd x y) (LRightAnd w) ltr = TAnd x $ indTrLDT y w ltr
indTrLDT (TUor x y) (LLeftUor w) ltr = TUor (indTrLDT x w ltr) y
indTrLDT (TUor x y) (LRightUor w) ltr = TUor x $ indTrLDT y w ltr
indTrLDT (TXor (Left l)) (LLeftXor w) ltr = TXor (Left $ indTrLDT l w ltr)
indTrLDT (TXor (Right r)) (LLeftXor w) ltr = TXor (Right r)
indTrLDT (TXor (Left l)) (LRightXor w) ltr = TXor (Left l)
indTrLDT (TXor (Right r)) (LRightXor w) ltr =  TXor (Right $ indTrLDT r w ltr)



mutual

  data LFun : (ll : LinLogic) -> (rll : LinLogic) -> Type where
    LFunId : LFun ll ll
    Emb : (i : IndexLL ll pll) -> (lFun : LFun pll ell) -> {auto prf : lFunUsesInput lFun = True} -> LFun (replLL ll i ell) rll -> LFun ll rll
    Trans : (i : IndexLL ll pll) -> (ltr : LLTr pll orll) -> LFun (replLL ll i orll) rll -> LFun ll rll
    Com : {rll : LinLogic} -> (df : ((lDT : LinDepT ll) -> LinT lDT -> LinDepT rll)) -> LFun rll nrfl -> LFun ll nrfl
  

  lFunUsesInput : LFun ll rll -> Bool
  lFunUsesInput x = lFunUsesInput' x SEmpty where
    lFunUsesInput' : LFun ll rll -> MSetLL ll -> Bool
    lFunUsesInput' LFunId s = False
    lFunUsesInput' (Emb i lFun x {ell}) SEmpty = lFunUsesInput' x $ SSome $ setLLAddEmpty i ell
    lFunUsesInput' (Emb i lFun x {ell}) (SSome s) = let ns = contructSetLL $ setLLAdd s i ell in case (ns) of
                                                                            SElem => True
                                                                            _     => lFunUsesInput' x $ SSome ns
    lFunUsesInput' (Trans i ltr y) SEmpty = lFunUsesInput' y $ SEmpty
    lFunUsesInput' (Trans i ltr y) (SSome s) = lFunUsesInput' y $ SSome $ indTrSetLL s i ltr
    lFunUsesInput' (Com df x) s   = True




data EList : IndexLL ofl pll -> LFun pll _ -> LFun all _ -> Nat -> Type where
  ENil : EList (LHere {ll=ll}) (LFunId {ll=ll}) (LFunId {ll=ll}) Z
  EL : (ni : IndexLL ll pll) -> (nflFun : LFun pll ell) -> (nlFun : LFun (replLL ll ni ell) rll) 
  -> {flFun : LFun _ rll} -> EList i flFun lFun k -> EList ni nflFun nlFun (S k)

data EVect : EList ni nflFun nlFun n -> Type where
  EVNill : EVect ENil
  EV : (ni : IndexLL ll pll) -> {nflFun : LFun pll ell} -> (nlFun : LFun (replLL ll ni ell) rll) -> {flFun : LFun _ rll} 
  -> {prEL : EList i flFun lFun k} -> (prL : LinDepT ll) ->  EVect prEL -> EVect $ EL ni nflFun nlFun prEL





genDFT' : (lFun : LFun ll rll) -> {flFun : LFun pll rll} -> (el : EList ei flFun elFun n) -> (EVect el -> LinDepT ll -> Type)
genDFT' LFunId ENil {ll} = (\vhv, x => LinDepT ll)
genDFT' LFunId (EL ei nflFun elFun pEL) = (\ev, x =>  let EV _ _ prL prEV = ev in
                                                    (genDFT' elFun pEL) prEV (replLDT prL ei x))
genDFT' (Emb ni nflFun nlFun {ell}) y = (\ ev, x => let tr = truncLDT x ni in
                                                case (tr) of
                                                 Just tx => genDFT' nflFun (EL ni nflFun nlFun y) (EV ni nlFun x ev) tx
                                                 Nothing => let ntr = ifNotTruncLDT x ni ell in
                                                            case (ntr) of
                                                              Just ntx => (genDFT' nlFun y) ev ntx
                                                              _ => assert_unreachable
                                                                                       )
genDFT' (Trans i ltr z) y = (\ev, x => (genDFT' z y) ev $ indTrLDT x i ltr )
genDFT' (Com df nlFun) y = (\ev, x => (fi : LinT x) -> (genDFT' nlFun y) ev $ df x fi)


genDFT : (lFun : LFun ll rll) -> {auto prf : lFunUsesInput lFun = True} -> ((EVect (ENil {ll=rll})) -> LinDepT ll -> Type)
genDFT lFun = genDFT' lFun ENil {n=Z}


genDF : (lFun : LFun ll rll) -> {auto prf : lFunUsesInput lFun = True} -> ((lDT : LinDepT ll) -> genDFT lFun EVNill lDT)
genDF lFun lDT = genDF' lFun EVNill lDT where
  genDF' : (lFun : LFun ll rll) -> (ev : EVect el) -> ((lDT : LinDepT ll) -> genDFT' lFun el ev lDT)
  genDF' LFunId EVNill lDT = lDT
  genDF' LFunId (EV ei elFun prL y) lDT = (genDF' elFun y) (replLDT prL ei lDT)
  genDF' (Emb ni nflFun nlFun {ell} ) ev lDT with (truncLDT lDT ni)
    | Just tx = (genDF' nflFun (EV ni nlFun lDT ev {nflFun=nflFun})) tx
    | Nothing with (ifNotTruncLDT lDT ni ell) 
      | Just ntx = (genDF' nlFun ev) ntx
      | Nothing = assert_unreachable
  genDF' (Trans i ltr x) ev lDT = genDF' x ev $ indTrLDT lDT i ltr
  genDF' (Com df nlFun) ev lDT = (\fi => genDF' nlFun ev $ df lDT fi)



-- A lFun is Full if all the data it receives is processed at least once.

--TODO ADD Agents, dependencies to previous inputs, total funT of a LFun operator.





