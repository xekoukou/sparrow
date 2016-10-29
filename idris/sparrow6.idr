module Sparrow


import Syntax.PreorderReasoning
import Data.Vect
import Data.HVect


%default total

--certain nat to fin
cnatToFin : (k: Nat) -> (n : Nat) -> {auto prf : LTE (S k) n} -> Fin n
cnatToFin Z Z {prf=prf} = void $ succNotLTEzero prf
cnatToFin Z (S k) = FZ
cnatToFin (S k) Z {prf=prf} = void $ succNotLTEzero prf
cnatToFin (S k) (S j) {prf=LTESucc prf} = FS $ cnatToFin k j


data Role : Type where
  MkRole : (s : String) -> Role



-- One node should only be accessed by a single set of input nodes. A reuse of a subgraph, like in the case of a recursion needs to be done with function subgraphs.


-- Currying can happen asynchronously
-- The number of arguments/Types are not determined at the beginning.
-- The Types of the next arguments can also be determined by a computation that is not in the types.
-- Two operators:

-- If a or b in the type system.
-- a or b that is not in the type system.
-- IMPORTANT: a xor b that is determined by the graph because of the two previous. In this case, a timeout should only be set for all of them,
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

--Choreograph
-- Audition Casting Actors

-- Each function has a set of nodes

genT : Vect n Type -> Type
genT [] = Type
genT (x :: xs) = x -> genT xs

applyH : {vt : Vect n Type} -> HVect vt -> genT vt -> Type
applyH [] y = y
applyH (x :: z) y = applyH z $ y x

data FunLang: Type where
  Atom : {dt : Vect n Type} -> genT dt -> FunLang 
  And  : FunLang -> FunLang -> FunLang
  Uor  : FunLang -> FunLang -> FunLang
  Xor  : FunLang -> FunLang -> FunLang  -- d decides on that



data FunLangOp : FunLang -> FunLang -> Type where
  Id      : FunLangOp fl fl
  XorC    : FunLangOp (Xor b a) rfl   -> FunLangOp (Xor a b) rfl
  AndC    : FunLangOp (And b a) rfl   -> FunLangOp (And a b) rfl
  UorC    : FunLangOp (Uor b a) rfl   -> FunLangOp (Uor a b) rfl
  AndXorD : FunLangOp (Xor (And a1 c) (And a2 c)) rfl -> FunLangOp (And (Xor a1 a2) c) rfl
  AndUorD : FunLangOp (Uor (And a1 c) (And a2 c)) rfl -> FunLangOp (And (Uor a1 a2) c) rfl


trFL : (fl : FunLang) -> FunLangOp fl rfl -> FunLang
trFL fl x {rfl} = rfl


data FunT : FunLang -> Type where
    TAtom : {dt : Vect n Type} -> {df : genT dt} -> (hv : HVect dt) -> FunT $ Atom df {dt=dt}
    TAnd  : FunT a -> FunT b         -> FunT $ And a b
    TUor  : FunT a -> FunT b         -> FunT $ Uor a b
    TXor  : Either (FunT a) (FunT b) -> FunT $ Xor a b




trFT : FunT fl -> FunLangOp fl rfl -> FunT rfl
trFT x Id = x
trFT (TXor (Left l)) (XorC y)  = trFT (TXor $ Right l) y
trFT (TXor (Right r)) (XorC y) = trFT (TXor $ Left r) y
trFT (TAnd x z) (AndC y)       = trFT (TAnd z x) y
trFT (TUor x z) (UorC y)       = trFT (TUor z x) y
trFT (TAnd (TXor (Left l)) x) (AndXorD y)   = trFT (TXor $ Left $ TAnd l x) y
trFT (TAnd (TXor (Right r)) x) (AndXorD y)  = trFT (TXor $ Right $ TAnd r x) y
trFT (TAnd (TUor x w) z) (AndUorD y)             = trFT (TUor (TAnd x z) (TAnd w z)) y



data FunInst : FunT a -> Type where
  IAtom      : {dt : Vect n Type} -> {df : genT dt} -> {hv : HVect dt} -> applyH hv df -> FunInst $ TAtom hv {dt=dt} {df=df}
  IAnd       : FunInst a -> FunInst b         -> FunInst $ TAnd a b
  IUor       : Either (FunInst a) (FunInst b) -> FunInst $ TUor a b
  IXorLeft   : FunInst a                      -> FunInst $ TXor $ Left a
  IXorRight  : FunInst b                      -> FunInst $ TXor $ Right b



trFI : {fl : FunLang} -> {fnT : FunT fl} -> FunInst fnT -> (g : FunLangOp fl rfl) -> FunInst $ trFT fnT g
trFI x Id = x
trFI (IXorLeft x) (XorC y) = trFI (IXorRight x) y
trFI (IXorRight x) (XorC y) = trFI (IXorLeft x) y
trFI (IAnd x z) (AndC y) = trFI (IAnd z x) y
trFI (IUor (Left l)) (UorC y) = trFI (IUor (Right l)) y
trFI (IUor (Right r)) (UorC y) = trFI (IUor (Left r)) y
trFI (IAnd (IXorLeft x) z) (AndXorD y)   = trFI (IXorLeft $ IAnd x z) y
trFI (IAnd (IXorRight x) z) (AndXorD y)  = trFI (IXorRight $ IAnd x z) y
trFI (IAnd (IUor (Left l)) x) (AndUorD y)   = trFI (IUor $ Left $ IAnd l x) y
trFI (IAnd (IUor (Right r)) x) (AndUorD y)  =  trFI (IUor $ Right $ IAnd r x) y


data IndexFL : FunLang -> FunLang -> Type where
  LHere     : IndexFL fl fl
  LLeftAnd  : IndexFL x rfl -> IndexFL (And x y) rfl
  LRightAnd : IndexFL y rfl -> IndexFL (And x y) rfl
  LLeftUor  : IndexFL x rfl -> IndexFL (Uor x y) rfl
  LRightUor : IndexFL y rfl -> IndexFL (Uor x y) rfl
  LLeftXor  : IndexFL x rfl -> IndexFL (Xor x y) rfl
  LRightXor : IndexFL y rfl -> IndexFL (Xor x y) rfl


truncFT : FunT fl -> (i : IndexFL fl pfl) -> Maybe $ FunT pfl
truncFT x LHere = Just x
truncFT (TAnd x y) (LLeftAnd w)  = truncFT x w
truncFT (TAnd x y) (LRightAnd w) = truncFT y w
truncFT (TUor x y) (LLeftUor w)  = truncFT x w
truncFT (TUor x y) (LRightUor w) = truncFT y w
truncFT (TXor (Left l)) (LLeftXor w)   = truncFT l w
truncFT (TXor (Right r)) (LLeftXor w)  = Nothing
truncFT (TXor (Left l)) (LRightXor w)  = Nothing
truncFT (TXor (Right r)) (LRightXor w) = truncFT r w



replFL : (fl : FunLang) -> IndexFL fl _ -> FunLang -> FunLang
replFL fl LHere y = y
replFL (And x z) (LLeftAnd w) y  = And (replFL x w y) z
replFL (And x z) (LRightAnd w) y = And x (replFL z w y)
replFL (Uor x z) (LLeftUor w) y  = Uor (replFL x w y) z
replFL (Uor x z) (LRightUor w) y = Uor x (replFL z w y)
replFL (Xor x z) (LLeftXor w) y  = Xor (replFL x w y) z
replFL (Xor x z) (LRightXor w) y = Xor x (replFL z w y)


replFT : FunT fl -> (i: IndexFL fl _) -> FunT $ nfl -> FunT $ replFL fl i nfl
replFT x LHere nfT  = nfT
replFT (TAnd x y) (LLeftAnd w) nfT   = TAnd (replFT x w nfT) y
replFT (TAnd x y) (LRightAnd w) nfT  = TAnd x $ replFT y w nfT
replFT (TUor x y) (LLeftUor w) nfT   = TUor (replFT x w nfT) y
replFT (TUor x y) (LRightUor w) nfT  = TUor x $ replFT y w nfT
replFT (TXor (Left l)) (LLeftXor w) nfT   = TXor (Left $ replFT l w nfT)
replFT (TXor (Right r)) (LLeftXor w) nfT  = TXor (Right r)
replFT (TXor (Left l)) (LRightXor w) nfT  = TXor (Left l)
replFT (TXor (Right r)) (LRightXor w) nfT =  TXor (Right $ replFT r w nfT)

isTruncFTNothing : (fnT : FunT fl) -> (i: IndexFL fl pfl) -> Bool
isTruncFTNothing fnT i = let tr = truncFT fnT i in
                                               case (tr) of
                                                     Just tx => False
                                                     Nothing => True

ifNotTruncFT : (fnT : FunT fl) -> (i: IndexFL fl pfl) -> (rfl : FunLang) -> Maybe $ FunT $ replFL fl i rfl
ifNotTruncFT x LHere  rfl = Nothing
ifNotTruncFT (TAnd x y) (LLeftAnd w) rfl        = pure $ TAnd !(ifNotTruncFT x w rfl) y 
ifNotTruncFT (TAnd x y) (LRightAnd w) rfl       = pure $ TAnd x  !(ifNotTruncFT y w rfl) 
ifNotTruncFT (TUor x y) (LLeftUor w) rfl        = pure $ TUor !(ifNotTruncFT x w rfl) y 
ifNotTruncFT (TUor x y) (LRightUor w) rfl       = pure $ TUor x !(ifNotTruncFT y w rfl) 
ifNotTruncFT (TXor (Left l)) (LLeftXor w) rfl   = pure $ TXor (Left  !(ifNotTruncFT l w rfl)) 
ifNotTruncFT (TXor (Right r)) (LLeftXor w) rfl  = pure $ TXor (Right r) 
ifNotTruncFT (TXor (Left l)) (LRightXor w) rfl  = pure $ TXor (Left l) 
ifNotTruncFT (TXor (Right r)) (LRightXor w) rfl = pure $ TXor (Right !(ifNotTruncFT r w rfl)) 



data SetFL : FunLang -> Type where
  SElem      : SetFL fl
  SLeftAnd   : SetFL x -> SetFL (And x y) 
  SRightAnd  : SetFL y -> SetFL (And x y) 
  SBothAnd   : SetFL x -> SetFL y -> SetFL (And x y) 
  SLeftUor   : SetFL x -> SetFL (Uor x y) 
  SRightUor  : SetFL y -> SetFL (Uor x y) 
  SBothUor   : SetFL x -> SetFL y -> SetFL (Uor x y) 
  SLeftXor   : SetFL x -> SetFL (Xor x y) 
  SRightXor  : SetFL y -> SetFL (Xor x y) 
  SBothXor   : SetFL x -> SetFL y -> SetFL (Xor x y) 


data MSetFL : FunLang -> Type where
  SEmpty : MSetFL fl
  SSome : SetFL fl -> MSetFL fl

setFLAddEmpty : (i: IndexFL fl _) -> (rfl : FunLang) -> SetFL $ replFL fl i rfl
setFLAddEmpty LHere rfl = SElem
setFLAddEmpty (LLeftAnd z)  rfl = SLeftAnd $ setFLAddEmpty z rfl
setFLAddEmpty (LRightAnd z) rfl = SRightAnd $ setFLAddEmpty z rfl
setFLAddEmpty (LLeftUor z)  rfl = SLeftUor $ setFLAddEmpty z rfl
setFLAddEmpty (LRightUor z) rfl = SRightUor $ setFLAddEmpty z rfl
setFLAddEmpty (LLeftXor z)  rfl = SLeftXor $ setFLAddEmpty z rfl
setFLAddEmpty (LRightXor z) rfl =  SRightXor $ setFLAddEmpty z rfl

contructSetFL : SetFL fl -> SetFL fl
contructSetFL (SBothAnd SElem SElem)  = SElem
contructSetFL (SBothUor SElem SElem)  = SElem
contructSetFL (SBothXor  SElem SElem) = SElem
contructSetFL SElem = SElem
contructSetFL (SLeftAnd z) = (SLeftAnd (contructSetFL z))
contructSetFL (SRightAnd z) = (SRightAnd (contructSetFL z))
contructSetFL (SBothAnd z w) = let  cr = (SBothAnd (contructSetFL z) (contructSetFL w)) in
                                   case (cr) of
                                        (SBothAnd SElem SElem) => SElem
                                        _                      => cr
contructSetFL (SLeftUor z) = (SLeftUor (contructSetFL z))
contructSetFL (SRightUor z) = (SRightUor (contructSetFL z))
contructSetFL (SBothUor z w) = let  cr = (SBothUor (contructSetFL z) (contructSetFL w)) in
                                   case (cr) of
                                        (SBothUor SElem SElem) => SElem
                                        _                      => cr
contructSetFL (SLeftXor z) = (SLeftXor (contructSetFL z))
contructSetFL (SRightXor z) = (SRightXor (contructSetFL z))
contructSetFL (SBothXor z w) = let  cr = (SBothXor (contructSetFL z) (contructSetFL w)) in
                                   case (cr) of
                                        (SBothXor SElem SElem) => SElem
                                        _                      => cr


setFLAdd : SetFL fl -> (i : IndexFL fl _) -> (rfl : FunLang) -> SetFL $ replFL fl i rfl
setFLAdd SElem y rfl = SElem
setFLAdd x LHere rfl = SElem
setFLAdd (SLeftAnd x) (LLeftAnd w)    rfl = SLeftAnd $ setFLAdd x w rfl
setFLAdd (SRightAnd x) (LLeftAnd w)   rfl = SBothAnd (setFLAddEmpty w rfl) x
setFLAdd (SBothAnd x y) (LLeftAnd w)  rfl = SBothAnd (setFLAdd x w rfl) y
setFLAdd (SRightAnd x) (LRightAnd w)  rfl = SRightAnd $ setFLAdd x w rfl
setFLAdd (SLeftAnd x) (LRightAnd w)   rfl = SBothAnd x (setFLAddEmpty w rfl)
setFLAdd (SBothAnd x y) (LRightAnd w) rfl = SBothAnd x (setFLAdd y w rfl)
setFLAdd (SLeftUor x) (LLeftUor w)    rfl = SLeftUor $ setFLAdd x w rfl
setFLAdd (SRightUor x) (LLeftUor w)   rfl = SBothUor (setFLAddEmpty w rfl) x
setFLAdd (SBothUor x y) (LLeftUor w)  rfl = SBothUor (setFLAdd x w rfl) y
setFLAdd (SRightUor x) (LRightUor w)  rfl = SRightUor $ setFLAdd x w rfl
setFLAdd (SLeftUor x) (LRightUor w)   rfl = SBothUor x (setFLAddEmpty w rfl)
setFLAdd (SBothUor x y) (LRightUor w) rfl = SBothUor x (setFLAdd y w rfl)
setFLAdd (SLeftXor x) (LLeftXor w)    rfl = SLeftXor $ setFLAdd x w rfl
setFLAdd (SRightXor x) (LLeftXor w)   rfl = SBothXor (setFLAddEmpty w rfl) x
setFLAdd (SBothXor x y) (LLeftXor w)  rfl = SBothXor (setFLAdd x w rfl) y
setFLAdd (SRightXor x) (LRightXor w)  rfl = SRightXor $ setFLAdd x w rfl
setFLAdd (SLeftXor x) (LRightXor w)   rfl = SBothXor x (setFLAddEmpty w rfl)
setFLAdd (SBothXor x y) (LRightXor w) rfl = SBothXor x (setFLAdd y w rfl)




trSetFL : SetFL fl -> (op : FunLangOp fl rfl) -> SetFL $ replFL fl LHere rfl
trSetFL SElem op = SElem
trSetFL x Id = x
trSetFL (SLeftXor x) (XorC y)   = trSetFL (SRightXor x) y
trSetFL (SRightXor x) (XorC y)  = trSetFL (SLeftXor x) y
trSetFL (SBothXor x z) (XorC y) = trSetFL (SBothXor z x) y
trSetFL (SLeftAnd x) (AndC y)   = trSetFL (SRightAnd x) y
trSetFL (SRightAnd x) (AndC y)  = trSetFL (SLeftAnd x) y
trSetFL (SBothAnd x z) (AndC y) = trSetFL (SBothAnd z x) y
trSetFL (SLeftUor x) (UorC y)   = trSetFL (SRightUor x) y
trSetFL (SRightUor x) (UorC y)  = trSetFL (SLeftUor x) y
trSetFL (SBothUor x z) (UorC y) = trSetFL (SBothUor z x) y
trSetFL (SLeftAnd SElem) (AndXorD y) = trSetFL (SBothXor (SLeftAnd SElem) (SLeftAnd SElem)) y
trSetFL (SLeftAnd (SLeftXor x)) (AndXorD y) = trSetFL (SLeftXor $ SLeftAnd x) y
trSetFL (SLeftAnd (SRightXor x)) (AndXorD y) = trSetFL (SRightXor $ SLeftAnd x) y
trSetFL (SLeftAnd (SBothXor x z)) (AndXorD y) = trSetFL (SBothXor (SLeftAnd x) (SLeftAnd z)) y
trSetFL (SRightAnd x) (AndXorD y) = trSetFL (SBothXor (SRightAnd x) (SRightAnd x)) y
trSetFL (SBothAnd SElem z) (AndXorD y) = trSetFL (SBothXor (SBothAnd SElem z) (SBothAnd SElem z)) y
trSetFL (SBothAnd (SLeftXor x) z) (AndXorD y) = trSetFL (SLeftXor $ SBothAnd x z) y
trSetFL (SBothAnd (SRightXor x) z) (AndXorD y) =  trSetFL (SRightXor $ SBothAnd x z) y
trSetFL (SBothAnd (SBothXor x w) z) (AndXorD y) = trSetFL (SBothXor (SBothAnd x z) (SBothAnd w z)) y
trSetFL (SLeftAnd SElem) (AndUorD y) = trSetFL (SBothUor (SLeftAnd SElem) (SLeftAnd SElem)) y
trSetFL (SLeftAnd (SLeftUor x)) (AndUorD y) = trSetFL (SLeftUor $ SLeftAnd x) y
trSetFL (SLeftAnd (SRightUor x)) (AndUorD y) = trSetFL (SRightUor $ SLeftAnd x) y
trSetFL (SLeftAnd (SBothUor x z)) (AndUorD y) = trSetFL (SBothUor (SLeftAnd x) (SLeftAnd z)) y
trSetFL (SRightAnd x) (AndUorD y) = trSetFL (SBothUor (SRightAnd x) (SRightAnd x)) y
trSetFL (SBothAnd SElem z) (AndUorD y) = trSetFL (SBothUor (SBothAnd SElem z) (SBothAnd SElem z)) y
trSetFL (SBothAnd (SLeftUor x) z) (AndUorD y) = trSetFL (SLeftUor $ SBothAnd x z) y
trSetFL (SBothAnd (SRightUor x) z) (AndUorD y) =  trSetFL (SRightUor $ SBothAnd x z) y
trSetFL (SBothAnd (SBothUor x w) z) (AndUorD y) = trSetFL (SBothUor (SBothAnd x z) (SBothAnd w z)) y


indTrSetFL : SetFL fl -> (i : IndexFL fl pfl) -> (op : FunLangOp pfl rfl) -> SetFL $ replFL fl i rfl
indTrSetFL SElem i op = SElem
indTrSetFL x LHere op = trSetFL x op
indTrSetFL (SLeftAnd x) (LLeftAnd w) op    = SLeftAnd $ indTrSetFL x w op
indTrSetFL (SRightAnd x) (LLeftAnd w) op   = SRightAnd x
indTrSetFL (SBothAnd x y) (LLeftAnd w) op  = SBothAnd (indTrSetFL x w op) y
indTrSetFL (SLeftAnd x) (LRightAnd w) op   = SLeftAnd x
indTrSetFL (SRightAnd x) (LRightAnd w) op  = SRightAnd $ indTrSetFL x w op
indTrSetFL (SBothAnd x y) (LRightAnd w) op = SBothAnd x (indTrSetFL y w op)
indTrSetFL (SLeftUor x) (LLeftUor w) op    = SLeftUor $ indTrSetFL x w op
indTrSetFL (SRightUor x) (LLeftUor w) op   = SRightUor x
indTrSetFL (SBothUor x y) (LLeftUor w) op  = SBothUor (indTrSetFL x w op) y
indTrSetFL (SLeftUor x) (LRightUor w) op   = SLeftUor x
indTrSetFL (SRightUor x) (LRightUor w) op  = SRightUor $ indTrSetFL x w op
indTrSetFL (SBothUor x y) (LRightUor w) op = SBothUor x (indTrSetFL y w op)
indTrSetFL (SLeftXor x) (LLeftXor w) op    = SLeftXor $ indTrSetFL x w op
indTrSetFL (SRightXor x) (LLeftXor w) op   = SRightXor x
indTrSetFL (SBothXor x y) (LLeftXor w) op  = SBothXor (indTrSetFL x w op) y
indTrSetFL (SLeftXor x) (LRightXor w) op   = SLeftXor x
indTrSetFL (SRightXor x) (LRightXor w) op  = SRightXor $ indTrSetFL x w op
indTrSetFL (SBothXor x y) (LRightXor w) op = SBothXor x (indTrSetFL y w op)



indTrFT : FunT fl -> (i: IndexFL fl pfl) -> (op : FunLangOp pfl rfl) -> FunT $ replFL fl i rfl
indTrFT x LHere op = trFT x op
indTrFT (TAnd x y) (LLeftAnd w) op = TAnd (indTrFT x w op) y
indTrFT (TAnd x y) (LRightAnd w) op = TAnd x $ indTrFT y w op
indTrFT (TUor x y) (LLeftUor w) op = TUor (indTrFT x w op) y
indTrFT (TUor x y) (LRightUor w) op = TUor x $ indTrFT y w op
indTrFT (TXor (Left l)) (LLeftXor w) op = TXor (Left $ indTrFT l w op)
indTrFT (TXor (Right r)) (LLeftXor w) op = TXor (Right r)
indTrFT (TXor (Left l)) (LRightXor w) op = TXor (Left l)
indTrFT (TXor (Right r)) (LRightXor w) op =  TXor (Right $ indTrFT r w op)




indReplInd : (i: IndexFL fl pfl) -> (nfl : FunLang) ->  IndexFL (replFL fl i nfl) nfl
indReplInd LHere nfl = LHere
indReplInd (LLeftAnd z) nfl  = LLeftAnd $ indReplInd z nfl
indReplInd (LRightAnd z) nfl = LRightAnd $ indReplInd z nfl
indReplInd (LLeftUor z)  nfl = LLeftUor $ indReplInd z nfl
indReplInd (LRightUor z) nfl = LRightUor $ indReplInd z nfl
indReplInd (LLeftXor z)  nfl = LLeftXor $ indReplInd z nfl
indReplInd (LRightXor z) nfl = LRightXor $ indReplInd z nfl



mutual

  data Gr : (fl : FunLang) -> (rfl : FunLang) -> Type where
    GrId : Gr fl fl
    Emb : (i : IndexFL fl pfl) -> (gr : Gr pfl efl) -> {auto prf : grUsesIn gr = True} -> Gr (replFL fl i efl) rfl -> Gr fl rfl
    Trans : (i : IndexFL fl pfl) -> (op : FunLangOp pfl orfl) -> Gr (replFL fl i orfl) rfl -> Gr fl rfl
    Com : {rfl : FunLang} -> (df : ((fnT : FunT fl) -> FunInst fnT -> FunT rfl)) -> Gr rfl nrfl -> Gr fl nrfl
  

  grUsesIn : Gr fl rfl -> Bool
  grUsesIn x = grUsesIn' x SEmpty where
    grUsesIn' : Gr fl rfl -> MSetFL fl -> Bool
    grUsesIn' GrId s = False
    grUsesIn' (Emb i gr x {efl}) SEmpty = grUsesIn' x $ SSome $ setFLAddEmpty i efl
    grUsesIn' (Emb i gr x {efl}) (SSome s) = let ns = contructSetFL $ setFLAdd s i efl in case (ns) of
                                                                            SElem => True
                                                                            _     => grUsesIn' x $ SSome ns
    grUsesIn' (Trans i op y) SEmpty = grUsesIn' y $ SEmpty
    grUsesIn' (Trans i op y) (SSome s) = grUsesIn' y $ SSome $ indTrSetFL s i op
    grUsesIn' (Com df x) s   = True




data EList : IndexFL ofl pfl -> Gr pfl _ -> Gr afl _ -> Nat -> Type where
  ENil : EList (LHere {fl=fl}) (GrId {fl=fl}) (GrId {fl=fl}) Z
  EL : (ni : IndexFL fl pfl) -> (nfgr : Gr pfl efl) -> (ngr : Gr (replFL fl ni efl) rfl) 
  -> {fgr : Gr _ rfl} -> EList i fgr gr k -> EList ni nfgr ngr (S k)

data EVect : EList ni nfgr ngr n -> Type where
  EVNill : EVect ENil
  EV : (ni : IndexFL fl pfl) -> {nfgr : Gr pfl efl} -> (ngr : Gr (replFL fl ni efl) rfl) -> {fgr : Gr _ rfl} 
  -> {prEL : EList i fgr gr k} -> (prL : FunT fl) ->  EVect prEL -> EVect $ EL ni nfgr ngr prEL





genDFT' : (gr : Gr fl rfl) -> {fgr : Gr pfl rfl} -> (el : EList ei fgr egr n) -> (EVect el -> FunT fl -> Type)
genDFT' GrId ENil {fl} = (\vhv, x => FunT fl)
genDFT' GrId (EL ei nfgr egr pEL) = (\ev, x =>  let EV _ _ prL prEV = ev in
                                                    (genDFT' egr pEL) prEV (replFT prL ei x))
genDFT' (Emb ni nfgr ngr {efl}) y = (\ ev, x => let tr = truncFT x ni in
                                                case (tr) of
                                                 Just tx => genDFT' nfgr (EL ni nfgr ngr y) (EV ni ngr x ev) tx
                                                 Nothing => let ntr = ifNotTruncFT x ni efl in
                                                            case (ntr) of
                                                              Just ntx => (genDFT' ngr y) ev ntx
                                                              _ => assert_unreachable
                                                                                       )
genDFT' (Trans i op z) y = (\ev, x => (genDFT' z y) ev $ indTrFT x i op )
genDFT' (Com df ngr) y = (\ev, x => (fi : FunInst x) -> (genDFT' ngr y) ev $ df x fi)


genDFT : (gr : Gr fl rfl) -> {auto prf : grUsesIn gr = True} -> ((EVect (ENil {fl=rfl})) -> FunT fl -> Type)
genDFT gr = genDFT' gr ENil {n=Z}


genDF : (gr : Gr fl rfl) -> {auto prf : grUsesIn gr = True} -> ((fnT : FunT fl) -> genDFT gr EVNill fnT)
genDF gr fnT = genDF' gr EVNill fnT where
  genDF' : (gr : Gr fl rfl) -> (ev : EVect el) -> ((fnT : FunT fl) -> genDFT' gr el ev fnT)
  genDF' GrId EVNill fnT = fnT
  genDF' GrId (EV ei egr prL y) fnT = (genDF' egr y) (replFT prL ei fnT)
  genDF' (Emb ni nfgr ngr {efl} ) ev fnT with (truncFT fnT ni)
    | Just tx = (genDF' nfgr (EV ni ngr fnT ev {nfgr=nfgr})) tx
    | Nothing with (ifNotTruncFT fnT ni efl) 
      | Just ntx = (genDF' ngr ev) ntx
      | Nothing = assert_unreachable
  genDF' (Trans i op x) ev fnT = genDF' x ev $ indTrFT fnT i op
  genDF' (Com df ngr) ev fnT = (\fi => genDF' ngr ev $ df fnT fi)



-- A gr is Full if all the data it receives is processed at least once.

--TODO ADD Agents, dependencies to previous inputs, total funT of a Gr operator.





