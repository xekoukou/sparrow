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

setFLAddEmpty : IndexFL fl _ -> SetFL fl
setFLAddEmpty LHere = SElem
setFLAddEmpty (LLeftAnd z)  = SLeftAnd $ setFLAddEmpty z
setFLAddEmpty (LRightAnd z) = SRightAnd $ setFLAddEmpty z
setFLAddEmpty (LLeftUor z)  = SLeftUor $ setFLAddEmpty z
setFLAddEmpty (LRightUor z) = SRightUor $ setFLAddEmpty z
setFLAddEmpty (LLeftXor z)  = SLeftXor $ setFLAddEmpty z
setFLAddEmpty (LRightXor z) =  SRightXor $ setFLAddEmpty z

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


setFLAdd : SetFL fl -> IndexFL fl _ -> SetFL fl
setFLAdd SElem y = SElem
setFLAdd x LHere = SElem
setFLAdd (SLeftAnd x) (LLeftAnd w)    = SLeftAnd $ setFLAdd x w
setFLAdd (SRightAnd x) (LLeftAnd w)   = SBothAnd (setFLAddEmpty w) x
setFLAdd (SBothAnd x y) (LLeftAnd w)  = SBothAnd (setFLAdd x w) y
setFLAdd (SRightAnd x) (LRightAnd w)  = SRightAnd $ setFLAdd x w
setFLAdd (SLeftAnd x) (LRightAnd w)   = SBothAnd x (setFLAddEmpty w)
setFLAdd (SBothAnd x y) (LRightAnd w) = SBothAnd x (setFLAdd y w)
setFLAdd (SLeftUor x) (LLeftUor w)    = SLeftUor $ setFLAdd x w
setFLAdd (SRightUor x) (LLeftUor w)   = SBothUor (setFLAddEmpty w) x
setFLAdd (SBothUor x y) (LLeftUor w)  = SBothUor (setFLAdd x w) y
setFLAdd (SRightUor x) (LRightUor w)  = SRightUor $ setFLAdd x w
setFLAdd (SLeftUor x) (LRightUor w)   = SBothUor x (setFLAddEmpty w)
setFLAdd (SBothUor x y) (LRightUor w) = SBothUor x (setFLAdd y w)
setFLAdd (SLeftXor x) (LLeftXor w)    = SLeftXor $ setFLAdd x w
setFLAdd (SRightXor x) (LLeftXor w)   = SBothXor (setFLAddEmpty w) x
setFLAdd (SBothXor x y) (LLeftXor w)  = SBothXor (setFLAdd x w) y
setFLAdd (SRightXor x) (LRightXor w)  = SRightXor $ setFLAdd x w
setFLAdd (SLeftXor x) (LRightXor w)   = SBothXor x (setFLAddEmpty w)
setFLAdd (SBothXor x y) (LRightXor w) = SBothXor x (setFLAdd y w)



indTrFL : (fl : FunLang) -> IndexFL fl pfl -> FunLangOp pfl rfl -> FunLang
indTrFL fl LHere y {rfl} = rfl
indTrFL (And x z) (LLeftAnd w) y  = And (indTrFL x w y) z
indTrFL (And x z) (LRightAnd w) y = And x (indTrFL z w y)
indTrFL (Uor x z) (LLeftUor w) y  = Uor (indTrFL x w y) z
indTrFL (Uor x z) (LRightUor w) y = Uor x (indTrFL z w y)
indTrFL (Xor x z) (LLeftXor w) y  = Xor (indTrFL x w y) z
indTrFL (Xor x z) (LRightXor w) y = Xor x (indTrFL z w y)




trSetFL : SetFL fl -> (op : FunLangOp fl rfl) -> SetFL $ trFL fl op
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


indTrSetFL : SetFL fl -> (i : IndexFL fl pfl) -> (op : FunLangOp pfl rfl) -> SetFL $ indTrFL fl i op
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



indTrFT : FunT fl -> (i: IndexFL fl pfl) -> (op : FunLangOp pfl rfl) -> FunT $ indTrFL fl i op
indTrFT x LHere op = trFT x op
indTrFT (TAnd x y) (LLeftAnd w) op = TAnd (indTrFT x w op) y
indTrFT (TAnd x y) (LRightAnd w) op = TAnd x $ indTrFT y w op
indTrFT (TUor x y) (LLeftUor w) op = TUor (indTrFT x w op) y
indTrFT (TUor x y) (LRightUor w) op = TUor x $ indTrFT y w op
indTrFT (TXor (Left l)) (LLeftXor w) op = TXor (Left $ indTrFT l w op)
indTrFT (TXor (Right r)) (LLeftXor w) op = TXor (Right r)
indTrFT (TXor (Left l)) (LRightXor w) op = TXor (Left l)
indTrFT (TXor (Right r)) (LRightXor w) op =  TXor (Right $ indTrFT r w op)


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


xreplFL : (fl : FunLang) -> IndexFL fl _ -> FunLang -> FunLang
xreplFL fl LHere y = y
xreplFL (And x z) (LLeftAnd w) y  = And (xreplFL x w y) z
xreplFL (And x z) (LRightAnd w) y = And x (xreplFL z w y)
xreplFL (Uor x z) (LLeftUor w) y  = Xor (xreplFL x w y) z
xreplFL (Uor x z) (LRightUor w) y = Xor x (xreplFL z w y)
xreplFL (Xor x z) (LLeftXor w) y  = Xor (xreplFL x w y) z
xreplFL (Xor x z) (LRightXor w) y = Xor x (xreplFL z w y)


xreplFT : FunT fl -> (i: IndexFL fl _) -> FunT $ nfl -> FunT $ xreplFL fl i nfl
xreplFT x LHere nfT  = nfT
xreplFT (TAnd x y) (LLeftAnd w) nfT   = TAnd (xreplFT x w nfT) y
xreplFT (TAnd x y) (LRightAnd w) nfT  = TAnd x $ xreplFT y w nfT
xreplFT (TUor x y) (LLeftUor w) nfT   = TXor (Left $ xreplFT x w nfT)
xreplFT (TUor x y) (LRightUor w) nfT  = TXor (Right $ xreplFT y w nfT)
xreplFT (TXor (Left l)) (LLeftXor w) nfT   = TXor (Left $ xreplFT l w nfT)
xreplFT (TXor (Right r)) (LLeftXor w) nfT  = TXor (Right r)
xreplFT (TXor (Left l)) (LRightXor w) nfT  = TXor (Left l)
xreplFT (TXor (Right r)) (LRightXor w) nfT =  TXor (Right $ xreplFT r w nfT)


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
    Emb : (i : IndexFL fl pfl) -> (gr : Gr pfl efl) -> {auto prf : grUsesIn gr = True} -> Gr (xreplFL fl i efl) rfl -> Gr fl rfl
    Trans : (i : IndexFL fl pfl) -> (op : FunLangOp pfl _) -> Gr (indTrFL fl i op) rfl -> Gr fl rfl
    Com : {rfl : FunLang} -> (df : ((fnT : FunT fl) -> FunInst fnT -> FunT rfl)) -> Gr rfl nrfl -> Gr fl nrfl
  

-- IndGrSetFL actually adds i inside SetFL 
  indGrSetFL : SetFL fl  -> (i: IndexFL fl pfl) -> (gr : Gr pfl rfl) -> SetFL (xreplFL fl i rfl)
  indGrSetFL SElem i gr = SElem
  indGrSetFL x LHere gr = SElem
  indGrSetFL (SLeftAnd x) (LLeftAnd w) gr    = SLeftAnd $ indGrSetFL x w gr
  indGrSetFL (SRightAnd x) (LLeftAnd w) gr   = SRightAnd x
  indGrSetFL (SBothAnd x y) (LLeftAnd w) gr  = SBothAnd (indGrSetFL x w gr) y
  indGrSetFL (SLeftAnd x) (LRightAnd w) gr   = SLeftAnd x
  indGrSetFL (SRightAnd x) (LRightAnd w) gr  = SRightAnd $ indGrSetFL x w gr
  indGrSetFL (SBothAnd x y) (LRightAnd w) gr = SBothAnd x (indGrSetFL y w gr)
  indGrSetFL (SLeftUor x) (LLeftUor w) gr    = SLeftXor $ indGrSetFL x w gr
  indGrSetFL (SRightUor x) (LLeftUor w) gr   = SRightXor x
  indGrSetFL (SBothUor x y) (LLeftUor w) gr  = SBothXor (indGrSetFL x w gr) y
  indGrSetFL (SLeftUor x) (LRightUor w) gr   = SLeftXor x
  indGrSetFL (SRightUor x) (LRightUor w) gr  = SRightXor $ indGrSetFL x w gr
  indGrSetFL (SBothUor x y) (LRightUor w) gr = SBothXor x (indGrSetFL y w gr)
  indGrSetFL (SLeftXor x) (LLeftXor w) gr    = SLeftXor $ indGrSetFL x w gr
  indGrSetFL (SRightXor x) (LLeftXor w) gr   = SRightXor x
  indGrSetFL (SBothXor x y) (LLeftXor w) gr  = SBothXor (indGrSetFL x w gr) y
  indGrSetFL (SLeftXor x) (LRightXor w) gr   = SLeftXor x
  indGrSetFL (SRightXor x) (LRightXor w) gr  = SRightXor $ indGrSetFL x w gr
  indGrSetFL (SBothXor x y) (LRightXor w) gr = SBothXor x (indGrSetFL y w gr)
  

  indGrSetFLEmpty : (i: IndexFL fl pfl) -> (gr : Gr pfl rfl) -> SetFL (xreplFL fl i rfl)
  indGrSetFLEmpty LHere gr = SElem
  indGrSetFLEmpty (LLeftAnd z) gr  = SLeftAnd $ indGrSetFLEmpty z gr
  indGrSetFLEmpty (LRightAnd z) gr = SRightAnd $ indGrSetFLEmpty z gr
  indGrSetFLEmpty (LLeftUor z)  gr = SLeftXor $ indGrSetFLEmpty z gr
  indGrSetFLEmpty (LRightUor z) gr = SRightXor $ indGrSetFLEmpty z gr
  indGrSetFLEmpty (LLeftXor z)  gr = SLeftXor $ indGrSetFLEmpty z gr
  indGrSetFLEmpty (LRightXor z) gr =  SRightXor $ indGrSetFLEmpty z gr
  


  grUsesIn : Gr fl rfl -> Bool
  grUsesIn x = grUsesIn' x SEmpty where
    grUsesIn' : Gr fl rfl -> MSetFL fl -> Bool
    grUsesIn' GrId s = False
    grUsesIn' (Emb i gr x) SEmpty = grUsesIn' x $ SSome $ indGrSetFLEmpty i gr
    grUsesIn' (Emb i gr x) (SSome s) = let ns = contructSetFL $ indGrSetFL s i gr in case (ns) of
                                                                            SElem => True
                                                                            _     => grUsesIn' x $ SSome ns
    grUsesIn' (Trans i op y) SEmpty = grUsesIn' y $ SEmpty
    grUsesIn' (Trans i op y) (SSome s) = grUsesIn' y $ SSome $ indTrSetFL s i op
    grUsesIn' (Com df x) s   = True


indGrInd : (i: IndexFL fl pfl) -> (gr : Gr pfl efl) ->  IndexFL (xreplFL fl i efl) efl
indGrInd LHere gr = LHere
indGrInd (LLeftAnd z) gr  = LLeftAnd $ indGrInd z gr
indGrInd (LRightAnd z) gr = LRightAnd $ indGrInd z gr
indGrInd (LLeftUor z)  gr = LLeftXor $ indGrInd z gr
indGrInd (LRightUor z) gr = LRightXor $ indGrInd z gr
indGrInd (LLeftXor z)  gr = LLeftXor $ indGrInd z gr
indGrInd (LRightXor z) gr = LRightXor $ indGrInd z gr



data EList : IndexFL ofl pfl -> Gr pfl _ -> Gr afl _ -> Nat -> Type where
  ENil : EList (LHere {fl=fl}) (GrId {fl=fl}) (GrId {fl=fl}) Z
  EL : (ni : IndexFL fl pfl) -> (nfgr : Gr pfl efl) -> (ngr : Gr (xreplFL fl ni efl) rfl) 
  -> {fgr : Gr _ rfl} -> EList i fgr gr k -> EList ni nfgr ngr (S k)

data EVect : EList ni nfgr ngr n -> Type where
  EVNill : EVect ENil
  EV : {ni : IndexFL fl pfl} -> {nfgr : Gr pfl efl} -> {ngr : Gr (xreplFL fl ni efl) rfl} -> {fgr : Gr _ rfl} 
  -> {prEL : EList i fgr gr k} -> (prL : FunT fl) ->  EVect prEL -> EVect $ EL ni nfgr ngr prEL

mutual
  genDFT : (gr : Gr fl rfl) -> {auto prf : grUsesIn gr = True} -> ((EVect (ENil {fl=rfl})) -> FunT fl -> Type)
  genDFT gr = genDFT' gr ENil {n=Z} where
    genDFT' : (gr : Gr fl rfl) -> {fgr : Gr pfl rfl} -> (el : EList ei fgr egr n) -> (EVect el -> FunT fl -> Type)
    genDFT' GrId ENil {fl} = (\vhv, x => FunT fl)
    genDFT' GrId (EL ei nfgr egr pEL) = (\ev, x =>  let EV prL prEV = ev in
                                                        (genDFT' egr pEL) prEV (xreplFT prL ei x))
    genDFT' (Emb ni nfgr ngr ) y = (\ ev, x => case (truncFT x ni) of
                                            Just tx => genDFT' nfgr (EL ni nfgr ngr y) (EV x ev) tx
                                            Nothing => ?dsf--genDFT' y x
                                                                           )
    genDFT' (Trans i op z) y = ?fgfg_3
    genDFT' (Com df x) y = ?fgfg_4

--mutual 
--  genDFT : (gr : Gr fl rfl) -> {auto prf : grUsesIn gr = True} -> (FunT fl -> Type)
--  genDFT gr {rfl=rfl'} = genDFT' gr Nothing {nu=rfl'} where
--    genDFT' : (gr : Gr fl rfl) -> Maybe $ (IndexFL rfl nu, FunLang) -> (FunT fl -> Type)
--    genDFT' GrId {fl} mExt = (\x => case (mExt) of
--                                        Nothing => FunT fl
--                                        Just (i, efl) => FunT $ replFL fl i efl )
--    genDFT' (Emb i gr y) mExt {fl} = (\x => case (truncFT x i) of
--                                            Just tx => (genDFT' gr (indGrInd i gr, indGrExtFL fl i gr)) tx
--                                            Nothing => ?dsf--genDFT' y x
--                                                                       )
--    genDFT' (Trans i op z) mExt = (\x => (genDFT' z mExt) $ indTrFT x i op )
--    genDFT' (Com df y) mExt = (\x => (fi : FunInst x) -> (genDFT' y mExt) $ df x fi)
--      
    
  --genDFT GI {fl} = (\x => FunT fl)  -- This is the identity type
  --genDFT (Tr i op y) {fl} = (\x => FunInst x -> (genDFT y) $ indTrFT x i op)
  --genDFT (Com i df y) = (\x => (fi : FunInst x) -> (genDFT y) $ comFT x fi i df)
  --
  --
--  genDF : (gr : Gr fl rfl) -> {auto prf : grUsesIn gr = True} -> ((fnT : FunT fl) -> genDFT gr fnT)
  --genDF GI = (\x => x)
  --genDF (Tr i op gr) = (\x, y => genDF gr $ indTrFT x i op)
  --genDF (Com i df gr) = (\x, y => genDF gr $ comFT x y i df) 
  --

--  extGenDF : FunT fl -> (i : IndexFL fl pfl) -> (gr : Gr pfl rfl) -> 



-- A gr is Full if all the data it receives is processed at least once.

--TODO ADD Agents, dependencies to previous inputs, total funT of a Gr operator.





