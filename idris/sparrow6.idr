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
  AndXorD : FunLangOp (Xor (Xor (And a1 b1) (And a1 b2)) $ Xor (And a2 b1) (And a2 b2)) rfl -> FunLangOp (And (Xor a1 a2) (Xor b1 b2)) rfl
  AndUorD : FunLangOp (Uor (Uor (And a1 b1) (And a1 b2)) $ Uor (And a2 b1) (And a2 b2)) rfl -> FunLangOp (And (Uor a1 a2) (Uor b1 b2)) rfl


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
trFT (TAnd (TXor (Left l)) (TXor (Left x))) (AndXorD y)   = trFT (TXor $ Left $ TXor $ Left $ TAnd l x) y
trFT (TAnd (TXor (Left l)) (TXor (Right r))) (AndXorD y)  = trFT (TXor $ Left $ TXor $ Right $ TAnd l r) y
trFT (TAnd (TXor (Right r)) (TXor (Left l))) (AndXorD y)  = trFT (TXor $ Right $ TXor $ Left $ TAnd r l) y
trFT (TAnd (TXor (Right r)) (TXor (Right x))) (AndXorD y) = trFT (TXor $ Right $ TXor $ Right $ TAnd r x) y
trFT (TAnd (TUor x w) (TUor z s)) (AndUorD y)             = trFT (TUor (TUor (TAnd x z) (TAnd x s)) $ TUor (TAnd w z) (TAnd w s)) y



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
trFI (IAnd (IXorLeft x) (IXorLeft z)) (AndXorD y)   = trFI (IXorLeft $ IXorLeft $ IAnd x z) y
trFI (IAnd (IXorLeft x) (IXorRight z)) (AndXorD y)  = trFI (IXorLeft $ IXorRight $ IAnd x z) y
trFI (IAnd (IXorRight x) (IXorLeft z)) (AndXorD y)  = trFI (IXorRight $ IXorLeft $ IAnd x z) y
trFI (IAnd (IXorRight x) (IXorRight z)) (AndXorD y) = trFI (IXorRight $ IXorRight $ IAnd x z) y
trFI (IAnd (IUor (Left x)) (IUor (Left l))) (AndUorD y)   = trFI (IUor $ Left $ IUor $ Left $ IAnd x l) y
trFI (IAnd (IUor (Right r)) (IUor (Left l))) (AndUorD y)  =  trFI (IUor $ Right $ IUor $ Left $ IAnd r l) y
trFI (IAnd (IUor (Left l)) (IUor (Right r))) (AndUorD y)  =  trFI (IUor $ Left $ IUor $ Right $ IAnd l r) y
trFI (IAnd (IUor (Right x)) (IUor (Right r))) (AndUorD y) =  trFI (IUor $ Right $ IUor $ Right $ IAnd x r) y


data IndexFL : FunLang -> FunLang -> Type where
  LHere     : IndexFL fl fl
  LLeftAnd  : IndexFL x rfl -> IndexFL (And x y) rfl
  LRightAnd : IndexFL y rfl -> IndexFL (And x y) rfl
  LLeftUor  : IndexFL x rfl -> IndexFL (Uor x y) rfl
  LRightUor : IndexFL y rfl -> IndexFL (Uor x y) rfl
  LLeftXor  : IndexFL x rfl -> IndexFL (Xor x y) rfl
  LRightXor : IndexFL y rfl -> IndexFL (Xor x y) rfl


trFL' : (fl : FunLang) -> IndexFL fl pfl -> FunLangOp pfl rfl -> FunLang
trFL' fl LHere y {rfl} = rfl
trFL' (And x z) (LLeftAnd w) y  = And (trFL' x w y) z
trFL' (And x z) (LRightAnd w) y = And x (trFL' z w y)
trFL' (Uor x z) (LLeftUor w) y  = Uor (trFL' x w y) z
trFL' (Uor x z) (LRightUor w) y = Uor x (trFL' z w y)
trFL' (Xor x z) (LLeftXor w) y  = Xor (trFL' x w y) z
trFL' (Xor x z) (LRightXor w) y = Xor x (trFL' z w y)

com : (fl : FunLang) -> {rfl : FunLang} -> IndexFL fl pfl -> FunLangOp pfl rfl -> {nrfl : FunLang} -> 
                        ({fnT : FunT rfl} -> FunInst fnT -> FunT nrfl) -> FunLang
com fl LHere y f {nrfl} = nrfl
com (And x z) (LLeftAnd w) y f  = And (com x w y f) z
com (And x z) (LRightAnd w) y f = And x (com z w y f)
com (Uor x z) (LLeftUor w) y f  = Uor (com x w y f) z
com (Uor x z) (LRightUor w) y f = Uor x (com z w y f)
com (Xor x z) (LLeftXor w) y f  = Xor (com x w y f) z
com (Xor x z) (LRightXor w) y f = Xor x (com z w y f)



data Gr : FunLang -> FunLang -> Type where
  Tr : (i : IndexFL fl pfl) -> (op : FunLangOp pfl rfl) -> Gr (trFL' fl i op) rfl -> Gr fl rfl
  Com : {rfl : FunLang} -> (i : IndexFL fl pfl) -> (op : FunLangOp pfl rfl) -> 
        {nrfl : FunLang} -> (df : ({fnT : FunT rfl} -> FunInst fnT -> FunT nrfl)) -> Gr (com fl {rfl=rfl} i op {nrfl=nrfl} df) rfl -> Gr fl rfl



--trFT' : {fl : FunLang} -> FunT pfl -> (i : IndexFL fl pfl) -> (op : FunLangOp pfl rfl) -> FunT $ trFL' fl i op
--trFT' x LHere y = trFT x y
--trFT' (TAnd x z) (LLeftAnd s) y = TAnd (trFT' x s y) z
--trFT' (TAnd x z) (LRightAnd s) y = TAnd x (trFT' z s y)
--trFT' (TUor x z) (LLeftUor s) y =  TUor (trFT' x s y) z
--trFT' (TUor x z) (LRightUor s) y =  TUor x (trFT' z s y)
--trFT' (TXor (Left l)) (LLeftXor s) y = ?dsf_3
--trFT' (TXor (Right r)) (LLeftXor s) y = ?dsf_4
--trFT' (TXor x) (LRightXor s) y = ?dsf_2
--


-- An index for FunT fl

data IndexFT : FunT fl -> Type where
  THere      : IndexFT $ fT
  TLeftAnd   : IndexFT x              -> IndexFT $ TAnd x y
  TRightAnd  : IndexFT y              -> IndexFT $ TAnd x y
  TLeftUor   : IndexFT x              -> IndexFT $ TUor x y
  TRightUor  : IndexFT y              -> IndexFT $ TUor x y
  TLeftXor   : IndexFT x              -> IndexFT $ TXor $ Left x
  TRightXor  : IndexFT y              -> IndexFT $ TXor $ Right y


-- An index for FunT fl

data IndexFI : FunInst fnT -> Type where
  IHere      : IndexFI $ fi
  ILeftAnd   : IndexFI x                 -> IndexFI $ IAnd x y
  IRightAnd  : IndexFI y                 -> IndexFI $ IAnd x y
  ILeftUor   : IndexFI x                 -> IndexFI $ IUor $ Left x
  IRightUor  : IndexFI y                 -> IndexFI $ IUor $ Right y
  ILeftXor   : IndexFI x                 -> IndexFI $ IXorLeft x
  IRightXor  : IndexFI y                 -> IndexFI $ IXorRight y






--tfunT : Type -> FunLang -> Type
--tfunT d fl = d -> FunT fl
--
--tfunInst : Type -> FunLang -> Type
--tfunInst d fl = (x :d) -> {funT : tfunT d fl} -> FunInst $ funT x
--
--
---- TODO FIX THIS 
---- Giving Roles based on the FunLang you have, need to be given for all FunLang in the Vect.
--
--data FunRoles : FunLang -> Type where
--    RAtom     : Role ->                     FunRoles $ Atom df
--    RAnd      : FunRoles a -> FunRoles b -> FunRoles $ And a b
--    RUor      : FunRoles a -> FunRoles b -> FunRoles $ Uor a b
--
--
--
--
--data IndFunLang : FunLang -> Type where
--  LHere     : IndFunLang $ Atom df
--  LLeftAnd  : IndFunLang x                 -> IndFunLang $ And x y
--  LRightAnd : IndFunLang y                 -> IndFunLang $ And x y
--  LBothAnd  : IndFunLang x -> IndFunLang y -> IndFunLang $ And x y
--  LLeftUor  : IndFunLang x                 -> IndFunLang $ Uor x y
--  LRightUor : IndFunLang y                 -> IndFunLang $ Uor x y
--  LBothUor  : IndFunLang x -> IndFunLang y -> IndFunLang $ Uor x y
--  LLeftXor  : IndFunLang x                 -> IndFunLang $ Xor x y
--  LRightXor : IndFunLang y                 -> IndFunLang $ Xor x y
--  LBothXor  : IndFunLang x -> IndFunLang y -> IndFunLang $ Xor x y
--
--
---- An index for FunT fl
--
--data IndFunT : FunT fl -> Type where
--  THere      : IndFunT $ TAtom hv
--  TLeftAnd   : IndFunT x              -> IndFunT $ TAnd x y
--  TRightAnd  : IndFunT y              -> IndFunT $ TAnd x y
--  TBothAnd   : IndFunT x -> IndFunT y -> IndFunT $ TAnd x y
--  TLeftUor   : IndFunT x              -> IndFunT $ TUor x y
--  TRightUor  : IndFunT y              -> IndFunT $ TUor x y
--  TBothUor   : IndFunT x -> IndFunT y -> IndFunT $ TUor x y
--  TLeftXor   : IndFunT x              -> IndFunT $ TXor $ Left x
--  TRightXor  : IndFunT y              -> IndFunT $ TXor $ Right y
--
--
---- An index for FunT fl
--
--data IndFunInst : FunInst fnT -> Type where
--  IHere      : IndFunInst $ IAtom v
--  ILeftAnd   : IndFunInst x                 -> IndFunInst $ IAnd x y
--  IRightAnd  : IndFunInst y                 -> IndFunInst $ IAnd x y
--  IBothAnd   : IndFunInst x -> IndFunInst y -> IndFunInst $ IAnd x y
--  ILeftUor   : IndFunInst x                 -> IndFunInst $ IUor $ Left x
--  IRightUor  : IndFunInst y                 -> IndFunInst $ IUor $ Right y
--  ILeftXor   : IndFunInst x                 -> IndFunInst $ IXorLeft x
--  IRightXor  : IndFunInst y                 -> IndFunInst $ IXorRight y
--
--
--
--
---- A data type that replaces the types of the used variables.
--data Used : Type where
--  WUsed : Used
--
--
--extractFunLang : IndFunLang fl -> FunLang
--extractFunLang (LHere {df=df}) = Atom df
--extractFunLang (LLeftAnd z)    = extractFunLang z
--extractFunLang (LRightAnd z)   = extractFunLang z
--extractFunLang (LBothAnd z w)  = And (extractFunLang z) (extractFunLang w)
--extractFunLang (LLeftUor z)    = extractFunLang z
--extractFunLang (LRightUor z)   = extractFunLang z
--extractFunLang (LBothUor z w)  = Uor (extractFunLang z) (extractFunLang w)
--extractFunLang (LLeftXor z)    = extractFunLang z
--extractFunLang (LRightXor z)   = extractFunLang z
--extractFunLang (LBothXor z w)  = Xor (extractFunLang z) (extractFunLang w)
--
--
--
---- An operator on FunT that takes all that it needs.
--
--extractFunLangT : IndFunT x -> FunLang
--extractFunLangT (THere) {x=TAtom {df=df} _} = Atom df
--extractFunLangT (TLeftAnd z)   = extractFunLangT z
--extractFunLangT (TRightAnd z)  = extractFunLangT z
--extractFunLangT (TBothAnd w s) = And (extractFunLangT w) (extractFunLangT s)
--extractFunLangT (TLeftUor z)   = extractFunLangT z
--extractFunLangT (TRightUor z)  = extractFunLangT z
--extractFunLangT (TBothUor w s) = Uor (extractFunLangT w) (extractFunLangT s)
--extractFunLangT (TLeftXor y)   = extractFunLangT y
--extractFunLangT (TRightXor x)  = extractFunLangT x
--
--
----TODO Need to provide checks that no used variables were accepted.
--extractFunTT : (i : IndFunT fnT) -> FunT $ extractFunLangT i
--extractFunTT (THere {hv=hv})  = TAtom hv
--extractFunTT (TLeftAnd z)     = extractFunTT z
--extractFunTT (TRightAnd z)    = extractFunTT z
--extractFunTT (TBothAnd w s)   = TAnd (extractFunTT w) (extractFunTT s)
--extractFunTT (TLeftUor z)     = extractFunTT z
--extractFunTT (TRightUor z)    = extractFunTT z
--extractFunTT (TBothUor w s)   = TUor (extractFunTT w) (extractFunTT s)
--extractFunTT (TLeftXor y)     = extractFunTT y
--extractFunTT (TRightXor x)    = extractFunTT x
--
--extractFunLangInst : IndFunInst fni -> FunLang
--extractFunLangInst IHere {fni=IAtom {df=df} _} = Atom df
--extractFunLangInst (ILeftAnd w)   = extractFunLangInst w
--extractFunLangInst (IRightAnd s)  = extractFunLangInst s
--extractFunLangInst (IBothAnd s t) = And (extractFunLangInst s) (extractFunLangInst t)
--extractFunLangInst (ILeftUor z)   = extractFunLangInst z
--extractFunLangInst (IRightUor w)  = extractFunLangInst w
--extractFunLangInst (ILeftXor y)   = extractFunLangInst y
--extractFunLangInst (IRightXor z)  = extractFunLangInst z
--
--extractFunTInst : {fni : FunInst fnT} -> (i : IndFunInst fni) -> FunT $ extractFunLangInst i
--extractFunTInst IHere {fnT=TAtom hv} = TAtom hv
--extractFunTInst (ILeftAnd w)   = extractFunTInst w
--extractFunTInst (IRightAnd s)  = extractFunTInst s
--extractFunTInst (IBothAnd s t) = TAnd (extractFunTInst s) (extractFunTInst t)
--extractFunTInst (ILeftUor z)   = extractFunTInst z
--extractFunTInst (IRightUor w)  = extractFunTInst w
--extractFunTInst (ILeftXor y)   = extractFunTInst y
--extractFunTInst (IRightXor z)  = extractFunTInst z
--
--extractFunInst : (i : IndFunInst fni) -> FunInst $ extractFunTInst i
--extractFunInst (IHere {v=v})  = IAtom v
--extractFunInst (ILeftAnd w)   = extractFunInst w
--extractFunInst (IRightAnd s)  = extractFunInst s
--extractFunInst (IBothAnd s t) = IAnd (extractFunInst s) (extractFunInst t)
--extractFunInst (ILeftUor z)   = extractFunInst z
--extractFunInst (IRightUor w)  = extractFunInst w
--extractFunInst (ILeftXor y)   = extractFunInst y
--extractFunInst (IRightXor z)  = extractFunInst z
--
--
----markUsed : {fnT : FunT fl} -> (i : IndFunT fnT) -> FunT fl
----markUsed (THere {a=a})  = TAtom Used
----markUsed (TLeftAnd z {y=y})   = TAnd (markUsed z) y
----markUsed (TRightAnd z {x=x})  = TAnd x (markUsed z)
----markUsed (TBothAnd w s)       = TAnd (markUsed w) (markUsed s)
----markUsed (TLeftUor z {y=y})   = TUor (markUsed z) y
----markUsed (TRightUor z {x=x})  = TUor x (markUsed z)
----markUsed (TBothUor w s)       = TUor (markUsed w) (markUsed s)
----markUsed (TLeftXor y)         = TXor $ Left $ markUsed y
----markUsed (TRightXor x)        = TXor $ Right $ markUsed x
--
--
--
--
--data OAFun : FunLang -> Type where
--  OFun : (i : IndFunLang fl) -> (d -> FunT ofl) -> OAFun fl
--
--data DComp : Type where
--  Comp : (fl : FunLang) -> Vect n (OAFun fl) -> DComp
--
--
--
--
----Probably add all FunInst with addition(And)?
----data DComp : Type where
----  Comp : (x : FunInst _) -> (vis : Vect n (IndFunInst x) ) -> DComp
--
----FunInst fnT -> FunInst nfnT
---- list of funInst -> [funInst, funInst2 funInst3] -> list of funInst
----
---- list of IndFunInst -> list of FunInsts -> gr_operators -> list of IndFunInsts -> FunInsts -> lower function calls -> FunInsts
----  
--
--
--
------ We define as G : [funT1 , funT2 ,.. ] the linear group of transformations of FunLang.
------ 
----
----mutual
----  OTrAct : FunLang -> Type where
----    OTrSingle : {fl : FunLang} -> ( (x : FunT fl) -> IndFunT x) -> ITrAct -> ItrAct fl
----
----  ITrAct : Type where
----    ITrSingle : OTrAct fl -> 
----
---- Composabolity or the Graph 
--
----nd : Type -> FunLang -> Type
----nd d fl = (y : d ** (tfunInst d fl) y)
----
----comp : (x : d) -> tfunInst d fl -> ( (x : nd d fl) -> tfunInst (nd d fl) nfl) -> string
----
----
