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


indTrFL : (fl : FunLang) -> IndexFL fl pfl -> FunLangOp pfl rfl -> FunLang
indTrFL fl LHere y {rfl} = rfl
indTrFL (And x z) (LLeftAnd w) y  = And (indTrFL x w y) z
indTrFL (And x z) (LRightAnd w) y = And x (indTrFL z w y)
indTrFL (Uor x z) (LLeftUor w) y  = Uor (indTrFL x w y) z
indTrFL (Uor x z) (LRightUor w) y = Uor x (indTrFL z w y)
indTrFL (Xor x z) (LLeftXor w) y  = Xor (indTrFL x w y) z
indTrFL (Xor x z) (LRightXor w) y = Xor x (indTrFL z w y)

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

-- Here com turns Uor into Xor because based on thr input Uor we have knowledge of whether the f will be executed or not, without going into an FunInst function.
comFL : (fl : FunLang) -> IndexFL fl pfl -> ((fnT : FunT pfl) -> FunInst fnT -> FunT rfl) -> FunLang
comFL fl LHere f {rfl}   = rfl
comFL (And x z) (LLeftAnd w) f  = And (comFL x w f) z
comFL (And x z) (LRightAnd w) f = And x (comFL z w f)
comFL (Uor x z) (LLeftUor w) f  = Xor (comFL x w f) z
comFL (Uor x z) (LRightUor w) f = Xor x (comFL z w f)
comFL (Xor x z) (LLeftXor w) f  = Xor (comFL x w f) z
comFL (Xor x z) (LRightXor w) f = Xor x (comFL z w f)


comFT : (fT : FunT fl) -> FunInst fT -> (i : IndexFL fl pfl) -> (df : ((fnT : FunT pfl) -> FunInst fnT -> FunT rfl)) -> FunT $ comFL fl i df
comFT fT x LHere df = df fT x
comFT (TAnd y z) (IAnd x s) (LLeftAnd w) df = TAnd (comFT y x w df) z
comFT (TAnd y z) (IAnd x s) (LRightAnd w) df = TAnd y (comFT z s w df)
comFT (TUor y z) (IUor (Left l)) (LLeftUor w) df = TXor $ Left $ comFT y l w df
comFT (TUor y z) (IUor (Right r)) (LLeftUor w) df = TXor $ Right z
comFT (TUor y z) (IUor (Left l)) (LRightUor w) df = TXor $ Left y
comFT (TUor y z) (IUor (Right r)) (LRightUor w) df = TXor $ Right $ comFT z r w df
comFT (TXor (Left l)) (IXorLeft x) (LLeftXor w) df = TXor $ Left $ comFT l x w df
comFT (TXor (Right r)) (IXorRight x) (LLeftXor w) df = TXor $ Right r
comFT (TXor (Left l)) (IXorLeft x) (LRightXor w) df = TXor $ Left l
comFT (TXor (Right r)) (IXorRight x) (LRightXor w) df = TXor $ Right $ comFT r x w df






data Gr : (fl : FunLang) -> (rfl : FunLang) -> Nat  -> Type where
  GI : Gr fl fl Z
  Tr : (i : IndexFL fl pfl) -> (op : FunLangOp pfl _) -> Gr (indTrFL fl i op) rfl k -> Gr fl rfl (S k)
  Com : (i : IndexFL fl pfl) -> {rfl : FunLang} -> (df : ((fnT : FunT pfl) -> FunInst fnT -> FunT rfl)) -> Gr (comFL fl i df) nrfl k -> Gr fl nrfl (S k)


genDFT : Gr fl rfl n -> (FunT fl -> Type)
genDFT GI {fl} = (\x => FunT fl)  -- This is the identity type
genDFT (Tr i op y) {fl} = (\x => FunInst x -> (genDFT y) $ indTrFT x i op)
genDFT (Com i df y) = (\x => (fi : FunInst x) -> (genDFT y) $ comFT x fi i df)


genDF : (gr : Gr fl rfl n) -> ((fnT : FunT fl) -> genDFT gr fnT)
genDF GI = (\x => x)
genDF (Tr i op gr) = (\x, y => genDF gr $ indTrFT x i op)
genDF (Com i df gr) = (\x, y => genDF gr $ comFT x y i df) 



isGrFull : Gr fl rfl _ -> Bool
isGrFull x = ?isGrFull_rhs

-- A gr is Full if all the data it receives is processed at least once.

--TODO ADD Agents, dependencies to previous inputs, total funT of a Gr operator.





