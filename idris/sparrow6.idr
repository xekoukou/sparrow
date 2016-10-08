module Sparrow


import Syntax.PreorderReasoning
import Data.Vect


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



data FunLang: Type where
  Atom : FunLang
  And : FunLang -> FunLang -> FunLang
--  Xor : Vect n FunLang -> FunLang  -- d decides on that
  Uor : FunLang -> FunLang -> FunLang


Eq FunLang where
  (==) Atom Atom = True
  (==) (And x y) (And z w) = ((x == z) && (y == w))
  (==) (Uor x y) (Uor z w) = ((x == z) && (y == w))
  (==) a b = False

data FunT : FunLang -> Type where
    TAtom : Type -> FunT Atom
    TAnd : FunT a -> FunT b -> FunT $ And a b
    TUor : FunT a -> FunT b -> FunT $ Uor a b


--data InSet : Eq a => Vect n a -> Type where
--  IsIn : Eq a => (x : a) -> {xs : Vect n a} -> {prf : ((elem x xs) = True)} -> InSet xs
--

-- Maybe this needs to be simplified.
data XorSet : Eq FunLang => Vect n FunLang -> Type where
  XorOpt : Eq FunLang => FunT x -> (xs : Vect n FunLang) -> {prf : ((elem x xs) = True)} -> XorSet xs



funT : d -> (v : Vect n FunLang) -> XorSet v

-- For the function that sends the actual data, we need to express the Uor in the same way that we expressed Xor in funT.

-- FunInst : d -> (v : Vect n FunLang) -> XorSet v

data FunInst : FunT a -> Type where
  IAtom : (a : Type) -> FunInst $ TAtom a
  IAnd : FunInst a -> FunInst b -> FunInst $ TAnd a b
  IUor : Either (FunInst a) (FunInst b) -> FunInst $ TUor a b

funInst : d -> (v : Vect n FunLang) -> let XorOpt x xs = funT d v in FunInst x


-- Giving Roles based on the FunLang you have, need to be given for all FunLang in the Vect.

data FunRoles : FunLang -> Type where
    RAtom : Role -> FunRoles Atom
    RAnd : FunRoles a -> FunRoles b -> FunRoles $ And a b
    RUor : FunRoles a -> FunRoles b -> FunRoles $ Uor a b




-- Composabolity or the Graph 


