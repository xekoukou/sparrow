module LinLogic


import public Syntax.PreorderReasoning
import public Data.Vect
import public Data.HVect
import public Prelude.Uninhabited

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


||| Linear Logic Cconnectives : Used to describe the input
||| and output of an agent.
|||
data LinLogic: Type where
  ||| When nothing is sent or recieved.
  Nil  : LinLogic
  ||| Contains a function that computes a dependent type
  Atom : {dt : Vect n Type} -> genT dt -> LinLogic 
--  ||| Represents a lambda (LFun) type.
--  LambdaT : LinLogic -> LinLogic -> LinLogic 
  ||| Both sub-connectives need to be sent or received.
  And  : Inf LinLogic -> Inf LinLogic -> LinLogic
  ||| Only one sub-connective can be sent or received
  ||| and the protocol specification has no control over which
  ||| choice will be made.
  Uor  : Inf LinLogic -> Inf LinLogic -> LinLogic
  ||| Only one sub-connective can be sent or received 
  ||| and the protocol determines the choice based on the previous
  ||| input of the agent.
  Dor  : Inf LinLogic -> Inf LinLogic -> LinLogic  -- d decides on that


||| Transformations to the Linear logic so as to construct
||| the correct sub-connective that is the input of a
||| linear function.
data LLTr : LinLogic -> LinLogic -> Type where
  Id      : LLTr ll ll
  ||| Commutative transformation for Dor
  DorC    : LLTr (Dor b a) rll   -> LLTr (Dor a b) rll
  ||| Commutative transformation for And
  AndC    : LLTr (And b a) rll   -> LLTr (And a b) rll
  ||| Commutative transformation for Uor
  UorC    : LLTr (Uor b a) rll   -> LLTr (Uor a b) rll
  ||| Distributive transformation for Dor
  AndDorD : LLTr (Dor (And a1 c) (And a2 c)) rll -> LLTr (And (Dor a1 a2) c) rll
  ||| Distributive transformation for Uor
  AndUorD : LLTr (Uor (And a1 c) (And a2 c)) rll -> LLTr (And (Uor a1 a2) c) rll



--hasLambdaT : LinLogic -> Bool
--hasLambdaT (Atom x) = False
--hasLambdaT (LambdaT x y) = True
--hasLambdaT (And x y) = hasLambdaT x || hasLambdaT y
--hasLambdaT (Uor x y) = hasLambdaT x || hasLambdaT y
--hasLambdaT (Dor x y) = hasLambdaT x || hasLambdaT y
--

||| Indexes over a specific node of a linear logic tree/sequence.
data IndexLL : LinLogic -> LinLogic -> Type where
  LHere     : IndexLL ll ll
  LLeftAnd  : IndexLL x rll -> IndexLL (And x y) rll
  LRightAnd : IndexLL y rll -> IndexLL (And x y) rll
  LLeftUor  : IndexLL x rll -> IndexLL (Uor x y) rll
  LRightUor : IndexLL y rll -> IndexLL (Uor x y) rll
  LLeftDor  : IndexLL x rll -> IndexLL (Dor x y) rll
  LRightDor : IndexLL y rll -> IndexLL (Dor x y) rll


||| Replaces a node of a linear logic tree with another one.
replLL : (ll : LinLogic) -> IndexLL ll _ -> LinLogic -> LinLogic
replLL ll LHere y = y
replLL (And x z) (LLeftAnd w) y  = And (replLL x w y) z
replLL (And x z) (LRightAnd w) y = And x (replLL z w y)
replLL (Uor x z) (LLeftUor w) y  = Uor (replLL x w y) z
replLL (Uor x z) (LRightUor w) y = Uor x (replLL z w y)
replLL (Dor x z) (LLeftDor w) y  = Dor (replLL x w y) z
replLL (Dor x z) (LRightDor w) y = Dor x (replLL z w y)



||| A non-empty set of points in a Linear Logic tree.
data SetLL : LinLogic -> Type where
  SElem      : SetLL ll
  SLeftAnd   : SetLL x -> SetLL (And x y) 
  SRightAnd  : SetLL y -> SetLL (And x y) 
  SBothAnd   : SetLL x -> SetLL y -> SetLL (And x y) 
  SLeftUor   : SetLL x -> SetLL (Uor x y) 
  SRightUor  : SetLL y -> SetLL (Uor x y) 
  SBothUor   : SetLL x -> SetLL y -> SetLL (Uor x y) 
  SLeftDor   : SetLL x -> SetLL (Dor x y) 
  SRightDor  : SetLL y -> SetLL (Dor x y) 
  SBothDor   : SetLL x -> SetLL y -> SetLL (Dor x y) 

||| A possible empty set of points in a Linear Logic tree.
data MSetLL : LinLogic -> Type where
  SEmpty : MSetLL ll
  SSome : SetLL ll -> MSetLL ll

||| Adds a point to an empty set.
||| @ i indexes to the node that is to be inserted.
setLLAddEmpty : (i: IndexLL ll _) -> (rll : LinLogic) -> SetLL $ replLL ll i rll
setLLAddEmpty LHere rll = SElem
setLLAddEmpty (LLeftAnd z)  rll = SLeftAnd $ setLLAddEmpty z rll
setLLAddEmpty (LRightAnd z) rll = SRightAnd $ setLLAddEmpty z rll
setLLAddEmpty (LLeftUor z)  rll = SLeftUor $ setLLAddEmpty z rll
setLLAddEmpty (LRightUor z) rll = SRightUor $ setLLAddEmpty z rll
setLLAddEmpty (LLeftDor z)  rll = SLeftDor $ setLLAddEmpty z rll
setLLAddEmpty (LRightDor z) rll =  SRightDor $ setLLAddEmpty z rll

||| If two adjecent nodes exist in the set, the higher node is
||| in the set. We contruct the set.
contructSetLL : SetLL ll -> SetLL ll
contructSetLL (SBothAnd SElem SElem)  = SElem
contructSetLL (SBothUor SElem SElem)  = SElem
contructSetLL (SBothDor  SElem SElem) = SElem
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
contructSetLL (SLeftDor z) = (SLeftDor (contructSetLL z))
contructSetLL (SRightDor z) = (SRightDor (contructSetLL z))
contructSetLL (SBothDor z w) = let  cr = (SBothDor (contructSetLL z) (contructSetLL w)) in
                                   case (cr) of
                                        (SBothDor SElem SElem) => SElem
                                        _                      => cr


||| Adds a point in a SetLL
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
setLLAdd (SLeftDor x) (LLeftDor w)    rll = SLeftDor $ setLLAdd x w rll
setLLAdd (SRightDor x) (LLeftDor w)   rll = SBothDor (setLLAddEmpty w rll) x
setLLAdd (SBothDor x y) (LLeftDor w)  rll = SBothDor (setLLAdd x w rll) y
setLLAdd (SRightDor x) (LRightDor w)  rll = SRightDor $ setLLAdd x w rll
setLLAdd (SLeftDor x) (LRightDor w)   rll = SBothDor x (setLLAddEmpty w rll)
setLLAdd (SBothDor x y) (LRightDor w) rll = SBothDor x (setLLAdd y w rll)



||| If we transform a linear logic tree, we need to transform the SetLL 
||| as well.
trSetLL : SetLL ll -> (ltr : LLTr ll rll) -> SetLL $ replLL ll LHere rll
trSetLL SElem ltr = SElem
trSetLL x Id = x
trSetLL (SLeftDor x) (DorC y)   = trSetLL (SRightDor x) y
trSetLL (SRightDor x) (DorC y)  = trSetLL (SLeftDor x) y
trSetLL (SBothDor x z) (DorC y) = trSetLL (SBothDor z x) y
trSetLL (SLeftAnd x) (AndC y)   = trSetLL (SRightAnd x) y
trSetLL (SRightAnd x) (AndC y)  = trSetLL (SLeftAnd x) y
trSetLL (SBothAnd x z) (AndC y) = trSetLL (SBothAnd z x) y
trSetLL (SLeftUor x) (UorC y)   = trSetLL (SRightUor x) y
trSetLL (SRightUor x) (UorC y)  = trSetLL (SLeftUor x) y
trSetLL (SBothUor x z) (UorC y) = trSetLL (SBothUor z x) y
trSetLL (SLeftAnd SElem) (AndDorD y) = trSetLL (SBothDor (SLeftAnd SElem) (SLeftAnd SElem)) y
trSetLL (SLeftAnd (SLeftDor x)) (AndDorD y) = trSetLL (SLeftDor $ SLeftAnd x) y
trSetLL (SLeftAnd (SRightDor x)) (AndDorD y) = trSetLL (SRightDor $ SLeftAnd x) y
trSetLL (SLeftAnd (SBothDor x z)) (AndDorD y) = trSetLL (SBothDor (SLeftAnd x) (SLeftAnd z)) y
trSetLL (SRightAnd x) (AndDorD y) = trSetLL (SBothDor (SRightAnd x) (SRightAnd x)) y
trSetLL (SBothAnd SElem z) (AndDorD y) = trSetLL (SBothDor (SBothAnd SElem z) (SBothAnd SElem z)) y
trSetLL (SBothAnd (SLeftDor x) z) (AndDorD y) = trSetLL (SLeftDor $ SBothAnd x z) y
trSetLL (SBothAnd (SRightDor x) z) (AndDorD y) =  trSetLL (SRightDor $ SBothAnd x z) y
trSetLL (SBothAnd (SBothDor x w) z) (AndDorD y) = trSetLL (SBothDor (SBothAnd x z) (SBothAnd w z)) y
trSetLL (SLeftAnd SElem) (AndUorD y) = trSetLL (SBothUor (SLeftAnd SElem) (SLeftAnd SElem)) y
trSetLL (SLeftAnd (SLeftUor x)) (AndUorD y) = trSetLL (SLeftUor $ SLeftAnd x) y
trSetLL (SLeftAnd (SRightUor x)) (AndUorD y) = trSetLL (SRightUor $ SLeftAnd x) y
trSetLL (SLeftAnd (SBothUor x z)) (AndUorD y) = trSetLL (SBothUor (SLeftAnd x) (SLeftAnd z)) y
trSetLL (SRightAnd x) (AndUorD y) = trSetLL (SBothUor (SRightAnd x) (SRightAnd x)) y
trSetLL (SBothAnd SElem z) (AndUorD y) = trSetLL (SBothUor (SBothAnd SElem z) (SBothAnd SElem z)) y
trSetLL (SBothAnd (SLeftUor x) z) (AndUorD y) = trSetLL (SLeftUor $ SBothAnd x z) y
trSetLL (SBothAnd (SRightUor x) z) (AndUorD y) =  trSetLL (SRightUor $ SBothAnd x z) y
trSetLL (SBothAnd (SBothUor x w) z) (AndUorD y) = trSetLL (SBothUor (SBothAnd x z) (SBothAnd w z)) y


||| Transform a SetLL from a specific node only determined by the index.
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
indTrSetLL (SLeftDor x) (LLeftDor w) ltr    = SLeftDor $ indTrSetLL x w ltr
indTrSetLL (SRightDor x) (LLeftDor w) ltr   = SRightDor x
indTrSetLL (SBothDor x y) (LLeftDor w) ltr  = SBothDor (indTrSetLL x w ltr) y
indTrSetLL (SLeftDor x) (LRightDor w) ltr   = SLeftDor x
indTrSetLL (SRightDor x) (LRightDor w) ltr  = SRightDor $ indTrSetLL x w ltr
indTrSetLL (SBothDor x y) (LRightDor w) ltr = SBothDor x (indTrSetLL y w ltr)



data IsFiniteLL : LinLogic -> Type where
  IsFNil  : IsFiniteLL Nil
  IsFAtom : IsFiniteLL $ Atom _
  IsFAnd  : IsFiniteLL x -> IsFiniteLL y -> IsFiniteLL $ And x y
  IsFUor  : IsFiniteLL x -> IsFiniteLL y -> IsFiniteLL $ Uor x y
  IsFDor  : IsFiniteLL x -> IsFiniteLL y -> IsFiniteLL $ Dor x y

isFiniteLL : (ll : LinLogic) -> Nat -> Maybe $ IsFiniteLL ll
isFiniteLL x Z = Nothing
isFiniteLL [] (S k) = Just $ IsFNil
isFiniteLL (Atom x) (S k)  = Just $ IsFAtom
isFiniteLL (And x y) (S k) = Just $ IsFAnd !(isFiniteLL x k) !(isFiniteLL y k)
isFiniteLL (Uor x y) (S k) = Just $ IsFUor !(isFiniteLL x k) !(isFiniteLL y k)
isFiniteLL (Dor x y) (S k) = Just $ IsFDor !(isFiniteLL x k) !(isFiniteLL y k)


falseNotTrue : False = True -> Void
falseNotTrue Refl impossible

onlyNilOrNoNil : (ll : LinLogic) -> IsFiniteLL ll -> Bool
onlyNilOrNoNil [] isf = True
onlyNilOrNoNil ll isf = onlyNilOrNoNil' ll isf where
  onlyNilOrNoNil' : (ll : LinLogic) -> IsFiniteLL ll -> Bool
  onlyNilOrNoNil' [] IsFNil = False
  onlyNilOrNoNil' (Atom x) IsFAtom  = True
  onlyNilOrNoNil' (And x y) (IsFAnd z w) =(onlyNilOrNoNil' x z) && (onlyNilOrNoNil' y w)
  onlyNilOrNoNil' (Uor x y) (IsFUor z w) =(onlyNilOrNoNil' x z) && (onlyNilOrNoNil' y w)
  onlyNilOrNoNil' (Dor x y) (IsFDor z w) =(onlyNilOrNoNil' x z) && (onlyNilOrNoNil' y w)
