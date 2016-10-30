module Main

import Data.Vect

%default total

data Agent : Type where
  A: Agent
  B: Agent


--data Action : Agent -> Agent -> Type where
--  Send : (a: Agent) -> (b: Agent) -> Type -> Action a b
--
--data Spec : Agent -> Nat -> Type where
--  Next: Action a b -> Spec _ n -> Spec a (S n)
--  Fork: Vect k (Spec a n) -> Spec a (S n)
--  Merge: Vect k (Spec _ n) -> Spec a -> Spec a (S n)
--  Nill: Spec _ Z
--
--data LAction : Agent -> Type where
--  LSend : (b: Agent) -> Type -> LAction b
--  LRecv : (b: Agent) -> Type -> LAction b
--
--
--data LSpec : Nat -> Type where
--  LNext: LAction b -> LSpec k -> LSpec (S k)
--  LFork: Vect n (LSpec k) -> LSpec (S k)
--  LMerge: Vect n (LSpec k) -> LSpec (S k)
--  LNill: LSpec Z
--
--data TSpec : Type where
--  TNext : ((m:Nat) -> TSpec -> LSpec m) -> TSpec
--  TFork : ((m:Nat) -> Vect n TSpec -> LSpec m) -> TSpec
--  TFork : ((m:Nat) -> Vect n TSpec -> LSpec m) -> TSpec
--



