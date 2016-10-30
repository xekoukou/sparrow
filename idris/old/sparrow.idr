module Main

import Data.HVect
import Data.Fin

%default total

-- TODO When we merge two worlds, we are unable to have access to the compautation results of one of the branches
-- becuase they are in a different lambda tree. Thus, we need to pass the values to the merged function from its input.


-- hmap : (f: (a -> Type)) -> ((x: a) -> f x) -> (b: Vect n a) -> HVect (map f b) 
-- hmap f c [] = [] 
-- hmap f c (x :: xs) = (c x) :: (hmap f c xs)



mutual 
  data TSFun : Vect SFun _ _ _ _ -> Type where
    MkTSFun : (a : SFun _ _ _ _) -> TSFun a
-- TODO Should this be Infinite function definitions. Probably it won't be infinite because we will finish at some point a specific session.
-- TODO We need to alter this to enable if statements.
  data SFun :  Vect n Type -> Vect k Type -> Vect l Type -> Type -> Type where
    SFEnd : SFun Nil Nil Nil Nat
    CSFun : {a : Type} -> {r : HVect (SFun _ _ _ _)} -> ( HVect vn -> HVect vk -> HVect vl -> (a , ?dsdf) ) -> SFun vn vk vl a  -- IMPORTANT We make at least one io operation.

-- Sparrow will give the function some data.
-- First, it will give the data it received from the io, then data from other branches of the computation. Lastly, it will give data that are global to all sessions.

-- A function will need to receive those data and return a new function for the next step.
-- Thus it should look like this:
-- IOData -> CompData -> GlobData -> (Tweet(a) , (IOData -> CompData -> GlobData -> ... ))  --> They are pure functions, so no need to care for referential transparency.
--
-- Now the type of Fun and type of Tweet depends on the state of the world.


-- Next, we need to build the state machine of the function.

-- The internal data as well as the consistent data should not be part of the protocol because they are internal data structures. But we do need to specify them.

-- We need a partially ordered map of SFun with the possible inputs it can receive.

-- We need to know the total number of edges. We cannot guarantee upon contstruction that the graph will be a correct one because we need to reference future nodes that we have't defined yet
-- but we should check that the number of the rule is within the number of rules.

data SGraph : Nat -> Vect h Type -> Type -> Type where  
  SNil : SGraph Z Nil Nat
  CSGraph : (vk: Vect k Type) -> (a: Type) -> Vect i Nat -> Vect l (Nat, Nat) -> SGraph n _ _ -> SGraph (S n) vk a



-- TODO We need to perform those check at compile time.
-- Here the first Nat represents the total number of Rules. It is equal to the n of the last SGraph.
isSGraphCorrect : Nat -> SGraph n _ _ -> Bool
isSGraphCorrect k SNil = True 
isSGraphCorrect k (CSGraph _ _ ys zs x) = foldr (\x,r => r && (k >= x)) True ys && foldr (\(x, _) ,r => r && (k >= x)) True zs && isSGraphCorrect k x


findInputLength : SGraph n _ _ -> Vect n Nat
findInputLength SNil = Nil
findInputLength (CSGraph vk _ _ _ y {k=k}) = k :: findInputLength y


vectToList : Vect n a -> List a
vectToList [] = []
vectToList (x :: xs) = x :: vectToList xs

getAll : SGraph n _ _ -> List (Nat, Nat)
getAll SNil = []
getAll (CSGraph _ _ ys zs y) = concat ((getAll y) :: (vectToList zs) :: List.Nil)

sortAll : List (Nat, Nat) -> List (Nat, Nat)
sortAll xs = sortBy (\(x1, x2), (y1, y2) => let c1 = compare x1 x2 in
                                                case (c1) of
                                                     EQ => compare x2 y2
                                                     _ => c1                ) xs

splitIntoLists : List (Nat, Nat) -> List (List Nat)
splitIntoLists xs = splitIntoLists' Z xs Nil Nil where
  splitIntoLists' : Nat -> List (Nat, Nat) -> List Nat -> List (List Nat) -> List (List Nat)
  splitIntoLists' n Nil l r = r -- Will only be reached when it is Nil from the start, thus l,r are also Nil.
  splitIntoLists' n ( (y1, y2) :: Nil) l r = case (y1 == n) of
                                               True => (nub (y2 :: l)) :: r
                                               False => [y2] :: (nub l) :: r
  splitIntoLists' n ( (y1, y2) :: ys ) l r = case (y1 == n) of
                                               True => splitIntoLists' n ys (y2 :: l) r
                                               False => splitIntoLists' n ys [y2] ((nub l) :: r)


checkCorrect : List Nat -> List (List Nat) -> Bool
checkCorrect [] [] = True
checkCorrect [] (x :: xs) = False
checkCorrect (x :: xs) [] = False
checkCorrect (x :: xs) (y :: ys) = case (x == length y) of
                                        False => False
                                        True => case (y) of
                                                     z :: zs => case (last (z :: zs) == x) of
                                                                     False => False
                                                                     True => checkCorrect xs ys
                                                     Nil => True



--TODO At compile-time
isGraphCorrect2 : SGraph n _ _ -> Bool    -- This checks that the inputs of SFun have other Sfuns that enable those inputs to be received.
isGraphCorrect2 x = let il = vectToList $ findInputLength x in
                        let oil = splitIntoLists $ sortAll $ getAll x in
                            checkCorrect il oil

---- The nat points to the rule that corresponds to the first SFun
--doesSFunRespectSGraph : Nat -> SGraph n vk a -> SFun _ vk _ a -> Bool
--doesSFunRespectSGraph k SNil SFEnd = True
--doesSFunRespectSGraph k SNil (CSFun f) = False
--doesSFunRespectSGraph k (CSGraph [] _ ys zs z) SFEnd = False
--doesSFunRespectSGraph k (CSGraph vk a ys zs z) (CSFun f) = ?doesSFunRespectSGraph_rhs_3
