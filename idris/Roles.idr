module Roles


import Sparrow


%access public export

%default total

data Role : String -> Type where
  MkRole : (s : String) -> Role s
