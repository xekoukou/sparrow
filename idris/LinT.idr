module LinT


import public LinDepT 

%access public export

%default total

||| The input and output of a linear function.
|||
data LinT : LinDepT a -> Type where
  INil : LinT TNil
  IAtom      : {dt : Vect n Type} -> {df : genT dt} -> {hv : HVect dt} -> applyH hv df -> LinT $ TAtom hv {dt=dt} {df=df}
  IAnd       : LinT a -> LinT b         -> LinT $ TAnd a b
  ||| Here the agent decides between the two values of Uor.
  IUor       : Either (LinT a) (LinT b) -> LinT $ TUor a b
  ||| If the protocol specification computes to send the left value
  ||| the agent sends the left value.
  IDorLeft   : LinT a                      -> LinT $ TDor $ Left a
  ||| If the protocol specification computes to send the right value
  ||| the agent sends the right value.
  IDorRight  : LinT b                      -> LinT $ TDor $ Right b



