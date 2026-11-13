(* An or-pattern that binds two variables, in the other order on its second
   side. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type edge =
  | Up of int * int
  | Down of int * int
  | Flat of int

let[@inline never] slope e =
  match e with Up (a, b) | Down (b, a) -> b - a | Flat _ -> 0

let result =
  slope (Up (2, opaque 9)) + (slope (Down (2, opaque 9)) * 10) + slope (Flat 3)
