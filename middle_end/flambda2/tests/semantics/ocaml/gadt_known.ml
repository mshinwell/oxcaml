(* A match on a GADT whose constructor is known once the function is inlined:
   the argument is used at the type that the constructor gives it. *)

type _ kind =
  | Number : int kind
  | Flag : bool kind

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] weight (type a) (kind : a kind) (x : a) : int =
  match kind with Number -> x + 1 | Flag -> if x then 10 else 20

let result = weight Number (opaque 4) + weight Flag true
