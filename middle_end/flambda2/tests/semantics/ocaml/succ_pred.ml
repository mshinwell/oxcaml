(* The successor and the predecessor of a number that Simplify does not know. *)

external ( + ) : int -> int -> int = "%addint"

external succ : int -> int = "%succint"

external pred : int -> int = "%predint"

external opaque : 'a -> 'a = "%opaque"

let result =
  let x = opaque 5 in
  succ x + pred x
