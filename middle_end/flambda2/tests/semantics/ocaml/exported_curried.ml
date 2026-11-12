(* An exported function of two arguments, called with both. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let add x y = x + y

let result = add (opaque 1) 2
