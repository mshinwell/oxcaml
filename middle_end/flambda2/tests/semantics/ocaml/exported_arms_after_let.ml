(* A function that makes a function in each arm of a test, and the same test
   made when the module runs on a value computed before it. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let choose c = if c then fun x -> x + 1 else fun x -> x + 2

let b = opaque true

let g = if b then fun x -> x + 1 else fun x -> x + 2
