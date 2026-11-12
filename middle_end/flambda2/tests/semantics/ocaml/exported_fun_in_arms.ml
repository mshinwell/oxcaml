(* A function chosen by a test when the module runs: each arm of the test makes
   a function that needs nothing from around it. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let f = if opaque true then fun x -> x + 1 else fun x -> x + 2
