(* An exported function that returns a closure over its two arguments. *)

external ( + ) : int -> int -> int = "%addint"

let add3 a b = fun c -> a + b + c
