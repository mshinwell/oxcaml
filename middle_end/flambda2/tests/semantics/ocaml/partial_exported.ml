(* A partial application of an exported function, exported. *)

external ( + ) : int -> int -> int = "%addint"

let add a b = a + b

let incr = add 1
