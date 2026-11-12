(* A pair that is not known until the module runs, taken apart, and then a
   function that uses both parts. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let a, b = opaque (1, 2)

let add x = x + a + b
