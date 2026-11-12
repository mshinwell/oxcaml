(* A function of one argument that returns a function, applied to two arguments
   at once. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] adder a = fun[@inline] b -> a + b

let result = adder (opaque 1) 2
