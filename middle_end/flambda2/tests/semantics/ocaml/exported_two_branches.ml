(* Two values, each chosen by a test when the module runs, with a function after
   each. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let a = if opaque true then 1 else 2

let add_a x = x + a

let b = if opaque false then 3 else 4

let add_b x = add_a x + b
