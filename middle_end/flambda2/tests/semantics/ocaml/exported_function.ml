(* A unit with no interface file: its function is a field of the module block.
   Simplify makes the closure a symbol. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let succ x = x + 1

let result = succ (opaque 3)
