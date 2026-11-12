(* A pair chosen by a test when the module runs: a number and a function made in
   the arm. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let p = if opaque true then 1, fun x -> x + 1 else 2, fun x -> x + 2
