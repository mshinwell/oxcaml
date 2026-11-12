(* A value chosen by two tests, one inside the other, when the module runs, and
   then a function that uses it. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let level = if opaque true then if opaque false then 1 else 2 else 3

let raise_by x = x + level
