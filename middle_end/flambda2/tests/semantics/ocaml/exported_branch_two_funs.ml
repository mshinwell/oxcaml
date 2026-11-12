(* A value chosen by a test when the module runs, and then two functions: the
   first uses the value and the second calls the first. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let step = if opaque true then 1 else 10

let next x = x + step

let after_next x = next x + 1
