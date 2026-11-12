(* A test when the module runs, then a function that does not use what it
   chose. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let flag = if opaque true then 1 else 2

let succ x = x + 1

let succ2 x = succ (succ x)
