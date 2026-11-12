(* A pair chosen by a test when the module runs, and then a function that reads
   it. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let p = if opaque true then 1, 2 else 3, 4

let sum () = match p with x, y -> x + y
