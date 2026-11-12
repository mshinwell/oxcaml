(* A value chosen by a test when the module runs, then a constant pair and a
   function that reads the pair and the value. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let base = if opaque true then 1 else 2

let pair = 10, 20

let total () = match pair with x, y -> x + y + base
