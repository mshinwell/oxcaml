(* A function, then a value chosen by a test when the module runs, then a
   function that uses both. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let double x = x + x

let offset = if opaque true then 1 else 2

let shifted x = double x + offset
