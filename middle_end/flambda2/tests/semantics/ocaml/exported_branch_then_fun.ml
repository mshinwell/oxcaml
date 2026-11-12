(* A value chosen by a test when the module runs, and then a function that uses
   it. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let base = if opaque true then 1 else 2

let add x = x + base
