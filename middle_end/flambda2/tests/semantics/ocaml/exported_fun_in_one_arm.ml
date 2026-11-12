(* A test when the module runs, between a function defined before it and a
   function made in the other arm. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let succ x = x + 1

let f = if opaque true then succ else fun x -> x + 2
