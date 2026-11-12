(* Two tests when the module runs, one after the other: the first chooses a
   number, the second a function. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let a = if opaque true then 1 else 2

let g = if opaque true then fun x -> x + 1 else fun x -> x + 2
