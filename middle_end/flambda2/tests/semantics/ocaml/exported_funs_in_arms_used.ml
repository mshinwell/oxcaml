(* A function chosen by a test when the module runs, and a function defined
   after the test that calls it. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let step = if opaque true then fun x -> x + 1 else fun x -> x + 2

let twice x = step (step x)
