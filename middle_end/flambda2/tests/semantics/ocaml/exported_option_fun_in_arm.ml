(* An option chosen by a test when the module runs, whose contents is a function
   made in the arm. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let f = if opaque true then Some (fun x -> x + 1) else None
