(* An exported function with a function of its own inside. *)

external ( + ) : int -> int -> int = "%addint"

let f x =
  let g y = y + x in
  g 1
