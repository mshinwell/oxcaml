(* A local function called through its variable, in an exported function. *)

external ( + ) : int -> int -> int = "%addint"

let f x =
  let g y = y + x in
  g x
