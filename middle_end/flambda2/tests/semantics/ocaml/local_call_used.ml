(* A local function called through its variable, in an exported function. *)

external ( + ) : int -> int -> int = "%addint"

let f x =
  let g y = y + x in
  g x

external opaque : 'a -> 'a = "%opaque"

let result = f (opaque 3)
