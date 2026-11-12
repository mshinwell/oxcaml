(* A function defined after a value that is not known until the module runs,
   which it does not use. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let x = opaque 1

let f y = y + 1

let z = f x
