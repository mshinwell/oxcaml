(* A function that is exported and also called by the unit. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let double x = x + x

let result = double (opaque 21)
