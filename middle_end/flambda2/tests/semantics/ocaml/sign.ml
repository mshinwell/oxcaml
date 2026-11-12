(* [compare] on integers, which gives -1, 0 or 1. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external compare : int -> int -> int = "%compare"

let[@inline] sign x = compare x 0

let result = sign (-7) + (10 * sign 7) + (100 * sign 0)
