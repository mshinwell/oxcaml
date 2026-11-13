(* Three arms that compute the same sum. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let pick n x = match n with 0 -> x + 1 | 1 -> x + 1 | _ -> x + 1

let result = pick (opaque 1) 2
