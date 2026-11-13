(* The length of a string that is not known, read twice in a function. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

external ( * ) : int -> int -> int = "%mulint"

let area s = length s * length s

let result = area (opaque "abcd")
