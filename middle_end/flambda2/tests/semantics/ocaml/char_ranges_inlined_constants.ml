(* The match by ranges of char_ranges.ml, inlined at constants. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] class_of c =
  match c with 'a' .. 'z' -> 1 | 'A' .. 'Z' -> 2 | '0' .. '9' -> 3 | _ -> 0

let result = class_of 'q' + class_of 'Q' + class_of '7' + class_of '!'
