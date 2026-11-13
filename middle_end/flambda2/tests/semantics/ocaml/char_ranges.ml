(* A match on a character by ranges. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let class_of c =
  match c with
  | 'a' .. 'z' -> 1
  | 'A' .. 'Z' -> 2
  | '0' .. '9' -> 3
  | ' ' | '\t' | '\n' -> 4
  | _ -> 0

let result =
  class_of 'q'
  + class_of (opaque 'Q')
  + class_of (opaque '7')
  + class_of (opaque ' ')
  + class_of (opaque '!')
