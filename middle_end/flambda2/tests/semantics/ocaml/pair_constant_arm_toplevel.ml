(* A pair built in the two arms of a test and matched at once, at the top of the
   unit: one arm builds it of an unknown value and the other is a constant
   pair. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let result =
  match if opaque true then opaque 3, true else 0, false with
  | v, true -> v
  | _, false -> -7
