(* Shifts of a 64-bit integer that Simplify does not know. *)

external add : int64 -> int64 -> int64 = "%int64_add"

external shift_left : int64 -> int -> int64 = "%int64_lsl"

external shift_right : int64 -> int -> int64 = "%int64_asr"

external opaque : 'a -> 'a = "%opaque"

let result =
  let x = opaque 9L in
  add (shift_left x 3) (shift_right x 1)
