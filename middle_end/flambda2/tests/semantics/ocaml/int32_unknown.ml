(* Arithmetic on a 32-bit integer that Simplify does not know: one unboxing, one
   boxing. *)

external add : int32 -> int32 -> int32 = "%int32_add"

external mul : int32 -> int32 -> int32 = "%int32_mul"

external opaque : 'a -> 'a = "%opaque"

let result =
  let x = opaque 7l in
  add (mul x x) x
