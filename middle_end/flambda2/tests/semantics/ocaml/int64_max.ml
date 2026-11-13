(* The greater of two boxed 64-bit integers, used after the two arms of the
   comparison meet: each arm gives a box that the comparison has unboxed. *)

external add : int64 -> int64 -> int64 = "%int64_add"

external to_int : int64 -> int = "%int64_to_int"

external less : int64 -> int64 -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] next_max : int64 -> int64 -> int64 =
 fun a b ->
  let m = if less a b then b else a in
  add m 1L

let result = to_int (add (next_max (opaque 3L) 4L) (next_max (opaque 6L) 5L))
