(* A boxed 64-bit integer that is computed on one path and given on the other,
   and used after they meet. *)

external add : int64 -> int64 -> int64 = "%int64_add"

external to_int : int64 -> int = "%int64_to_int"

let[@inline never] f : bool -> int64 -> int64 -> int64 =
 fun c a b ->
  let x = if c then add a b else b in
  add x 1L

let result = to_int (f true 3L 4L)
