(* A boxed 64-bit integer that is replaced by zero where it is negative, used
   after the two arms of the test meet: one arm gives the box that the test has
   unboxed, the other a constant. *)

external add : int64 -> int64 -> int64 = "%int64_add"

external to_int : int64 -> int = "%int64_to_int"

external less : int64 -> int64 -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] above : int64 -> int64 =
 fun a ->
  let v = if less a 0L then 0L else a in
  add v 1L

let result = to_int (add (above (opaque 5L)) (above (opaque (-5L))))
