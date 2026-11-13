(* A boxed 64-bit integer that one join is given and passes on to another, which
   unboxes it. *)

external opaque : 'a -> 'a = "%opaque"

external add64 : int64 -> int64 -> int64 = "%int64_add"

let[@inline never] f a b x =
  let t = if b then add64 x 1L else add64 x 2L in
  let y = if a then t else 3L in
  add64 y y

let result = f (opaque true) (opaque false) (opaque 5L)
