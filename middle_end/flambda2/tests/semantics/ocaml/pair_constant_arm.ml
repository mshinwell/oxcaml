(* A pair built in the two arms of a test and matched at once: one arm builds it
   of a variable and the other is a constant pair. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] pick c x =
  match if c then x, true else 0, false with v, true -> v | _, false -> -7

let result = pick (opaque true) 3 + pick (opaque false) 3
