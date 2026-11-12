(* A variant built on the two arms of a test with two constructors that carry
   the same argument, and then a match with one arm for both. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type side =
  | Left of int
  | Right of int
  | Neither

let[@inline] place c x = if c then Left x else Right x

let[@inline never] carried c x =
  match place c x with Left v | Right v -> v + 1 | Neither -> 0

let result =
  carried (opaque true) (opaque 5) + carried (opaque false) (opaque 4)
