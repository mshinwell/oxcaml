(* A variant made on the two arms of a test, by two constructors that carry the
   same argument, and matched at once by one arm for both. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type side =
  | Left of int
  | Right of int
  | Neither

let[@inline never] f c x =
  match if c then Left x else Right x with
  | Left v | Right v -> v + 1
  | Neither -> 0

let result = f (opaque true) (opaque 5) + f (opaque false) (opaque 4)
