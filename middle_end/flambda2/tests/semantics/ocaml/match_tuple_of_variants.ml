(* A match on a pair of two values of a variant of three constant constructors,
   with or-patterns and wildcards across the pair. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type colour =
  | Red
  | Green
  | Blue

let[@inline never] mix a b =
  match a, b with
  | Red, Red -> 1
  | Red, _ | _, Red -> 2
  | Green, Blue | Blue, Green -> 3
  | Green, Green -> 4
  | Blue, Blue -> 5

let result =
  mix (opaque Red) (opaque Red)
  + mix (opaque Green) (opaque Red)
  + mix (opaque Blue) (opaque Green)
  + mix (opaque Green) (opaque Green)
  + mix (opaque Blue) (opaque Blue)
