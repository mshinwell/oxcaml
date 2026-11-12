(* A match on polymorphic variants: a constant one is an integer, the others are
   blocks whose first field is that integer. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] weight item =
  match item with `Feather -> 1 | `Stone n -> n | `Pair (a, b) -> a + b

let result =
  weight `Feather + weight (`Stone (opaque 10)) + weight (`Pair (2, 3))
