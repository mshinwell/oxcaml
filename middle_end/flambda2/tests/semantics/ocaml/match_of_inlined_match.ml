(* The match of match_of_match.ml, with the inner match in an inlined function
   that returns a constructor. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

type colour =
  | Red
  | Green
  | Blue

type weight =
  | Light
  | Heavy of int

let[@inline] weigh c =
  match c with Red -> Light | Green -> Heavy 2 | Blue -> Heavy 3

let[@inline never] body c x = match weigh c with Light -> x | Heavy n -> x * n

let result = body Red 5 + body (opaque Green) 5 + body Blue (opaque 5)
