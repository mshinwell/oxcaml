(* A match whose scrutinee is the result of another match. *)

external ( + ) : int -> int -> int = "%addint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

type colour =
  | Red
  | Green
  | Blue

let[@inline never] body c x =
  match match c with Red -> 1 | Green -> 2 | Blue -> 3 with
  | 1 -> x + 10
  | 2 -> x + 20
  | _ -> x + 30

let result = body Red 1 + body (opaque Green) 2 + body Blue (opaque 3)
