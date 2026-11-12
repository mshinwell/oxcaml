(* A type with constant and non-constant constructors, matched by patterns that
   look inside the arguments. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type colour =
  | Red
  | Green
  | Blue

type shape =
  | Empty
  | Dot
  | Circle of int * colour
  | Rect of int * int * colour
  | Group of shape * shape

let score shape =
  match shape with
  | Empty -> 0
  | Dot -> 1
  | Circle (r, Red) -> r + 10
  | Circle (r, (Green | Blue)) -> r + 20
  | Rect (w, h, Blue) -> w + h + 30
  | Rect (w, _, _) -> w + 40
  | Group (Empty, s) | Group (s, Empty) -> ( match s with Dot -> 50 | _ -> 60)
  | Group (Circle (r, _), Circle (r', _)) -> r + r' + 70
  | Group (_, _) -> 80

let result =
  score (opaque (Circle (1, Green)))
  + score (opaque (Rect (2, 3, Blue)))
  + score (opaque (Group (Empty, Dot)))
  + score (opaque (Group (Circle (4, Red), Circle (5, Blue))))
  + score (opaque Dot)
