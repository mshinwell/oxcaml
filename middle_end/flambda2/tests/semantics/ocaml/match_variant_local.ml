(* [match_variant.ml] without the type annotation on [cells]. The compiler then
   allocates the two blocks on the stack, in a region that it opens around the
   expression: [Begin_region], [End_region] and a local allocation mode. The
   model has no regions: the test tool drops them and converts the two blocks as
   if they were on the heap (README.md, "Regions"). *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type shape =
  | Point
  | Square of int
  | Rect of int * int

let[@inline] cells shape =
  match shape with Point -> 1 | Square n -> n * n | Rect (w, h) -> w * h

let result =
  cells (Rect (opaque 3, 4)) + cells (Square (opaque 5)) + cells Point
