(* A match on a variant, in a function applied to constructors. Simplify inlines
   [cells] three times and resolves each match: the tests of [Is_int] and of the
   tag go, and the fields are read from the blocks that were just made, which
   then go too.

   The type annotation on [cells] makes its argument an ordinary, heap allocated
   one. Without it the compiler allocates the argument on the stack, in a
   region, which the model has not got (see [match_variant_local.ml]). *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type shape =
  | Point
  | Square of int
  | Rect of int * int

let[@inline] cells : shape -> int =
 fun shape ->
  match shape with Point -> 1 | Square n -> n * n | Rect (w, h) -> w * h

let result =
  cells (Rect (opaque 3, 4)) + cells (Square (opaque 5)) + cells Point
