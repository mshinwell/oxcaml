(* [inlined_at_one_call.ml] with an import: the unit exports a predefined
   exception too. One function is called twice: the first call is marked to be
   inlined and the second never to be. The unit is validated once unused static
   bindings are removed from the head of the term after too, and no import is
   bound at that head. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let square_plus_one x = (x * x) + 1

let result =
  (square_plus_one [@inlined]) (opaque 3)
  + (square_plus_one [@inlined never]) (opaque 4)

let not_found = Not_found
