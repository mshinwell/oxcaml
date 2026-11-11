(* Records built and projected. [add] is inlined; its result is a record whose
   fields are read at once, so no record is left. (For the type annotation, see
   [match_variant.ml].) *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type point =
  { x : int;
    y : int
  }

let[@inline] add : point -> point -> point =
 fun p q -> { x = p.x + q.x; y = p.y + q.y }

let result =
  let r = add { x = opaque 1; y = 2 } { x = 3; y = opaque 4 } in
  let s = add r r in
  s.x * s.y
