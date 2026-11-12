(* [{ point with y }] copies the other fields. Simplify inlines [with_y] and
   reads the fields of the copy from the original. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type point =
  { x : int;
    y : int;
    z : int
  }

let[@inline] with_y point y = { point with y }

let result =
  let point = with_y { x = opaque 1; y = 2; z = 3 } 20 in
  point.x + point.y + point.z
