(* Constructors with inline records. Simplify inlines [area] twice and resolves
   both matches; neither block is built. *)

external ( * ) : int -> int -> int = "%mulint"

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type shape =
  | Circle of { radius : int }
  | Rect of
      { width : int;
        height : int
      }

let[@inline] area shape =
  match shape with
  | Circle { radius } -> 3 * radius * radius
  | Rect { width; height } -> width * height

let result =
  area (Circle { radius = opaque 2 })
  + area (Rect { width = 3; height = opaque 4 })
