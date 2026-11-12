(* A record made by an exported function and read by another. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type t =
  { x : int;
    y : int
  }

let make x y = { x; y }

let sum t = t.x + t.y

let result = sum (make (opaque 1) 2)
