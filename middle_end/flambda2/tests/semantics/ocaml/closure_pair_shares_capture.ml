(* Two closures made together over the same value that is not known, kept in a
   pair and both called. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let make n =
  let add x = x + n in
  let scale x = x * n in
  add, scale

let result =
  let add, scale = make (opaque 10) in
  add 1 + scale 2 + add 3 + scale 4
