(* A closure put in a pair and read back from it, then called. *)

external ( + ) : int -> int -> int = "%addint"

external fst : 'a * 'b -> 'a = "%field0_immut"

let f x =
  let g y = y + x in
  let p = g, x in
  (fst p) x

external opaque : 'a -> 'a = "%opaque"

let result = f (opaque 3)
