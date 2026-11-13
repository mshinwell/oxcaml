(* One arm for two runs of integers that another run separates. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] edge n =
  match n with 0 | 1 | 2 | 7 | 8 | 9 -> 1 | 3 | 4 | 5 | 6 -> 2 | _ -> 0

let result =
  edge (opaque 1)
  + (edge (opaque 8) * 10)
  + (edge (opaque 5) * 100)
  + (edge (opaque 10) * 1000)
  + (edge (opaque 2) * 10000)
