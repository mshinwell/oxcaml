(* The greatest and the least integer as literals of a match. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] kind n =
  match n with
  | 4611686018427387903 -> 1
  | -4611686018427387904 -> 2
  | 4611686018427387902 -> 3
  | 0 -> 4
  | _ -> 5

let result =
  kind (opaque 4611686018427387903)
  + (10 * kind (opaque (-4611686018427387904)))
  + (100 * kind (opaque 4611686018427387902))
  + (1000 * kind (opaque 0))
  + (10000 * kind (opaque 1))
