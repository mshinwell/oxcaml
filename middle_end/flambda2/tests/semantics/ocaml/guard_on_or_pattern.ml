(* A guard on an or-pattern that binds: where it fails each side has its own
   later case. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

type t =
  | L of int
  | R of int
  | N

let[@inline never] f v =
  match v with
  | (L x | R x) when x = 0 -> 1
  | L x -> x + 10
  | R x -> x + 20
  | N -> 0

let result =
  f (L (opaque 0))
  + (f (R (opaque 0)) * 10)
  + (f (L (opaque 5)) * 100)
  + (f (R (opaque 5)) * 10000)
  + f N
