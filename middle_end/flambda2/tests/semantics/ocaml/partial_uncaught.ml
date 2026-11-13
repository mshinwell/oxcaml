(* A match that leaves a constructor out and is given it: the unit ends with
   Match_failure, which nothing catches. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type t =
  | A
  | B
  | C

let[@warning "-8"] [@inline never] f v = match v with A -> 1 | B -> 2

let first = f (opaque A)

let result = first + f (opaque C)
